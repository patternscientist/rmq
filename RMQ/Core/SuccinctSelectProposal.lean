import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctRankProposal
import RMQ.Core.GenericSelect.SelectSource

/-!
# Select-side sampled-directory proposal

This scratch module isolates the minimal select-side theorem surface needed to
advance the payload-live succinct RMQ path without changing the main
`SuccinctSpace` API yet.

The hard construction still has to build the locator tables.  The definitions
below say precisely what that construction should return: payload-live select
data whose auxiliary locator payload is bounded by the canonical sampled
directory envelope, while queries still use a counted path through
block-indexed payload tables:

1. read one coarse locator word,
2. read one local locator word,
3. read one payload word,
4. run the word-select primitive.

That is the useful next boundary for a concrete two-level select codec.
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

/-- Bit budget occupied by the true/false fixed-width select locator tables. -/
def selectLocatorPayloadBudget
    (trueEntries falseEntries : List (Option SuccinctSpace.StoredWordSelectSample))
    (fieldWidth : Nat) : Nat :=
  trueEntries.length * SuccinctSpace.selectSampleWordWidth fieldWidth +
    falseEntries.length * SuccinctSpace.selectSampleWordWidth fieldWidth

theorem fixedWidthSelectSampleTables_payload_length_eq_budget
    {trueEntries falseEntries :
      List (Option SuccinctSpace.StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      SuccinctSpace.FixedWidthSelectSampleTables
        trueEntries falseEntries fieldWidth) :
    tables.payload.length =
      selectLocatorPayloadBudget trueEntries falseEntries fieldWidth := by
  simp [selectLocatorPayloadBudget,
    SuccinctSpace.FixedWidthSelectSampleTables.payload_length]

theorem fixedWidthSelectSampleTables_payload_length_le_sampled
    {trueEntries falseEntries :
      List (Option SuccinctSpace.StoredWordSelectSample)}
    {fieldWidth slots n : Nat}
    (tables :
      SuccinctSpace.FixedWidthSelectSampleTables
        trueEntries falseEntries fieldWidth)
    (hbudget :
      selectLocatorPayloadBudget trueEntries falseEntries fieldWidth <=
        SuccinctSpace.sampledDirectoryOverhead slots n) :
    tables.payload.length <=
      SuccinctSpace.sampledDirectoryOverhead slots n := by
  rw [fixedWidthSelectSampleTables_payload_length_eq_budget tables]
  exact hbudget

theorem canonicalSelectBlockTablesFinite_payload_length_eq
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) :
    (canonicalSelectBlockTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).payload.length =
      (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth +
        (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth := by
  simp [canonicalSelectBlockTablesFinite, canonicalSelectBlockTables,
    selectBlockDeltaEntries, canonicalSelectBlockCount,
    SuccinctSpace.FixedWidthSelectSampleTables.payload_length]

theorem canonicalSelectBlockTablesFinite_payload_length_ge_succ
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) :
    bits.length + 1 <=
      (canonicalSelectBlockTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).payload.length := by
  rw [canonicalSelectBlockTablesFinite_payload_length_eq hbits]
  have hword :
      1 <= SuccinctSpace.selectSampleWordWidth fieldWidth := by
    unfold SuccinctSpace.selectSampleWordWidth
    omega
  have hfirst :
      bits.length + 1 <=
        (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth := by
    simpa using Nat.mul_le_mul_left (bits.length + 1) hword
  exact Nat.le_trans hfirst (Nat.le_add_right _ _)

theorem not_littleOLinear_of_succ_le
    {overhead : Nat -> Nat}
    (hle : forall n : Nat, n + 1 <= overhead n) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  intro hoverhead
  rcases hoverhead 2 (by omega) with ⟨threshold, hthreshold⟩
  have hscaled : 2 * overhead threshold <= threshold :=
    hthreshold threshold (Nat.le_refl threshold)
  have hsucc : threshold + 1 <= overhead threshold := hle threshold
  have hcontr : 2 * (threshold + 1) <= threshold := by
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hsucc) hscaled
  omega

theorem not_littleOLinear_of_self_le
    {overhead : Nat -> Nat}
    (hle : forall n : Nat, n <= overhead n) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  intro hoverhead
  rcases hoverhead 2 (by omega) with ⟨threshold, hthreshold⟩
  let n := threshold + 1
  have hscaled : 2 * overhead n <= n :=
    hthreshold n (by omega)
  have hself : n <= overhead n := hle n
  have hcontr : 2 * n <= n := by
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hself) hscaled
  omega

def clarkSelectTwoWordDescriptorIndexIdentityOverhead (n : Nat) : Nat :=
  let bits : List Bool := List.replicate n false
  let fieldWidth := SuccinctRankProposal.machineWordBits bits.length
  (clarkSelectTwoWordDescriptorIndexTable
    false bits 1 1 fieldWidth (bits.length + 1)
    (by omega)
    (by omega)
    (by
      simpa [fieldWidth, SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := bits.length)))).table.payload.length

theorem clarkSelectTwoWordDescriptorIndexIdentityOverhead_ge_succ
    (n : Nat) :
    n + 1 <= clarkSelectTwoWordDescriptorIndexIdentityOverhead n := by
  let bits : List Bool := List.replicate n false
  let fieldWidth := SuccinctRankProposal.machineWordBits bits.length
  have hbits : bits.length < 2 ^ fieldWidth := by
    simpa [fieldWidth, SuccinctRankProposal.machineWordBits] using
      (Nat.lt_log2_self (n := bits.length))
  have hpayload :
      clarkSelectTwoWordDescriptorIndexIdentityOverhead n =
        (bits.length + 1) * fieldWidth := by
    simp [clarkSelectTwoWordDescriptorIndexIdentityOverhead, bits,
      fieldWidth, clarkSelectTwoWordDescriptorIndexTable,
      clarkSelectTwoWordDescriptorIndexEntries,
      SuccinctSpace.FixedWidthNatTable.payload_length]
  have hfield : 1 <= fieldWidth := by
    exact SuccinctRankProposal.machineWordBits_pos bits.length
  have hmul : bits.length + 1 <= (bits.length + 1) * fieldWidth := by
    simpa using Nat.mul_le_mul_left (bits.length + 1) hfield
  have hlen : bits.length = n := by
    simp [bits]
  rw [hpayload]
  simpa [hlen] using hmul

theorem clarkSelectTwoWordDescriptorIndexIdentityOverhead_not_littleO :
    ¬ SuccinctSpace.LittleOLinear
        clarkSelectTwoWordDescriptorIndexIdentityOverhead := by
  exact not_littleOLinear_of_succ_le
    clarkSelectTwoWordDescriptorIndexIdentityOverhead_ge_succ

theorem canonicalSelectBlockTablesFinite_identity_payload_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall bits : List Bool,
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (by
              simpa [SuccinctRankProposal.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length <=
          overhead bits.length) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_succ_le
  intro n
  let bits : List Bool := List.replicate n false
  have hpayload :
      bits.length + 1 <=
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (by
              simpa [SuccinctRankProposal.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length :=
    canonicalSelectBlockTablesFinite_payload_length_ge_succ
      (bits := bits)
      (wordSize := SuccinctRankProposal.machineWordBits bits.length)
      (occurrencesPerSuper :=
        SuccinctRankProposal.machineWordBits bits.length)
      (fieldWidth := SuccinctRankProposal.machineWordBits bits.length)
      (by
        simpa [SuccinctRankProposal.machineWordBits] using
          (Nat.lt_log2_self (n := bits.length)))
  have hboundBits := hbound bits
  have hlen : bits.length = n := by
    simp [bits]
  have hcombined := Nat.le_trans hpayload hboundBits
  simpa [hlen] using hcombined

theorem noTwoLevelPayloadLiveStoredWordRankSelectFamily_with_canonical_select_block
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    ¬ (forall bits : List Bool,
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (SuccinctRankProposal.machineWordBits bits.length)
            (by
              simpa [SuccinctRankProposal.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length <=
          selectBlock bits.length) := by
  intro hbound
  exact
    canonicalSelectBlockTablesFinite_identity_payload_not_littleO
      hbound family.selectBlock_littleO

/--
Four-field sparse/dense false-select locator entry.

The same fixed-width codec is used for super entries and local entries.  The
entry records the sampled occurrence, sampled BP position, a small span-class
tag, and a payload pointer into the appropriate explicit table.
-/
structure SparseDenseFalseSelectLocatorEntry where
  baseOccurrence : Nat
  basePosition : Nat
  spanClass : Nat
  pointer : Nat

def sparseDenseFalseSelectLocatorEntryWordWidth
    (fieldWidth : Nat) : Nat :=
  4 * fieldWidth

theorem sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded
    (n : Nat) :
    ¬ sparseDenseFalseSelectLocatorEntryWordWidth
        (SuccinctRankProposal.machineWordBits n) <=
      SuccinctRankProposal.machineWordBits n := by
  intro hbounded
  have hpos : 0 < SuccinctRankProposal.machineWordBits n :=
    SuccinctRankProposal.machineWordBits_pos n
  unfold sparseDenseFalseSelectLocatorEntryWordWidth at hbounded
  omega

def sparseDenseFalseSelectLocatorEntryToBitsLE
    (fieldWidth : Nat)
    (entry : SparseDenseFalseSelectLocatorEntry) :
    List Bool :=
  SuccinctSpace.natToBitsLE fieldWidth entry.baseOccurrence ++
    SuccinctSpace.natToBitsLE fieldWidth entry.basePosition ++
      SuccinctSpace.natToBitsLE fieldWidth entry.spanClass ++
        SuccinctSpace.natToBitsLE fieldWidth entry.pointer

theorem sparseDenseFalseSelectLocatorEntryToBitsLE_length
    (fieldWidth : Nat)
    (entry : SparseDenseFalseSelectLocatorEntry) :
    (sparseDenseFalseSelectLocatorEntryToBitsLE fieldWidth entry).length =
      sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth := by
  simp [sparseDenseFalseSelectLocatorEntryToBitsLE,
    sparseDenseFalseSelectLocatorEntryWordWidth,
    SuccinctSpace.natToBitsLE_length]
  omega

def bitsToSparseDenseFalseSelectLocatorEntry
    (fieldWidth : Nat) (bits : List Bool) :
    SparseDenseFalseSelectLocatorEntry where
  baseOccurrence :=
    SuccinctSpace.bitsToNatLE (bits.take fieldWidth)
  basePosition :=
    SuccinctSpace.bitsToNatLE ((bits.drop fieldWidth).take fieldWidth)
  spanClass :=
    SuccinctSpace.bitsToNatLE ((bits.drop (2 * fieldWidth)).take fieldWidth)
  pointer :=
    SuccinctSpace.bitsToNatLE ((bits.drop (3 * fieldWidth)).take fieldWidth)

theorem bitsToNatLE_lt_two_pow_length (bits : List Bool) :
    SuccinctSpace.bitsToNatLE bits < 2 ^ bits.length := by
  induction bits with
  | nil =>
      simp [SuccinctSpace.bitsToNatLE]
  | cons bit rest ih =>
      cases bit <;>
        simp [SuccinctSpace.bitsToNatLE, SuccinctSpace.bitToNat,
          Nat.pow_succ] at ih ⊢ <;>
        omega

theorem bitsToNatLE_take_lt_two_pow (bits : List Bool) (width : Nat) :
    SuccinctSpace.bitsToNatLE (bits.take width) < 2 ^ width := by
  have hlt := bitsToNatLE_lt_two_pow_length (bits.take width)
  have hlen : (bits.take width).length <= width := by
    simpa [List.length_take] using Nat.min_le_left width bits.length
  exact Nat.lt_of_lt_of_le hlt
    (Nat.pow_le_pow_right (by omega : 0 < 2) hlen)

theorem fixedWidthNatTable_entry_lt_two_pow
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    {i entry : Nat}
    (hget : entries[i]? = some entry) :
    entry < 2 ^ width := by
  have hread := table.read_exact i
  rw [hget] at hread
  cases hword : table.store.words[i]? with
  | none =>
      simp [hword] at hread
  | some word =>
      have hentry : SuccinctSpace.bitsToNatLE word = entry := by
        simpa [hword] using hread
      have hlen : word.length = width :=
        table.read_word_length_of_some hword
      rw [<- hentry, <- hlen]
      exact bitsToNatLE_lt_two_pow_length word

theorem bitsToSparseDenseFalseSelectLocatorEntry_fields_lt
    (fieldWidth : Nat) (bits : List Bool) :
    let entry := bitsToSparseDenseFalseSelectLocatorEntry fieldWidth bits
    entry.baseOccurrence < 2 ^ fieldWidth /\
      entry.basePosition < 2 ^ fieldWidth /\
        entry.spanClass < 2 ^ fieldWidth /\
          entry.pointer < 2 ^ fieldWidth := by
  simp [bitsToSparseDenseFalseSelectLocatorEntry,
    bitsToNatLE_take_lt_two_pow]

theorem bitsToSparseDenseFalseSelectLocatorEntry_toBits_of_bound
    {fieldWidth : Nat}
    {entry : SparseDenseFalseSelectLocatorEntry}
    (hbound :
      entry.baseOccurrence < 2 ^ fieldWidth /\
        entry.basePosition < 2 ^ fieldWidth /\
          entry.spanClass < 2 ^ fieldWidth /\
            entry.pointer < 2 ^ fieldWidth) :
    bitsToSparseDenseFalseSelectLocatorEntry fieldWidth
        (sparseDenseFalseSelectLocatorEntryToBitsLE fieldWidth entry) =
      entry := by
  rcases entry with
    ⟨baseOccurrence, basePosition, spanClass, pointer⟩
  rcases hbound with ⟨hbaseOccurrence, hbasePosition, hspanClass, hpointer⟩
  let baseOccurrenceBits :=
    SuccinctSpace.natToBitsLE fieldWidth baseOccurrence
  let basePositionBits :=
    SuccinctSpace.natToBitsLE fieldWidth basePosition
  let spanClassBits :=
    SuccinctSpace.natToBitsLE fieldWidth spanClass
  let pointerBits :=
    SuccinctSpace.natToBitsLE fieldWidth pointer
  have hbaseOccurrenceLen :
      baseOccurrenceBits.length = fieldWidth := by
    simp [baseOccurrenceBits, SuccinctSpace.natToBitsLE_length]
  have hbasePositionLen :
      basePositionBits.length = fieldWidth := by
    simp [basePositionBits, SuccinctSpace.natToBitsLE_length]
  have hspanClassLen :
      spanClassBits.length = fieldWidth := by
    simp [spanClassBits, SuccinctSpace.natToBitsLE_length]
  have hpointerLen :
      pointerBits.length = fieldWidth := by
    simp [pointerBits, SuccinctSpace.natToBitsLE_length]
  have htakeBaseOccurrence :
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).take fieldWidth =
        baseOccurrenceBits := by
    calc
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).take fieldWidth =
        (baseOccurrenceBits ++
            (basePositionBits ++ spanClassBits ++ pointerBits)).take
          baseOccurrenceBits.length := by
          rw [hbaseOccurrenceLen]
          simp [List.append_assoc]
      _ = baseOccurrenceBits := by
          rw [List.take_append_of_le_length (Nat.le_refl _)]
          rw [List.take_of_length_le (Nat.le_refl _)]
  have hdropBaseOccurrence :
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop fieldWidth =
        basePositionBits ++ spanClassBits ++ pointerBits := by
    calc
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop fieldWidth =
        (baseOccurrenceBits ++
            (basePositionBits ++ spanClassBits ++ pointerBits)).drop
          baseOccurrenceBits.length := by
          rw [hbaseOccurrenceLen]
          simp [List.append_assoc]
      _ = basePositionBits ++ spanClassBits ++ pointerBits := by
          rw [List.drop_append_of_le_length (Nat.le_refl _)]
          rw [List.drop_of_length_le (Nat.le_refl _)]
          simp
  have htakeBasePosition :
      ((baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop fieldWidth).take fieldWidth =
        basePositionBits := by
    rw [hdropBaseOccurrence]
    calc
      (basePositionBits ++ spanClassBits ++ pointerBits).take fieldWidth =
        (basePositionBits ++ (spanClassBits ++ pointerBits)).take
          basePositionBits.length := by
          rw [hbasePositionLen]
          simp [List.append_assoc]
      _ = basePositionBits := by
          rw [List.take_append_of_le_length (Nat.le_refl _)]
          rw [List.take_of_length_le (Nat.le_refl _)]
  have hdropTwo :
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (2 * fieldWidth) =
        spanClassBits ++ pointerBits := by
    calc
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (2 * fieldWidth) =
        ((baseOccurrenceBits ++ basePositionBits) ++
            (spanClassBits ++ pointerBits)).drop
          (baseOccurrenceBits ++ basePositionBits).length := by
          have hlen :
              (baseOccurrenceBits ++ basePositionBits).length =
                2 * fieldWidth := by
            simp [hbaseOccurrenceLen, hbasePositionLen]
            omega
          rw [hlen]
          simp [List.append_assoc]
      _ = spanClassBits ++ pointerBits := by
          rw [List.drop_append_of_le_length (Nat.le_refl _)]
          rw [List.drop_of_length_le (Nat.le_refl _)]
          simp
  have htakeSpanClass :
      ((baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (2 * fieldWidth)).take fieldWidth =
        spanClassBits := by
    rw [hdropTwo]
    calc
      (spanClassBits ++ pointerBits).take fieldWidth =
        (spanClassBits ++ pointerBits).take spanClassBits.length := by
          rw [hspanClassLen]
      _ = spanClassBits := by
          rw [List.take_append_of_le_length (Nat.le_refl _)]
          rw [List.take_of_length_le (Nat.le_refl _)]
  have hdropThree :
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (3 * fieldWidth) =
        pointerBits := by
    calc
      (baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (3 * fieldWidth) =
        ((baseOccurrenceBits ++ basePositionBits ++ spanClassBits) ++
            pointerBits).drop
          (baseOccurrenceBits ++ basePositionBits ++ spanClassBits).length := by
          have hlen :
              (baseOccurrenceBits ++ basePositionBits ++
                  spanClassBits).length =
                3 * fieldWidth := by
            simp [hbaseOccurrenceLen, hbasePositionLen, hspanClassLen]
            omega
          rw [hlen]
      _ = pointerBits := by
          rw [List.drop_append_of_le_length (Nat.le_refl _)]
          rw [List.drop_of_length_le (Nat.le_refl _)]
          simp
  have htakePointer :
      ((baseOccurrenceBits ++ basePositionBits ++ spanClassBits ++
          pointerBits).drop (3 * fieldWidth)).take fieldWidth =
        pointerBits := by
    rw [hdropThree]
    rw [List.take_of_length_le]
    rw [hpointerLen]
    exact Nat.le_refl fieldWidth
  have htakeBaseOccurrenceRaw :
      (SuccinctSpace.natToBitsLE fieldWidth baseOccurrence ++
          SuccinctSpace.natToBitsLE fieldWidth basePosition ++
            SuccinctSpace.natToBitsLE fieldWidth spanClass ++
              SuccinctSpace.natToBitsLE fieldWidth pointer).take fieldWidth =
        SuccinctSpace.natToBitsLE fieldWidth baseOccurrence := by
    simpa [baseOccurrenceBits, basePositionBits, spanClassBits, pointerBits]
      using htakeBaseOccurrence
  have htakeBasePositionRaw :
      ((SuccinctSpace.natToBitsLE fieldWidth baseOccurrence ++
          SuccinctSpace.natToBitsLE fieldWidth basePosition ++
            SuccinctSpace.natToBitsLE fieldWidth spanClass ++
              SuccinctSpace.natToBitsLE fieldWidth pointer).drop
          fieldWidth).take fieldWidth =
        SuccinctSpace.natToBitsLE fieldWidth basePosition := by
    simpa [baseOccurrenceBits, basePositionBits, spanClassBits, pointerBits]
      using htakeBasePosition
  have htakeSpanClassRaw :
      ((SuccinctSpace.natToBitsLE fieldWidth baseOccurrence ++
          SuccinctSpace.natToBitsLE fieldWidth basePosition ++
            SuccinctSpace.natToBitsLE fieldWidth spanClass ++
              SuccinctSpace.natToBitsLE fieldWidth pointer).drop
          (2 * fieldWidth)).take fieldWidth =
        SuccinctSpace.natToBitsLE fieldWidth spanClass := by
    simpa [baseOccurrenceBits, basePositionBits, spanClassBits, pointerBits]
      using htakeSpanClass
  have htakePointerRaw :
      ((SuccinctSpace.natToBitsLE fieldWidth baseOccurrence ++
          SuccinctSpace.natToBitsLE fieldWidth basePosition ++
            SuccinctSpace.natToBitsLE fieldWidth spanClass ++
              SuccinctSpace.natToBitsLE fieldWidth pointer).drop
          (3 * fieldWidth)).take fieldWidth =
        SuccinctSpace.natToBitsLE fieldWidth pointer := by
    simpa [baseOccurrenceBits, basePositionBits, spanClassBits, pointerBits]
      using htakePointer
  simp [List.append_assoc] at htakeBaseOccurrenceRaw htakeBasePositionRaw htakeSpanClassRaw htakePointerRaw
  simp [bitsToSparseDenseFalseSelectLocatorEntry,
    sparseDenseFalseSelectLocatorEntryToBitsLE]
  rw [htakeBaseOccurrenceRaw, htakeBasePositionRaw, htakeSpanClassRaw,
    htakePointerRaw]
  simp [SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hbaseOccurrence,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hbasePosition,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hspanClass,
    SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt hpointer]

/-- Fixed-width payload table for super/local sparse-dense locator entries. -/
structure FixedWidthSparseDenseFalseSelectLocatorEntryTable
    (entries : List SparseDenseFalseSelectLocatorEntry)
    (fieldWidth : Nat) where
  payload : List Bool
  store : SuccinctSpace.PayloadWordStore payload
  payload_length_eq :
    payload.length =
      entries.length *
        sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits ->
        bits.length =
          sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth
  read_exact :
    forall i : Nat,
      (store.words[i]?).map
          (bitsToSparseDenseFalseSelectLocatorEntry fieldWidth) =
        entries[i]?

namespace FixedWidthSparseDenseFalseSelectLocatorEntryTable

def ofEncodedWords
    (entries : List SparseDenseFalseSelectLocatorEntry)
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToSparseDenseFalseSelectLocatorEntry fieldWidth) =
        entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length =
            sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth) :
    FixedWidthSparseDenseFalseSelectLocatorEntryTable entries fieldWidth where
  payload := SuccinctSpace.flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (SuccinctSpace.flattenPayloadWords words).length =
          words.length *
            sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth :=
        SuccinctSpace.flattenPayloadWords_length_of_forall_length hwidth
      _ =
          entries.length *
            sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth := by
        rw [<- hentries]
        simp
  word_length_of_get? := by
    intro i bits hget
    have hlist : words[i]? = some bits := by
      simpa [Array.getElem?_toList] using hget
    exact hwidth (List.mem_of_getElem? hlist)
  read_exact := by
    intro i
    have hmap :
        (words.map
            (bitsToSparseDenseFalseSelectLocatorEntry fieldWidth))[i]? =
          entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List SparseDenseFalseSelectLocatorEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseFalseSelectLocatorEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.basePosition < 2 ^ fieldWidth /\
              entry.spanClass < 2 ^ fieldWidth /\
                entry.pointer < 2 ^ fieldWidth) :
    FixedWidthSparseDenseFalseSelectLocatorEntryTable
      entries fieldWidth :=
  ofEncodedWords entries fieldWidth
    (entries.map
      (sparseDenseFalseSelectLocatorEntryToBitsLE fieldWidth)) (by
      induction entries with
      | nil =>
          simp
      | cons entry rest ih =>
          have hentry :
              bitsToSparseDenseFalseSelectLocatorEntry fieldWidth
                  (sparseDenseFalseSelectLocatorEntryToBitsLE
                    fieldWidth entry) =
                entry := by
            exact
              bitsToSparseDenseFalseSelectLocatorEntry_toBits_of_bound
                (hbound List.mem_cons_self)
          have hrest :
              forall {tailEntry : SparseDenseFalseSelectLocatorEntry},
                List.Mem tailEntry rest ->
                  tailEntry.baseOccurrence < 2 ^ fieldWidth /\
                    tailEntry.basePosition < 2 ^ fieldWidth /\
                      tailEntry.spanClass < 2 ^ fieldWidth /\
                        tailEntry.pointer < 2 ^ fieldWidth := by
            intro tailEntry hmem
            exact hbound (List.mem_cons_of_mem entry hmem)
          simp [hentry, ih hrest])
      (by
        intro word hmem
        rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
        exact
          sparseDenseFalseSelectLocatorEntryToBitsLE_length
            fieldWidth entry)

def readCosted
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    (i : Nat) :
    Costed (Option SparseDenseFalseSelectLocatorEntry) :=
  Costed.map
    (fun word? =>
      word?.map (bitsToSparseDenseFalseSelectLocatorEntry fieldWidth))
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_one
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, Costed.erase_map, table.read_exact i]

theorem payload_length
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth) :
    table.payload.length =
      entries.length *
        sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth :=
  table.payload_length_eq

theorem read_word_length_of_some
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    {i : Nat} {word : List Bool}
    (hword : table.store.words[i]? = some word) :
    word.length =
      sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth :=
  table.word_length_of_get? hword

theorem entry_fields_lt
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    {i : Nat} {entry : SparseDenseFalseSelectLocatorEntry}
    (hget : entries[i]? = some entry) :
    entry.baseOccurrence < 2 ^ fieldWidth /\
      entry.basePosition < 2 ^ fieldWidth /\
        entry.spanClass < 2 ^ fieldWidth /\
          entry.pointer < 2 ^ fieldWidth := by
  have hread := table.read_exact i
  rw [hget] at hread
  cases hword : table.store.words[i]? with
  | none =>
      simp [hword] at hread
  | some word =>
      have hentry :
          bitsToSparseDenseFalseSelectLocatorEntry fieldWidth word =
            entry := by
        simpa [hword] using hread
      subst entry
      exact
        bitsToSparseDenseFalseSelectLocatorEntry_fields_lt
          fieldWidth word

theorem read_word_length_le_machine
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth n : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    (hmachine :
      sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth <=
        SuccinctRankProposal.machineWordBits n)
    {i : Nat} {word : List Bool}
    (hword : table.store.words[i]? = some word) :
    word.length <= SuccinctRankProposal.machineWordBits n := by
  rw [table.read_word_length_of_some hword]
  exact hmachine

theorem profile
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth) :
    table.payload.length =
        entries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      SuccinctSpace.flattenPayloadWords table.store.words.toList =
        table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List SparseDenseFalseSelectLocatorEntry)
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToSparseDenseFalseSelectLocatorEntry fieldWidth) =
        entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length =
            sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth) :
    (ofEncodedWords entries fieldWidth words hentries hwidth).payload.length =
        entries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth /\
      (forall i,
        ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
          i).cost <= 1 /\
          ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
            i).erase = entries[i]?) /\
      SuccinctSpace.flattenPayloadWords
          (ofEncodedWords entries fieldWidth words hentries
            hwidth).store.words.toList =
        (ofEncodedWords entries fieldWidth words hentries hwidth).payload := by
  exact (ofEncodedWords entries fieldWidth words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List SparseDenseFalseSelectLocatorEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseFalseSelectLocatorEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.basePosition < 2 ^ fieldWidth /\
              entry.spanClass < 2 ^ fieldWidth /\
                entry.pointer < 2 ^ fieldWidth) :
    (ofEntries entries fieldWidth hbound).payload.length =
        entries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth fieldWidth /\
      (forall i,
        ((ofEntries entries fieldWidth hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries fieldWidth hbound).readCosted i).erase =
            entries[i]?) /\
      SuccinctSpace.flattenPayloadWords
          (ofEntries entries fieldWidth hbound).store.words.toList =
        (ofEntries entries fieldWidth hbound).payload := by
  exact (ofEntries entries fieldWidth hbound).profile

end FixedWidthSparseDenseFalseSelectLocatorEntryTable

/--
Dense-local false-select locator split across multiple payload words.

This supplements the four-field packed locator above: dense local queries need
the sampled occurrence and a relative/aligned view of the sampled position, but
the builder must not be forced to fit every field into one machine word at once.
-/
structure SparseDenseFalseSelectDenseLocalEntry where
  baseOccurrence : Nat
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat

namespace SparseDenseFalseSelectDenseLocalEntry

def baseOccurrences
    (entries : List SparseDenseFalseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.baseOccurrence)

def baseWordIndices
    (entries : List SparseDenseFalseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.baseWordIndex)

def ranksBefore
    (entries : List SparseDenseFalseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.rankBefore)

def firstOffsets
    (entries : List SparseDenseFalseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.firstOffset)

end SparseDenseFalseSelectDenseLocalEntry

def sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
    (entries : List SparseDenseFalseSelectDenseLocalEntry)
    (fieldWidth : Nat) : Nat :=
  entries.length * fieldWidth +
    entries.length * fieldWidth +
      entries.length * fieldWidth +
        entries.length * fieldWidth

/--
Multiword fixed-width payload table for dense-local false-select entries.

Each field is stored in its own fixed-width Nat table. Thus every payload word
is bounded by `fieldWidth`, and `fieldWidth <= machineWordBits n` is sufficient
for machine-word reads; no `4 * fieldWidth <= machineWordBits n` obligation is
introduced.
-/
structure FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
    (entries : List SparseDenseFalseSelectDenseLocalEntry)
    (fieldWidth : Nat) where
  baseOccurrenceTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseFalseSelectDenseLocalEntry.baseOccurrences entries)
      fieldWidth
  baseWordIndexTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseFalseSelectDenseLocalEntry.baseWordIndices entries)
      fieldWidth
  rankBeforeTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseFalseSelectDenseLocalEntry.ranksBefore entries)
      fieldWidth
  firstOffsetTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseFalseSelectDenseLocalEntry.firstOffsets entries)
      fieldWidth

namespace FixedWidthSparseDenseFalseSelectDenseLocalEntryTable

def entryOfFields
    (baseOccurrence baseWordIndex rankBefore firstOffset : Option Nat) :
    Option SparseDenseFalseSelectDenseLocalEntry :=
  match baseOccurrence, baseWordIndex, rankBefore, firstOffset with
  | some baseOccurrence, some baseWordIndex, some rankBefore,
      some firstOffset =>
      some {
        baseOccurrence := baseOccurrence
        baseWordIndex := baseWordIndex
        rankBefore := rankBefore
        firstOffset := firstOffset }
  | _, _, _, _ => none

theorem entryOfFields_get?
    (entries : List SparseDenseFalseSelectDenseLocalEntry)
    (i : Nat) :
    entryOfFields
        ((SparseDenseFalseSelectDenseLocalEntry.baseOccurrences entries)[i]?)
        ((SparseDenseFalseSelectDenseLocalEntry.baseWordIndices entries)[i]?)
        ((SparseDenseFalseSelectDenseLocalEntry.ranksBefore entries)[i]?)
        ((SparseDenseFalseSelectDenseLocalEntry.firstOffsets entries)[i]?) =
      entries[i]? := by
  induction entries generalizing i with
  | nil =>
      simp [entryOfFields,
        SparseDenseFalseSelectDenseLocalEntry.baseOccurrences,
        SparseDenseFalseSelectDenseLocalEntry.baseWordIndices,
        SparseDenseFalseSelectDenseLocalEntry.ranksBefore,
        SparseDenseFalseSelectDenseLocalEntry.firstOffsets]
  | cons entry rest ih =>
      cases i with
      | zero =>
          rcases entry with
            ⟨baseOccurrence, baseWordIndex, rankBefore, firstOffset⟩
          simp [entryOfFields,
            SparseDenseFalseSelectDenseLocalEntry.baseOccurrences,
            SparseDenseFalseSelectDenseLocalEntry.baseWordIndices,
            SparseDenseFalseSelectDenseLocalEntry.ranksBefore,
            SparseDenseFalseSelectDenseLocalEntry.firstOffsets]
      | succ i =>
          simpa [SparseDenseFalseSelectDenseLocalEntry.baseOccurrences,
            SparseDenseFalseSelectDenseLocalEntry.baseWordIndices,
            SparseDenseFalseSelectDenseLocalEntry.ranksBefore,
            SparseDenseFalseSelectDenseLocalEntry.firstOffsets]
            using ih i

def payload
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) : List Bool :=
  table.baseOccurrenceTable.payload ++
    table.baseWordIndexTable.payload ++
      table.rankBeforeTable.payload ++
        table.firstOffsetTable.payload

def readWords
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) : List (List Bool) :=
  table.baseOccurrenceTable.store.words.toList ++
    table.baseWordIndexTable.store.words.toList ++
      table.rankBeforeTable.store.words.toList ++
        table.firstOffsetTable.store.words.toList

def ofEntries
    (entries : List SparseDenseFalseSelectDenseLocalEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseFalseSelectDenseLocalEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.baseWordIndex < 2 ^ fieldWidth /\
              entry.rankBefore < 2 ^ fieldWidth /\
                entry.firstOffset < 2 ^ fieldWidth) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      entries fieldWidth where
  baseOccurrenceTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseFalseSelectDenseLocalEntry.baseOccurrences entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).1)
  baseWordIndexTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseFalseSelectDenseLocalEntry.baseWordIndices entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.1)
  rankBeforeTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseFalseSelectDenseLocalEntry.ranksBefore entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.2.1)
  firstOffsetTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseFalseSelectDenseLocalEntry.firstOffsets entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.2.2)

def readCosted
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    Costed (Option SparseDenseFalseSelectDenseLocalEntry) :=
  Costed.bind (table.baseOccurrenceTable.readCosted i)
    fun baseOccurrence? =>
      Costed.bind (table.baseWordIndexTable.readCosted i)
        fun baseWordIndex? =>
          Costed.bind (table.rankBeforeTable.readCosted i)
            fun rankBefore? =>
              Costed.map
                (fun firstOffset? =>
                  entryOfFields baseOccurrence? baseWordIndex?
                    rankBefore? firstOffset?)
                (table.firstOffsetTable.readCosted i)

@[simp] theorem readCosted_cost
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost = 4 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_four
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost <= 4 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simpa [readCosted, Costed.erase_bind, Costed.erase_map,
    SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    using entryOfFields_get? entries i

theorem entry_fields_lt
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    {i : Nat} {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hget : entries[i]? = some entry) :
    entry.baseOccurrence < 2 ^ fieldWidth /\
      entry.baseWordIndex < 2 ^ fieldWidth /\
        entry.rankBefore < 2 ^ fieldWidth /\
          entry.firstOffset < 2 ^ fieldWidth := by
  have hbase :
      (SparseDenseFalseSelectDenseLocalEntry.baseOccurrences entries)[i]? =
        some entry.baseOccurrence := by
    simpa [SparseDenseFalseSelectDenseLocalEntry.baseOccurrences,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseFalseSelectDenseLocalEntry =>
          entry.baseOccurrence)) hget
  have hword :
      (SparseDenseFalseSelectDenseLocalEntry.baseWordIndices entries)[i]? =
        some entry.baseWordIndex := by
    simpa [SparseDenseFalseSelectDenseLocalEntry.baseWordIndices,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseFalseSelectDenseLocalEntry =>
          entry.baseWordIndex)) hget
  have hrank :
      (SparseDenseFalseSelectDenseLocalEntry.ranksBefore entries)[i]? =
        some entry.rankBefore := by
    simpa [SparseDenseFalseSelectDenseLocalEntry.ranksBefore,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseFalseSelectDenseLocalEntry =>
          entry.rankBefore)) hget
  have hoffset :
      (SparseDenseFalseSelectDenseLocalEntry.firstOffsets entries)[i]? =
        some entry.firstOffset := by
    simpa [SparseDenseFalseSelectDenseLocalEntry.firstOffsets,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseFalseSelectDenseLocalEntry =>
          entry.firstOffset)) hget
  exact
    ⟨fixedWidthNatTable_entry_lt_two_pow
        table.baseOccurrenceTable hbase,
      fixedWidthNatTable_entry_lt_two_pow
        table.baseWordIndexTable hword,
      fixedWidthNatTable_entry_lt_two_pow
        table.rankBeforeTable hrank,
      fixedWidthNatTable_entry_lt_two_pow
        table.firstOffsetTable hoffset⟩

theorem payload_length
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) :
    table.payload.length =
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
        entries fieldWidth := by
  simp [payload,
    sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
    SparseDenseFalseSelectDenseLocalEntry.baseOccurrences,
    SparseDenseFalseSelectDenseLocalEntry.baseWordIndices,
    SparseDenseFalseSelectDenseLocalEntry.ranksBefore,
    SparseDenseFalseSelectDenseLocalEntry.firstOffsets,
    SuccinctSpace.FixedWidthNatTable.payload_length, Nat.add_assoc]

def ReadProfile
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) : Prop :=
  (forall i, (table.baseOccurrenceTable.readCosted i).cost <= 1 /\
    (table.baseOccurrenceTable.readCosted i).erase =
      (SparseDenseFalseSelectDenseLocalEntry.baseOccurrences entries)[i]?) /\
  (forall i, (table.baseWordIndexTable.readCosted i).cost <= 1 /\
    (table.baseWordIndexTable.readCosted i).erase =
      (SparseDenseFalseSelectDenseLocalEntry.baseWordIndices entries)[i]?) /\
  (forall i, (table.rankBeforeTable.readCosted i).cost <= 1 /\
    (table.rankBeforeTable.readCosted i).erase =
      (SparseDenseFalseSelectDenseLocalEntry.ranksBefore entries)[i]?) /\
  (forall i, (table.firstOffsetTable.readCosted i).cost <= 1 /\
    (table.firstOffsetTable.readCosted i).erase =
      (SparseDenseFalseSelectDenseLocalEntry.firstOffsets entries)[i]?) /\
  (forall i, (table.readCosted i).cost <= 4 /\
    (table.readCosted i).erase = entries[i]?)

theorem readProfile
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) :
    table.ReadProfile := by
  constructor
  · intro i
    exact ⟨table.baseOccurrenceTable.readCosted_cost_le_one i,
      table.baseOccurrenceTable.readCosted_erase i⟩
  · constructor
    · intro i
      exact ⟨table.baseWordIndexTable.readCosted_cost_le_one i,
        table.baseWordIndexTable.readCosted_erase i⟩
    · constructor
      · intro i
        exact ⟨table.rankBeforeTable.readCosted_cost_le_one i,
          table.rankBeforeTable.readCosted_erase i⟩
      · constructor
        · intro i
          exact ⟨table.firstOffsetTable.readCosted_cost_le_one i,
            table.firstOffsetTable.readCosted_erase i⟩
        · intro i
          exact ⟨table.readCosted_cost_le_four i,
            table.readCosted_erase i⟩

def ReadWordsLengthLeMachine
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (n : Nat) : Prop :=
  (forall {i : Nat} {word : List Bool},
    table.baseOccurrenceTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    table.baseWordIndexTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    table.rankBeforeTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    table.firstOffsetTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n)

theorem readWordsLengthLeMachine
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth n : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (hfield : fieldWidth <= SuccinctRankProposal.machineWordBits n) :
    table.ReadWordsLengthLeMachine n := by
  constructor
  · intro i word hword
    rw [table.baseOccurrenceTable.read_word_length_of_some hword]
    exact hfield
  · constructor
    · intro i word hword
      rw [table.baseWordIndexTable.read_word_length_of_some hword]
      exact hfield
    · constructor
      · intro i word hword
        rw [table.rankBeforeTable.read_word_length_of_some hword]
        exact hfield
      · intro i word hword
        rw [table.firstOffsetTable.read_word_length_of_some hword]
        exact hfield

theorem read_word_length_le_machine
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth n : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth)
    (hread : table.ReadWordsLengthLeMachine n)
    {word : List Bool}
    (hmem : List.Mem word table.readWords) :
    word.length <= SuccinctRankProposal.machineWordBits n := by
  rcases hread with ⟨hbase, hwordIndex, hrank, hoffset⟩
  rw [readWords] at hmem
  rcases List.mem_append.mp hmem with hprefix0 | hoffsetMem
  · rcases List.mem_append.mp hprefix0 with hprefix1 | hrankMem
    · rcases List.mem_append.mp hprefix1 with hbaseMem | hwordIndexMem
      · rcases (List.mem_iff_getElem?.mp hbaseMem) with ⟨i, hgetList⟩
        have hget :
            table.baseOccurrenceTable.store.words[i]? = some word := by
          simpa [Array.getElem?_toList] using hgetList
        exact hbase hget
      · rcases (List.mem_iff_getElem?.mp hwordIndexMem) with
          ⟨i, hgetList⟩
        have hget :
            table.baseWordIndexTable.store.words[i]? = some word := by
          simpa [Array.getElem?_toList] using hgetList
        exact hwordIndex hget
    · rcases (List.mem_iff_getElem?.mp hrankMem) with ⟨i, hgetList⟩
      have hget :
          table.rankBeforeTable.store.words[i]? = some word := by
        simpa [Array.getElem?_toList] using hgetList
      exact hrank hget
  · rcases (List.mem_iff_getElem?.mp hoffsetMem) with ⟨i, hgetList⟩
    have hget :
        table.firstOffsetTable.store.words[i]? = some word := by
      simpa [Array.getElem?_toList] using hgetList
    exact hoffset hget

theorem profile
    {entries : List SparseDenseFalseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
        entries fieldWidth) :
    table.payload.length =
        sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
          entries fieldWidth /\
      table.ReadProfile := by
  exact ⟨table.payload_length, table.readProfile⟩

theorem ofEntries_profile
    (entries : List SparseDenseFalseSelectDenseLocalEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseFalseSelectDenseLocalEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.baseWordIndex < 2 ^ fieldWidth /\
              entry.rankBefore < 2 ^ fieldWidth /\
                entry.firstOffset < 2 ^ fieldWidth) :
    (ofEntries entries fieldWidth hbound).payload.length =
        sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
          entries fieldWidth /\
      (ofEntries entries fieldWidth hbound).ReadProfile := by
  exact (ofEntries entries fieldWidth hbound).profile

end FixedWidthSparseDenseFalseSelectDenseLocalEntryTable

def fixedWidthLongSuperExplicitTable
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    SuccinctSpace.FixedWidthNatTable entries width :=
  SuccinctSpace.FixedWidthNatTable.ofEntries entries width hbound

theorem fixedWidthLongSuperExplicitTable_profile
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    (fixedWidthLongSuperExplicitTable entries width hbound).payload.length =
        entries.length * width /\
      (forall i,
        ((fixedWidthLongSuperExplicitTable entries width hbound).readCosted
          i).cost <= 1 /\
          ((fixedWidthLongSuperExplicitTable entries width hbound).readCosted
            i).erase = entries[i]?) /\
      SuccinctSpace.flattenPayloadWords
          (fixedWidthLongSuperExplicitTable entries width
            hbound).store.words.toList =
        (fixedWidthLongSuperExplicitTable entries width hbound).payload := by
  exact
    SuccinctSpace.FixedWidthNatTable.ofEntries_profile
      entries width hbound

def fixedWidthSparseLocalExplicitTable
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    SuccinctSpace.FixedWidthNatTable entries width :=
  SuccinctSpace.FixedWidthNatTable.ofEntries entries width hbound

theorem fixedWidthSparseLocalExplicitTable_profile
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    (fixedWidthSparseLocalExplicitTable entries width hbound).payload.length =
        entries.length * width /\
      (forall i,
        ((fixedWidthSparseLocalExplicitTable entries width hbound).readCosted
          i).cost <= 1 /\
          ((fixedWidthSparseLocalExplicitTable entries width hbound).readCosted
            i).erase = entries[i]?) /\
      SuccinctSpace.flattenPayloadWords
          (fixedWidthSparseLocalExplicitTable entries width
            hbound).store.words.toList =
        (fixedWidthSparseLocalExplicitTable entries width hbound).payload := by
  exact
    SuccinctSpace.FixedWidthNatTable.ofEntries_profile
      entries width hbound

def sparseDenseFalseSelectOverhead
    (superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots : Nat)
    (n : Nat) : Nat :=
  SuccinctSpace.sampledDirectoryOverhead superDirectorySlots n +
    SuccinctSpace.idDivLogLogOverhead longSuperExplicitSlots n +
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        localDirectorySlots n +
        SuccinctSpace.idDivLogLogOverhead sparseLocalExplicitSlots n

theorem sparseDenseFalseSelectOverhead_littleO
    (superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (sparseDenseFalseSelectOverhead
        superDirectorySlots longSuperExplicitSlots localDirectorySlots
        sparseLocalExplicitSlots) := by
  unfold sparseDenseFalseSelectOverhead
  simpa [Nat.add_assoc] using
    (((SuccinctSpace.sampledDirectoryOverhead_littleO
        superDirectorySlots).add
      (SuccinctSpace.idDivLogLogOverhead_littleO
        longSuperExplicitSlots)).add
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO
        localDirectorySlots)).add
      (SuccinctSpace.idDivLogLogOverhead_littleO
        sparseLocalExplicitSlots)

def sparseDenseFalseSelectCodecPayloadBudget
    (superEntries : List SparseDenseFalseSelectLocatorEntry)
    (longSuperExplicitEntries : List Nat)
    (localEntries : List SparseDenseFalseSelectLocatorEntry)
    (sparseLocalExplicitEntries : List Nat)
    (superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat) : Nat :=
  superEntries.length *
      sparseDenseFalseSelectLocatorEntryWordWidth superFieldWidth +
    longSuperExplicitEntries.length * longSuperExplicitWidth +
      localEntries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth localFieldWidth +
        sparseLocalExplicitEntries.length * sparseLocalExplicitWidth

/-- Payload codec bundle for the four sparse/dense false-select table classes. -/
structure SparseDenseFalseSelectCodecTables
    (superEntries : List SparseDenseFalseSelectLocatorEntry)
    (longSuperExplicitEntries : List Nat)
    (localEntries : List SparseDenseFalseSelectLocatorEntry)
    (sparseLocalExplicitEntries : List Nat)
    (superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat) where
  superTable :
    FixedWidthSparseDenseFalseSelectLocatorEntryTable
      superEntries superFieldWidth
  longSuperExplicitTable :
    SuccinctSpace.FixedWidthNatTable
      longSuperExplicitEntries longSuperExplicitWidth
  localTable :
    FixedWidthSparseDenseFalseSelectLocatorEntryTable
      localEntries localFieldWidth
  sparseLocalExplicitTable :
    SuccinctSpace.FixedWidthNatTable
      sparseLocalExplicitEntries sparseLocalExplicitWidth

namespace SparseDenseFalseSelectCodecTables

def payload
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth) :
    List Bool :=
  tables.superTable.payload ++
    tables.longSuperExplicitTable.payload ++
      tables.localTable.payload ++
        tables.sparseLocalExplicitTable.payload

theorem payload_length
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth) :
    tables.payload.length =
      sparseDenseFalseSelectCodecPayloadBudget
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth := by
  simp [payload, sparseDenseFalseSelectCodecPayloadBudget,
    FixedWidthSparseDenseFalseSelectLocatorEntryTable.payload_length,
    SuccinctSpace.FixedWidthNatTable.payload_length, Nat.add_assoc]

def ReadProfile
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth) : Prop :=
  (forall i, (tables.superTable.readCosted i).cost <= 1 /\
    (tables.superTable.readCosted i).erase = superEntries[i]?) /\
  (forall i, (tables.longSuperExplicitTable.readCosted i).cost <= 1 /\
    (tables.longSuperExplicitTable.readCosted i).erase =
      longSuperExplicitEntries[i]?) /\
  (forall i, (tables.localTable.readCosted i).cost <= 1 /\
    (tables.localTable.readCosted i).erase = localEntries[i]?) /\
  (forall i, (tables.sparseLocalExplicitTable.readCosted i).cost <= 1 /\
    (tables.sparseLocalExplicitTable.readCosted i).erase =
      sparseLocalExplicitEntries[i]?)

theorem readProfile
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth) :
    tables.ReadProfile := by
  constructor
  · intro i
    exact ⟨tables.superTable.readCosted_cost_le_one i,
      tables.superTable.readCosted_erase i⟩
  · constructor
    · intro i
      exact
        ⟨tables.longSuperExplicitTable.readCosted_cost_le_one i,
          tables.longSuperExplicitTable.readCosted_erase i⟩
    · constructor
      · intro i
        exact ⟨tables.localTable.readCosted_cost_le_one i,
          tables.localTable.readCosted_erase i⟩
      · intro i
        exact
          ⟨tables.sparseLocalExplicitTable.readCosted_cost_le_one i,
            tables.sparseLocalExplicitTable.readCosted_erase i⟩

def ReadWordsLengthLeMachine
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth)
    (n : Nat) : Prop :=
  (forall {i : Nat} {word : List Bool},
    tables.superTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    tables.longSuperExplicitTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    tables.localTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n) /\
  (forall {i : Nat} {word : List Bool},
    tables.sparseLocalExplicitTable.store.words[i]? = some word ->
      word.length <= SuccinctRankProposal.machineWordBits n)

theorem readWordsLengthLeMachine
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth n : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth)
    (hsuper :
      sparseDenseFalseSelectLocatorEntryWordWidth superFieldWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hlong :
      longSuperExplicitWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hlocal :
      sparseDenseFalseSelectLocatorEntryWordWidth localFieldWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hsparse :
      sparseLocalExplicitWidth <=
        SuccinctRankProposal.machineWordBits n) :
    tables.ReadWordsLengthLeMachine n := by
  constructor
  · intro i word hword
    exact tables.superTable.read_word_length_le_machine hsuper hword
  · constructor
    · intro i word hword
      rw [tables.longSuperExplicitTable.read_word_length_of_some hword]
      exact hlong
    · constructor
      · intro i word hword
        exact tables.localTable.read_word_length_le_machine hlocal hword
      · intro i word hword
        rw [tables.sparseLocalExplicitTable.read_word_length_of_some hword]
        exact hsparse

theorem payload_length_le_sparseDenseFalseSelectOverhead
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth)
    {superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots n : Nat}
    (hbudget :
      sparseDenseFalseSelectCodecPayloadBudget
          superEntries longSuperExplicitEntries localEntries
          sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
          localFieldWidth sparseLocalExplicitWidth <=
        sparseDenseFalseSelectOverhead
          superDirectorySlots longSuperExplicitSlots localDirectorySlots
          sparseLocalExplicitSlots n) :
    tables.payload.length <=
      sparseDenseFalseSelectOverhead
        superDirectorySlots longSuperExplicitSlots localDirectorySlots
        sparseLocalExplicitSlots n := by
  rw [tables.payload_length]
  exact hbudget

theorem profile_le_sparseDenseFalseSelectOverhead
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {superFieldWidth longSuperExplicitWidth localFieldWidth
      sparseLocalExplicitWidth : Nat}
    (tables :
      SparseDenseFalseSelectCodecTables
        superEntries longSuperExplicitEntries localEntries
        sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
        localFieldWidth sparseLocalExplicitWidth)
    {superDirectorySlots longSuperExplicitSlots localDirectorySlots
      sparseLocalExplicitSlots n : Nat}
    (hbudget :
      sparseDenseFalseSelectCodecPayloadBudget
          superEntries longSuperExplicitEntries localEntries
          sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
          localFieldWidth sparseLocalExplicitWidth <=
        sparseDenseFalseSelectOverhead
          superDirectorySlots longSuperExplicitSlots localDirectorySlots
          sparseLocalExplicitSlots n)
    (hsuper :
      sparseDenseFalseSelectLocatorEntryWordWidth superFieldWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hlong :
      longSuperExplicitWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hlocal :
      sparseDenseFalseSelectLocatorEntryWordWidth localFieldWidth <=
        SuccinctRankProposal.machineWordBits n)
    (hsparse :
      sparseLocalExplicitWidth <=
        SuccinctRankProposal.machineWordBits n) :
    SuccinctSpace.LittleOLinear
        (sparseDenseFalseSelectOverhead
          superDirectorySlots longSuperExplicitSlots localDirectorySlots
          sparseLocalExplicitSlots) /\
      tables.payload.length <=
        sparseDenseFalseSelectOverhead
          superDirectorySlots longSuperExplicitSlots localDirectorySlots
          sparseLocalExplicitSlots n /\
      tables.ReadProfile /\
      tables.ReadWordsLengthLeMachine n := by
  constructor
  · exact
      sparseDenseFalseSelectOverhead_littleO
        superDirectorySlots longSuperExplicitSlots localDirectorySlots
        sparseLocalExplicitSlots
  · constructor
    · exact
        tables.payload_length_le_sparseDenseFalseSelectOverhead hbudget
    · constructor
      · exact tables.readProfile
      · exact
          tables.readWordsLengthLeMachine hsuper hlong hlocal hsparse

end SparseDenseFalseSelectCodecTables

/--
A payload-live select component whose locator payload fits in a sampled
directory envelope.

The `overhead` is kept explicit because the current reusable select component
is exact-length.  The bound here is the bridge needed by a later packed
rank/select family that wants `<= sampledDirectoryOverhead slots n` accounting.
-/
structure SampledPayloadLiveStoredWordSelectData
    (bits : List Bool) (slots : Nat) where
  overhead : Nat
  data :
    SuccinctSpace.PayloadLiveStoredWordSelectData bits overhead
  overhead_le :
    overhead <= SuccinctSpace.sampledDirectoryOverhead slots bits.length

namespace SampledPayloadLiveStoredWordSelectData

def auxPayload
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots) :
    List Bool :=
  component.data.auxPayload

def selectCosted
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots)
    (target : Bool) (occurrence : Nat) :
    RMQ.Costed (Option Nat) :=
  component.data.selectCosted target occurrence

theorem auxPayload_length_le_sampled
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots) :
    component.auxPayload.length <=
      SuccinctSpace.sampledDirectoryOverhead slots bits.length := by
  have hlen := component.data.auxPayload_length
  unfold auxPayload
  rw [hlen]
  exact component.overhead_le

theorem selectCosted_cost_le_three
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots)
    (target : Bool) (occurrence : Nat) :
    (component.selectCosted target occurrence).cost <= 3 := by
  exact component.data.selectCosted_cost_le_three target occurrence

theorem selectCosted_exact
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots)
    (target : Bool) (occurrence : Nat) :
    (component.selectCosted target occurrence).erase =
      RMQ.Succinct.select target bits occurrence := by
  exact component.data.selectCosted_exact target occurrence

theorem profile
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordSelectData bits slots) :
    component.auxPayload.length <=
        SuccinctSpace.sampledDirectoryOverhead slots bits.length /\
      SuccinctSpace.flattenPayloadWords
          component.data.bitWords.words.toList = bits /\
      forall target occurrence,
        (component.selectCosted target occurrence).cost <= 3 /\
          (component.selectCosted target occurrence).erase =
            RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact component.auxPayload_length_le_sampled
  · constructor
    · exact component.data.bitWords.payload_eq_words_join
    · intro target occurrence
      exact ⟨component.selectCosted_cost_le_three target occurrence,
        component.selectCosted_exact target occurrence⟩

end SampledPayloadLiveStoredWordSelectData

/-- Bounded-envelope sampled select family. -/
structure SampledPayloadLiveStoredWordSelectFamily
    (slots : Nat) where
  component :
    forall bits : List Bool,
      SampledPayloadLiveStoredWordSelectData bits slots

namespace SampledPayloadLiveStoredWordSelectFamily

theorem bounded_constant_query_profile
    {slots : Nat}
    (family : SampledPayloadLiveStoredWordSelectFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length <=
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.component bits).data.bitWords.words.toList = bits /\
          forall target occurrence,
            ((family.component bits).selectCosted
                target occurrence).cost <= 3 /\
              ((family.component bits).selectCosted
                  target occurrence).erase =
                RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact SuccinctSpace.sampledDirectoryOverhead_littleO slots
  · intro bits
    exact (family.component bits).profile

end SampledPayloadLiveStoredWordSelectFamily

/--
Exact-envelope version: this is the form that can plug directly into existing
exact-length family interfaces once a concrete sampled-select builder is
available.
-/
structure ExactSampledPayloadLiveStoredWordSelectFamily
    (slots : Nat) where
  component :
    forall bits : List Bool,
      SuccinctSpace.PayloadLiveStoredWordSelectData bits
        (SuccinctSpace.sampledDirectoryOverhead slots bits.length)

namespace ExactSampledPayloadLiveStoredWordSelectFamily

def toSampledFamily
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordSelectFamily slots) :
    SampledPayloadLiveStoredWordSelectFamily slots where
  component bits :=
    { overhead := SuccinctSpace.sampledDirectoryOverhead slots bits.length
      data := family.component bits
      overhead_le := Nat.le_refl _ }

theorem constant_query_profile
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordSelectFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length =
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.component bits).bitWords.words.toList = bits /\
          forall target occurrence,
            ((family.component bits).selectCosted
                target occurrence).cost <= 3 /\
              ((family.component bits).selectCosted
                  target occurrence).erase =
                RMQ.Succinct.select target bits occurrence := by
  constructor
  · exact SuccinctSpace.sampledDirectoryOverhead_littleO slots
  · intro bits
    have hprofile := (family.component bits).profile
    exact hprofile

theorem bounded_constant_query_profile
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordSelectFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.toSampledFamily.component bits).auxPayload.length <=
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.toSampledFamily.component bits).data.bitWords.words.toList =
            bits /\
          forall target occurrence,
            ((family.toSampledFamily.component bits).selectCosted
                target occurrence).cost <= 3 /\
              ((family.toSampledFamily.component bits).selectCosted
                  target occurrence).erase =
                RMQ.Succinct.select target bits occurrence := by
  exact family.toSampledFamily.bounded_constant_query_profile

end ExactSampledPayloadLiveStoredWordSelectFamily

/-!
## Sparse/dense false-select close locator

This is the C1-specific close-select surface for `select false shape.bpCode`.
It reuses the packed four-field locator-entry codec above for super and
coarse local inventories, while dense-local payload fields are split across
`FixedWidthSparseDenseFalseSelectDenseLocalEntryTable`.  The dense case reads
that split dense entry before the two aligned BP payload-word fallback; all
directory reads go through payload-backed stores.
-/

/-- Canonical coarse slot budget for the sparse/dense false-select locator. -/
def canonicalSparseDenseFalseSelectOverhead (n : Nat) : Nat :=
  sparseDenseFalseSelectOverhead 32 32 32 32 (2 * n)

theorem canonicalSparseDenseFalseSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear canonicalSparseDenseFalseSelectOverhead := by
  unfold canonicalSparseDenseFalseSelectOverhead
  exact (sparseDenseFalseSelectOverhead_littleO 32 32 32 32).comp_two_mul_arg

/-- Fixed model cost for one sparse/dense close-select query. -/
def sparseDenseFalseSelectQueryCost : Nat := 16

def sparseDenseFalseSelectWordBits
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

def sparseDenseFalseSelectEll
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.log2 (sparseDenseFalseSelectWordBits shape) + 1

def sparseDenseFalseSelectSuperStride
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape *
    sparseDenseFalseSelectWordBits shape

def sparseDenseFalseSelectLocalStride
    (shape : Cartesian.CartesianShape) : Nat :=
  max 1
    (sparseDenseFalseSelectWordBits shape /
      (sparseDenseFalseSelectEll shape *
        sparseDenseFalseSelectEll shape))

def sparseDenseFalseSelectSuperLongSpan
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectSuperStride shape *
    sparseDenseFalseSelectWordBits shape *
      sparseDenseFalseSelectEll shape

def sparseDenseFalseSelectLocalSparseSpan
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape

def sparseDenseFalseSelectEntryIsMarked
    (entry : SparseDenseFalseSelectLocatorEntry) : Bool :=
  entry.spanClass != 0

/-- Collect target-bit positions, continuing from an absolute base offset. -/
def selectPositionsFrom
    (target : Bool) : List Bool -> Nat -> List Nat
  | [], _base => []
  | bit :: rest, base =>
      let tail := selectPositionsFrom target rest (base + 1)
      if bit = target then base :: tail else tail

/-- Collect all absolute positions whose bit equals `target`. -/
def selectPositions (target : Bool) (bits : List Bool) : List Nat :=
  selectPositionsFrom target bits 0

theorem selectPositionsFrom_get?_eq_selectFrom
    (target : Bool) (bits : List Bool) (base occurrence : Nat) :
    (selectPositionsFrom target bits base)[occurrence]? =
      RMQ.Succinct.selectFrom target bits base occurrence := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [selectPositionsFrom, RMQ.Succinct.selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · cases occurrence with
        | zero =>
            simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit]
        | succ occurrence =>
            simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
              ih (base + 1) occurrence]
      · simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
          ih (base + 1) occurrence]

theorem selectPositions_get?_eq_select
    (target : Bool) (bits : List Bool) (occurrence : Nat) :
    (selectPositions target bits)[occurrence]? =
      RMQ.Succinct.select target bits occurrence := by
  simp [selectPositions, RMQ.Succinct.select,
    selectPositionsFrom_get?_eq_selectFrom]

theorem selectPositionsFrom_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) (base : Nat) :
    (selectPositionsFrom target bits base).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  induction bits generalizing base with
  | nil =>
      simp [selectPositionsFrom, RMQ.Succinct.rankPrefix]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · simp [selectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1), Nat.add_comm]
      · simp [selectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1)]

theorem selectPositions_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) :
    (selectPositions target bits).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  simpa [selectPositions] using
    selectPositionsFrom_length_eq_rankPrefix_length target bits 0

theorem select_exists_of_lt_rankPrefix
    {target : Bool} {bits : List Bool} {occurrence limit : Nat}
    (hcount :
      occurrence < RMQ.Succinct.rankPrefix target bits limit) :
    exists pos, RMQ.Succinct.select target bits occurrence = some pos := by
  have hcountMin :
      occurrence <
        RMQ.Succinct.rankPrefix target bits
          (Nat.min limit bits.length) := by
    simpa [RMQ.Succinct.rankPrefix_min_length_eq] using hcount
  have htotal :
      occurrence <
        RMQ.Succinct.rankPrefix target bits bits.length := by
    exact Nat.lt_of_lt_of_le hcountMin
      (RMQ.Succinct.rankPrefix_mono_limit
        target bits (Nat.min_le_right limit bits.length))
  have hidx :
      occurrence < (selectPositions target bits).length := by
    simpa [selectPositions_length_eq_rankPrefix_length] using htotal
  refine ⟨(selectPositions target bits)[occurrence], ?_⟩
  have hget :
      (selectPositions target bits)[occurrence]? =
        some ((selectPositions target bits)[occurrence]) :=
    List.getElem?_eq_getElem hidx
  simpa [selectPositions_get?_eq_select] using hget

theorem select_none_of_rankPrefix_length_le
    {target : Bool} {bits : List Bool} {occurrence : Nat}
    (hcount :
      RMQ.Succinct.rankPrefix target bits bits.length <= occurrence) :
    RMQ.Succinct.select target bits occurrence = none := by
  have hget :
      (selectPositions target bits)[occurrence]? = none := by
    exact List.getElem?_eq_none (by
      simpa [selectPositions_length_eq_rankPrefix_length] using hcount)
  simpa [selectPositions_get?_eq_select] using hget

def builtLongExplicitFalseSelectEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  selectPositions false shape.bpCode

def builtLongExplicitFalseSelectSuperEntry :
    SparseDenseFalseSelectLocatorEntry where
  baseOccurrence := 0
  basePosition := 0
  spanClass := 1
  pointer := 0

def builtLongExplicitFalseSelectSuperEntries
    (_shape : Cartesian.CartesianShape) :
    List SparseDenseFalseSelectLocatorEntry :=
  [builtLongExplicitFalseSelectSuperEntry]

structure BuiltLongExplicitFalseSelectBranch
    (shape : Cartesian.CartesianShape) where
  superEntries : List SparseDenseFalseSelectLocatorEntry
  longSuperExplicitEntries : List Nat

def builtLongExplicitFalseSelectBranch
    (shape : Cartesian.CartesianShape) :
    BuiltLongExplicitFalseSelectBranch shape where
  superEntries := builtLongExplicitFalseSelectSuperEntries shape
  longSuperExplicitEntries := builtLongExplicitFalseSelectEntries shape

theorem builtLongExplicitFalseSelectSuperEntry_marked :
    sparseDenseFalseSelectEntryIsMarked
      builtLongExplicitFalseSelectSuperEntry = true := by
  simp [sparseDenseFalseSelectEntryIsMarked,
    builtLongExplicitFalseSelectSuperEntry]

theorem builtLongExplicitFalseSelectBranch_long_explicit_exact
    (shape : Cartesian.CartesianShape) (q : Nat) :
    (builtLongExplicitFalseSelectBranch shape).longSuperExplicitEntries[
        builtLongExplicitFalseSelectSuperEntry.pointer +
          (q - builtLongExplicitFalseSelectSuperEntry.baseOccurrence)]? =
      RMQ.Succinct.select false shape.bpCode q := by
  simp [builtLongExplicitFalseSelectBranch,
    builtLongExplicitFalseSelectEntries,
    builtLongExplicitFalseSelectSuperEntry,
    selectPositions_get?_eq_select]

theorem builtLongExplicitFalseSelectBranch_long_explicit_obligation
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectLocatorEntry)
    (hsuper :
      (builtLongExplicitFalseSelectBranch shape).superEntries[
          q / sparseDenseFalseSelectSuperStride shape]? = some super)
    (_hmarked : sparseDenseFalseSelectEntryIsMarked super = true) :
    (builtLongExplicitFalseSelectBranch shape).longSuperExplicitEntries[
        super.pointer + (q - super.baseOccurrence)]? =
      RMQ.Succinct.select false shape.bpCode q := by
  dsimp [builtLongExplicitFalseSelectBranch,
    builtLongExplicitFalseSelectSuperEntries] at hsuper ⊢
  cases hslot : q / sparseDenseFalseSelectSuperStride shape with
  | zero =>
      simp [hslot, builtLongExplicitFalseSelectSuperEntry] at hsuper
      subst super
      simp [builtLongExplicitFalseSelectEntries,
        selectPositions_get?_eq_select]
  | succ k =>
      simp [hslot] at hsuper

/--
Dense local fallback for a sparse/dense select interval.

The base position may be unaligned, so the query reads the aligned word
containing it and, only when necessary, the next aligned word.  The only
non-read primitives are counted word-rank and word-select operations.
-/
def denseTwoWordFalseSelectCosted
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind (bitWords.store.readWordCosted firstWordIndex) fun firstWord? =>
    match firstWord? with
    | none => Costed.pure none
    | some firstWord =>
        Costed.bind
          (RMQ.RAM.rankBoolWordPrefix false firstWord firstOffset).toCosted
          fun beforeFirst =>
            Costed.bind
              (RMQ.RAM.rankBoolWordPrefix
                false firstWord firstWord.length).toCosted
              fun uptoFirst =>
                let firstCount := uptoFirst - beforeFirst
                if localOccurrence < firstCount then
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => firstWordStart + offset)
                    (RMQ.RAM.selectBoolWord false firstWord
                      (beforeFirst + localOccurrence)).toCosted
                else
                  Costed.bind
                    (bitWords.store.readWordCosted (firstWordIndex + 1))
                    fun secondWord? =>
                      match secondWord? with
                      | none => Costed.pure none
                      | some secondWord =>
                          Costed.map
                            (fun local? =>
                              local?.map fun offset =>
                                (firstWordIndex + 1) * wordSize + offset)
                            (RMQ.RAM.selectBoolWord false secondWord
                              (localOccurrence - firstCount)).toCosted

theorem denseTwoWordFalseSelectCosted_cost_le_five
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).cost <= 5 := by
  unfold denseTwoWordFalseSelectCosted
  cases hfirst :
      (bitWords.store.readWordCosted
        (basePosition / wordSize)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      by_cases hchoose :
          q - baseOccurrence <
            RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
              RMQ.RAM.boolRankPrefix false firstWord
                (basePosition - basePosition / wordSize * wordSize)
      · simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose]
      · cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            simp [Costed.bind, Costed.pure, hfirst, hchoose,
              hsecond]
        | some secondWord =>
            simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose,
              hsecond]

def sparseDenseFalseSelectDenseLocalEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

def denseLocalEntryFalseSelectCosted
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) : Costed (Option Nat) :=
  denseTwoWordFalseSelectCosted bitWords
    (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
    entry.baseOccurrence q

theorem denseLocalEntryFalseSelectCosted_cost_le_five
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) :
    (denseLocalEntryFalseSelectCosted bitWords entry q).cost <= 5 := by
  exact
    denseTwoWordFalseSelectCosted_cost_le_five bitWords
      (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
      entry.baseOccurrence q

/-!
### Built sparse/dense false-select routing helpers

These helpers are the bridge between a concrete builder's entries and the
branch-exactness fields of `SparseDenseFalseSelectCloseData`.  They keep the
slot arithmetic explicit and leave only local construction facts for Worker A:
coverage for missing slots, built explicit-position segments for exception
payloads, and a dense local word certificate for the two-word fallback.
-/

def falseSelectSuperSlot (q superStride : Nat) : Nat :=
  q / superStride

/-- Number of rectangular local slots reserved for each super interval. -/
def falseSelectLocalSlotsPerSuper
    (superStride localStride : Nat) : Nat :=
  (superStride + localStride - 1) / localStride

/-- Local slot within one super interval, measured from the super base
occurrence. -/
def falseSelectLocalSlotInSuper
    (entry : SparseDenseFalseSelectLocatorEntry)
    (q localStride : Nat) : Nat :=
  (q - entry.baseOccurrence) / localStride

/-- Rectangular local-table slot for occurrence `q`.

This is the repaired route:
`superSlot * localSlotsPerSuper + localSlotInSuper`.  It deliberately ignores
`entry.pointer`, so packed super entries no longer smuggle an absolute local
table base.
-/
def falseSelectLocalSlot
    (q superStride localSlotsPerSuper localStride : Nat)
    (entry : SparseDenseFalseSelectLocatorEntry)
    : Nat :=
  falseSelectSuperSlot q superStride * localSlotsPerSuper +
    falseSelectLocalSlotInSuper entry q localStride

/-- Padded sparse-local explicit slot derived from the rectangular local slot.

The sparse branch uses one padded block of `localStride` relative offsets per
local slot, rather than an absolute pointer packed into every local entry.
-/
def falseSelectSparseLocalExplicitSlot
    (localSlot q localStride : Nat)
    (entry : SparseDenseFalseSelectLocatorEntry) : Nat :=
  localSlot * localStride + (q - entry.baseOccurrence)

def falseSelectOccurrenceCount
    (shape : Cartesian.CartesianShape) : Nat :=
  RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length

theorem falseSelectOccurrenceCount_eq_size
    (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape = shape.size := by
  exact SuccinctSpace.bpCode_rankFalse_full shape

def falseSelectCeilDiv (n stride : Nat) : Nat :=
  (n + stride - 1) / stride

def builtRectangularFalseSelectSuperSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  falseSelectCeilDiv (falseSelectOccurrenceCount shape)
    (sparseDenseFalseSelectSuperStride shape)

def builtRectangularFalseSelectLocalSlotsPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  falseSelectLocalSlotsPerSuper
    (sparseDenseFalseSelectSuperStride shape)
    (sparseDenseFalseSelectLocalStride shape)

def builtRectangularFalseSelectLocalSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularFalseSelectSuperSlotCount shape *
    builtRectangularFalseSelectLocalSlotsPerSuper shape

theorem sparseDenseFalseSelectWordBits_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectWordBits shape := by
  simp [sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits_pos]

theorem sparseDenseFalseSelectSuperStride_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectSuperStride shape := by
  unfold sparseDenseFalseSelectSuperStride
  exact Nat.mul_pos (sparseDenseFalseSelectWordBits_pos shape)
    (sparseDenseFalseSelectWordBits_pos shape)

theorem sparseDenseFalseSelectLocalStride_pos
    (shape : Cartesian.CartesianShape) :
    0 < sparseDenseFalseSelectLocalStride shape := by
  unfold sparseDenseFalseSelectLocalStride
  omega

theorem builtRectangularFalseSelectLocalSlotsPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRectangularFalseSelectLocalSlotsPerSuper shape := by
  unfold builtRectangularFalseSelectLocalSlotsPerSuper
    falseSelectLocalSlotsPerSuper
  exact Nat.div_pos
    (by
      have hsuper := sparseDenseFalseSelectSuperStride_pos shape
      omega)
    (sparseDenseFalseSelectLocalStride_pos shape)

def builtRectangularFalseSelectLocalSlotInSuperOfGlobal
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  globalLocalSlot -
    (globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape) *
        builtRectangularFalseSelectLocalSlotsPerSuper shape

def builtRectangularFalseSelectLocalBaseOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let superSlot :=
    globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape
  let localSlotInSuper :=
    builtRectangularFalseSelectLocalSlotInSuperOfGlobal
      shape globalLocalSlot
  superSlot * sparseDenseFalseSelectSuperStride shape +
    localSlotInSuper * sparseDenseFalseSelectLocalStride shape

theorem builtRectangularFalseSelectLocalBaseOccurrence_mod
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot =
      (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectSuperStride shape +
        (globalLocalSlot %
            builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectLocalStride shape := by
  unfold builtRectangularFalseSelectLocalBaseOccurrence
    builtRectangularFalseSelectLocalSlotInSuperOfGlobal
  rw [Nat.mod_eq_sub_div_mul]

theorem builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <
      (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) *
          sparseDenseFalseSelectSuperStride shape +
        sparseDenseFalseSelectSuperStride shape := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocal : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  have hceil :
      (r + 1) * localStride <=
        superStride + localStride - 1 := by
    have hle : r + 1 <= slots := by omega
    have hleDiv :
        r + 1 <=
          (superStride + localStride - 1) / localStride := by
      simpa [slots, superStride, localStride,
        builtRectangularFalseSelectLocalSlotsPerSuper,
        falseSelectLocalSlotsPerSuper] using hle
    exact Nat.mul_le_of_le_div localStride (r + 1)
      (superStride + localStride - 1) hleDiv
  have hrLocal : r * localStride < superStride := by
    rw [Nat.add_mul, Nat.one_mul] at hceil
    omega
  rw [hbase]
  simpa [q, slots, superStride] using (by omega :
    q * superStride + r * localStride <
      q * superStride + superStride)

theorem builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape (globalLocalSlot + 1) := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocal : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  by_cases hnextLocal : r + 1 < slots
  · have hn1 :
        globalLocalSlot + 1 = q * slots + (r + 1) := by
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by
              rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by
              exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by
              rw [Nat.div_eq_of_lt hnextLocal]
              omega
    have hmod :
        (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by
              exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          q * superStride + (r + 1) * localStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, localStride, hdiv, hmod]
    rw [hbase, hnext]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have hlast : r + 1 = slots := by omega
    have hn1 :
        globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]
      exact Nat.mul_div_left (q + 1) hslots
    have hmod :
        (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]
      exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          (q + 1) * superStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, hdiv, hmod]
    have hboundary :=
      builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
        shape globalLocalSlot
    rw [hnext]
    rw [Nat.add_mul, Nat.one_mul]
    simpa [q, slots, superStride] using Nat.le_of_lt hboundary

def falseSelectPositions (bits : List Bool) (base count : Nat) :
    List Nat :=
  (List.range count).map fun offset =>
    (RMQ.Succinct.select false bits (base + offset)).getD bits.length

def builtRelativeSplitFalseSelectPosition
    (shape : Cartesian.CartesianShape) (occurrence : Nat) : Nat :=
  (RMQ.Succinct.select false shape.bpCode occurrence).getD
    shape.bpCode.length

def builtRelativeSplitFalseSelectLocalEndOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot +
      sparseDenseFalseSelectLocalStride shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectLocalSpan
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectLocalEndOccurrence shape globalLocalSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

def builtRelativeSplitFalseSelectLocalIsSparse
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Bool :=
  decide
    (sparseDenseFalseSelectWordBits shape <
      builtRelativeSplitFalseSelectLocalSpan shape globalLocalSlot)

def builtRelativeSplitFalseSelectSuperBaseOccurrence
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  superSlot * sparseDenseFalseSelectSuperStride shape

def builtRelativeSplitFalseSelectSuperEndOccurrence
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  Nat.min
    (builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
      sparseDenseFalseSelectSuperStride shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectSuperSpan
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

def builtRelativeSplitFalseSelectSuperIsLong
    (shape : Cartesian.CartesianShape) (superSlot : Nat) : Bool :=
  decide
    (sparseDenseFalseSelectSuperLongSpan shape <
      builtRelativeSplitFalseSelectSuperSpan shape superSlot)

def builtRelativeSplitFalseSelectLocalSuperSlot
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  globalLocalSlot /
    builtRectangularFalseSelectLocalSlotsPerSuper shape

def builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  Nat.min
    (builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot +
      sparseDenseFalseSelectLocalStride shape)
    (builtRelativeSplitFalseSelectSuperEndOccurrence shape
      (builtRelativeSplitFalseSelectLocalSuperSlot
        shape globalLocalSlot))

def builtRelativeSplitFalseSelectShortSuperLocalSpan
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Nat :=
  let baseOccurrence :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let endOccurrence :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  let lastPosition :=
    builtRelativeSplitFalseSelectPosition shape (endOccurrence - 1)
  lastPosition + 1 - basePosition

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot <=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape (globalLocalSlot + 1) := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let q := globalLocalSlot / slots
  let r := globalLocalSlot % slots
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hr : r < slots := Nat.mod_lt _ hslots
  have hdecomp : globalLocalSlot = q * slots + r := by
    have h := Nat.div_add_mod globalLocalSlot slots
    simpa [q, r, Nat.mul_comm] using h.symm
  have hbase :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot =
        q * superStride + r * localStride := by
    simpa [q, r, slots, superStride, localStride] using
      builtRectangularFalseSelectLocalBaseOccurrence_mod
        shape globalLocalSlot
  have hendBase :
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot <=
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot +
          localStride := by
    unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    exact Nat.min_le_left _ _
  have hendSuper :
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot <=
        q * superStride + superStride := by
    have hsuperEnd :
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape globalLocalSlot) <=
          q * superStride + superStride := by
      unfold builtRelativeSplitFalseSelectSuperEndOccurrence
        builtRelativeSplitFalseSelectSuperBaseOccurrence
        builtRelativeSplitFalseSelectLocalSuperSlot
      exact Nat.min_le_left _ _
    exact Nat.le_trans (Nat.min_le_right _ _) (by
      simpa [q, slots, superStride] using hsuperEnd)
  by_cases hnextLocal : r + 1 < slots
  · have hn1 :
        globalLocalSlot + 1 = q * slots + (r + 1) := by
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q := by
      calc
        (globalLocalSlot + 1) / slots =
            (q * slots + (r + 1)) / slots := by rw [hn1]
        _ = ((r + 1) + slots * q) / slots := by
              rw [Nat.mul_comm, Nat.add_comm]
        _ = (r + 1) / slots + q := by
              exact Nat.add_mul_div_left (r + 1) q hslots
        _ = q := by
              rw [Nat.div_eq_of_lt hnextLocal]
              omega
    have hmod :
        (globalLocalSlot + 1) % slots = r + 1 := by
      calc
        (globalLocalSlot + 1) % slots =
            (q * slots + (r + 1)) % slots := by rw [hn1]
        _ = r + 1 := by
              exact Nat.mul_add_mod_of_lt hnextLocal
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          q * superStride + (r + 1) * localStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, localStride, hdiv, hmod]
    rw [hnext]
    have h := hendBase
    rw [hbase] at h
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h
  · have hlast : r + 1 = slots := by omega
    have hn1 :
        globalLocalSlot + 1 = (q + 1) * slots := by
      rw [hdecomp, Nat.add_mul, Nat.one_mul]
      omega
    have hdiv :
        (globalLocalSlot + 1) / slots = q + 1 := by
      rw [hn1]
      exact Nat.mul_div_left (q + 1) hslots
    have hmod :
        (globalLocalSlot + 1) % slots = 0 := by
      rw [hn1]
      exact Nat.mul_mod_left (q + 1) slots
    have hnext :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1) =
          (q + 1) * superStride := by
      rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
      simp [q, slots, superStride, hdiv, hmod]
    rw [hnext]
    have h := hendSuper
    simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
      Nat.add_left_comm] using h

def builtRelativeSplitFalseSelectLocalIsSparseException
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) : Bool :=
  (! builtRelativeSplitFalseSelectSuperIsLong shape
      (builtRelativeSplitFalseSelectLocalSuperSlot
        shape globalLocalSlot)) &&
    decide
      (sparseDenseFalseSelectWordBits shape <
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot)

def falseSelectRelativeOffsetsOrZero
    (bits : List Bool) (baseOccurrence count endOccurrence
      basePosition : Nat) : List Nat :=
  (List.range count).map fun offset =>
    if baseOccurrence + offset < endOccurrence then
      match RMQ.Succinct.select false bits (baseOccurrence + offset) with
      | some pos => pos - basePosition
      | none => 0
    else
      0

def builtRelativeSplitFalseSelectSparseExceptionFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).map
    (builtRelativeSplitFalseSelectLocalIsSparseException shape)

def builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.min (builtRectangularFalseSelectLocalSlotCount shape)
    (falseSelectOccurrenceCount shape)

def builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape)).map
    (builtRelativeSplitFalseSelectLocalIsSparseException shape)

def builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    List Nat :=
  if builtRelativeSplitFalseSelectLocalIsSparseException
      shape globalLocalSlot then
    let superSlot :=
      builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
    let baseOccurrence :=
      builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
      basePosition
  else
    []

def builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape)

def builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (Nat.min shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape))

theorem natLog2_le_log2_of_le
    {m n : Nat} (hm : m ≠ 0) (hn : n ≠ 0) (hle : m <= n) :
    Nat.log2 m <= Nat.log2 n := by
  have hpow : 2 ^ Nat.log2 m <= n :=
    Nat.le_trans (Nat.log2_self_le hm) hle
  exact (Nat.le_log2 hn).mpr hpow

theorem machineWordBits_mono_le
    {m n : Nat} (hle : m <= n) :
    SuccinctRankProposal.machineWordBits m <=
      SuccinctRankProposal.machineWordBits n := by
  unfold SuccinctRankProposal.machineWordBits
  by_cases hm : m = 0
  · simp [hm]
  · have hn : n ≠ 0 := by omega
    exact Nat.succ_le_succ (natLog2_le_log2_of_le hm hn hle)

theorem nat_div_succ_le_div_add_one
    (n w : Nat) (hw : 0 < w) :
    (n + 1) / w <= n / w + 1 := by
  apply Nat.div_le_of_le_mul
  have hlt : n < n / w * w + w :=
    Nat.lt_div_mul_add hw (a := n)
  calc
    n + 1 <= n / w * w + w := by omega
    _ = (n / w + 1) * w := by
      rw [Nat.add_mul]
      simp [Nat.mul_comm, Nat.add_comm]
    _ = w * (n / w + 1) := by
      rw [Nat.mul_comm]

theorem nat_div_add_sub_div_le_add
    (b d w : Nat) (hw : 0 < w) :
    (b + d) / w - b / w <= d := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hstep :
          (b + (d + 1)) / w <= (b + d) / w + 1 := by
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          nat_div_succ_le_div_add_one (b + d) w hw
      have hmono :
          b / w <= (b + d) / w :=
        Nat.div_le_div_right (by omega)
      omega

theorem nat_div_sub_div_le_sub
    {a b w : Nat} (hw : 0 < w) (hb : b <= a) :
    a / w - b / w <= a - b := by
  have hsplit : a = b + (a - b) := by omega
  rw [hsplit]
  simpa using nat_div_add_sub_div_le_add b (a - b) w hw

theorem one_lt_two_pow_of_pos {k : Nat} (hk : 0 < k) :
    1 < 2 ^ k := by
  cases k with
  | zero =>
      omega
  | succ k =>
      have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega : 0 < 2)
      simp [Nat.pow_succ]
      omega

theorem machineWordBits_le_self_of_pos {n : Nat} (hn : 0 < n) :
    SuccinctRankProposal.machineWordBits n <= n := by
  unfold SuccinctRankProposal.machineWordBits
  by_cases hone : n = 1
  · subst n
    have hpow := Nat.log2_self_le (n := 1) (by omega : 1 ≠ 0)
    by_cases hlog : 0 < Nat.log2 1
    · have htwo : 2 <= 2 ^ Nat.log2 1 := by
        have honeLt := one_lt_two_pow_of_pos hlog
        omega
      omega
    · omega
  · have hn_ne : n ≠ 0 := by omega
    have htwo : 2 <= n := by omega
    have hpow : n < 2 ^ n := by
      have hsucc := SuccinctSpace.nat_succ_le_two_pow n
      omega
    have hlog_lt : Nat.log2 n < n :=
      (Nat.log2_lt hn_ne).2 hpow
    omega

theorem lt_two_pow_machineWordBits_of_lt
    {x n : Nat} (hx : x < n) :
    x < 2 ^ SuccinctRankProposal.machineWordBits n := by
  exact Nat.lt_trans hx
    (by
      simpa [SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := n)))

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
  exact machineWordBits_mono_le
    (Nat.min_le_left shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape))

theorem natLog2_succ_le_of_pos_lt_pow
    {n k : Nat} (hnpos : 0 < n) (hlt : n < 2 ^ k) :
    Nat.log2 n + 1 <= k := by
  by_cases hk : k <= Nat.log2 n
  · have hn : n ≠ 0 := by omega
    have hpow : 2 ^ k <= n := (Nat.le_log2 hn).1 hk
    omega
  · omega

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
      4 * sparseDenseFalseSelectEll shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let m :=
    Nat.min shape.bpCode.length
      (sparseDenseFalseSelectSuperLongSpan shape)
  by_cases hm : m = 0
  · have hell_pos : 0 < ell := by
      simp [ell, sparseDenseFalseSelectEll]
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRankProposal.machineWordBits, m, hm,
      sparseDenseFalseSelectEll]
    omega
  · have hmpos : 0 < m := Nat.pos_of_ne_zero hm
    have hword_pos : 0 < wordBits := by
      simp [wordBits, sparseDenseFalseSelectWordBits,
        SuccinctRankProposal.machineWordBits_pos]
    have hell_pos : 0 < ell := by
      simp [ell, sparseDenseFalseSelectEll]
    have hword_lt_pow :
        wordBits < 2 ^ ell := by
      simpa [wordBits, ell, sparseDenseFalseSelectEll,
        sparseDenseFalseSelectWordBits,
        SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := wordBits))
    have hword_le_pow : wordBits <= 2 ^ ell :=
      Nat.le_of_lt hword_lt_pow
    have hell_le_pow : ell <= 2 ^ ell :=
      SuccinctSpace.nat_le_two_pow ell
    have hww_le :
        wordBits * wordBits <= 2 ^ ell * 2 ^ ell :=
      Nat.mul_le_mul hword_le_pow hword_le_pow
    have hww_pos : 0 < wordBits * wordBits :=
      Nat.mul_pos hword_pos hword_pos
    have hwww_lt_step :
        (wordBits * wordBits) * wordBits <
          (wordBits * wordBits) * 2 ^ ell :=
      Nat.mul_lt_mul_of_pos_left hword_lt_pow hww_pos
    have hwww_le_step :
        (wordBits * wordBits) * 2 ^ ell <=
          (2 ^ ell * 2 ^ ell) * 2 ^ ell :=
      Nat.mul_le_mul_right (2 ^ ell) hww_le
    have hwww_lt :
        wordBits * wordBits * wordBits <
          2 ^ ell * 2 ^ ell * 2 ^ ell := by
      exact Nat.lt_of_lt_of_le
        (by simpa [Nat.mul_assoc] using hwww_lt_step)
        (by simpa [Nat.mul_assoc] using hwww_le_step)
    have hleft_lt :
        (wordBits * wordBits * wordBits) * ell <
          (2 ^ ell * 2 ^ ell * 2 ^ ell) * ell :=
      Nat.mul_lt_mul_of_pos_right hwww_lt hell_pos
    have hright_le :
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * ell <=
          (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell :=
      Nat.mul_le_mul_left (2 ^ ell * 2 ^ ell * 2 ^ ell)
        hell_le_pow
    have hpows :
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell =
          2 ^ (4 * ell) := by
      calc
        (2 ^ ell * 2 ^ ell * 2 ^ ell) * 2 ^ ell =
            (((2 ^ ell * 2 ^ ell) * 2 ^ ell) * 2 ^ ell) := by
              simp [Nat.mul_assoc]
        _ = ((2 ^ (ell + ell) * 2 ^ ell) * 2 ^ ell) := by
              rw [← Nat.pow_add]
        _ = (2 ^ (ell + ell + ell) * 2 ^ ell) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (ell + ell + ell + ell) := by
              rw [← Nat.pow_add]
        _ = 2 ^ (4 * ell) := by
              congr 1
              omega
    have hsuper_lt :
        sparseDenseFalseSelectSuperLongSpan shape < 2 ^ (4 * ell) := by
      have hraw :
          (wordBits * wordBits * wordBits) * ell <
            2 ^ (4 * ell) := by
        have h :=
          Nat.lt_of_lt_of_le hleft_lt hright_le
        rwa [hpows] at h
      simpa [sparseDenseFalseSelectSuperLongSpan,
        sparseDenseFalseSelectSuperStride, wordBits, ell,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hraw
    have hm_lt : m < 2 ^ (4 * ell) := by
      exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) hsuper_lt
    have hlog := natLog2_succ_le_of_pos_lt_pow hmpos hm_lt
    simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRankProposal.machineWordBits, m, ell] using hlog

theorem nat_succ_square_le_two_pow_of_six_le
    (q : Nat) :
    6 <= q -> (q + 1) * (q + 1) <= 2 ^ q := by
  exact Nat.strongRecOn q (fun q ih hq => by
    by_cases hq8 : 8 <= q
    · have hprev : 6 <= q - 2 := by omega
      have hprev_lt : q - 2 < q := by omega
      have ihprev := ih (q - 2) hprev_lt hprev
      have hlin : q + 1 <= 2 * ((q - 2) + 1) := by omega
      have hsq :
          (q + 1) * (q + 1) <=
            2 * (2 * (((q - 2) + 1) * ((q - 2) + 1))) := by
        have hmul := Nat.mul_le_mul hlin hlin
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hpowMul : 2 * (2 * 2 ^ (q - 2)) = 2 ^ q := by
        have hqeq : q = (q - 2) + 2 := by omega
        calc
          2 * (2 * 2 ^ (q - 2)) = 2 ^ ((q - 2) + 2) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by rw [← hqeq]
      exact Nat.le_trans hsq
        (by
          have hmul := Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left 2 ihprev)
          simpa [hpowMul] using hmul)
    · have hqCases : q = 6 ∨ q = 7 := by omega
      rcases hqCases with hqeq | hqeq
      · subst q
        decide
      · subst q
        decide)

theorem sparseDenseFalseSelectEll_square_le_sixtyFour_wordBits
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectEll shape *
        sparseDenseFalseSelectEll shape <=
      64 * sparseDenseFalseSelectWordBits shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let q := Nat.log2 wordBits
  have hword_pos : 0 < wordBits := by
    simp [wordBits, sparseDenseFalseSelectWordBits,
      SuccinctRankProposal.machineWordBits_pos]
  by_cases hlarge : 6 <= q
  · have hword_ne : wordBits ≠ 0 := by omega
    have hsq :
        (q + 1) * (q + 1) <= wordBits :=
      Nat.le_trans
        (nat_succ_square_le_two_pow_of_six_le q hlarge)
        (Nat.log2_self_le hword_ne)
    have hword_le : wordBits <= 64 * wordBits := by omega
    exact Nat.le_trans
      (by
        simpa [q, wordBits, sparseDenseFalseSelectEll] using hsq)
      hword_le
  · have hq_le : q <= 5 := by omega
    have hell_le :
        sparseDenseFalseSelectEll shape <= 6 := by
      simpa [sparseDenseFalseSelectEll, q, wordBits] using
        Nat.succ_le_succ hq_le
    have hell_square_le :
        sparseDenseFalseSelectEll shape *
            sparseDenseFalseSelectEll shape <= 6 * 6 :=
      Nat.mul_le_mul hell_le hell_le
    have hword_one : 1 <= wordBits := by omega
    have hconst : 6 * 6 <= 64 * wordBits := by omega
    exact Nat.le_trans hell_square_le hconst

theorem builtRelativeSplitFalseSelectSparseException_localStride_mul_width_mul_ell_le_const_wordBits
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectLocalStride shape *
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape *
        sparseDenseFalseSelectEll shape <=
      512 * sparseDenseFalseSelectWordBits shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let denom := ell * ell
  let q := wordBits / denom
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  have hstride : localStride <= q + 1 := by
    have hmax : max 1 q <= q + 1 := by
      exact Nat.max_le.2 ⟨Nat.succ_pos q, Nat.le_succ q⟩
    simpa [localStride, q, denom, wordBits, ell,
      sparseDenseFalseSelectLocalStride, sparseDenseFalseSelectEll] using
      hmax
  have hwidth : relativeWidth <= 4 * ell := by
    simpa [relativeWidth, ell] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
        shape
  have hfirst :
      localStride * relativeWidth * ell <=
        (q + 1) * (4 * ell) * ell := by
    have hmul := Nat.mul_le_mul hstride hwidth
    exact Nat.mul_le_mul_right ell hmul
  have hqdenom : q * denom <= wordBits := by
    exact Nat.div_mul_le_self wordBits denom
  have hqdenom_succ :
      (q + 1) * denom <= wordBits + denom := by
    calc
      (q + 1) * denom = q * denom + denom := by
        rw [Nat.add_mul]
        simp
      _ <= wordBits + denom := Nat.add_le_add_right hqdenom denom
  have hell_square :
      denom <= 64 * wordBits := by
    simpa [denom, ell, wordBits] using
      sparseDenseFalseSelectEll_square_le_sixtyFour_wordBits shape
  have hqdenom_budget :
      4 * ((q + 1) * denom) <= 512 * wordBits := by
    have hsum : wordBits + denom <= 65 * wordBits := by
      omega
    have hsucc_le : (q + 1) * denom <= 65 * wordBits :=
      Nat.le_trans hqdenom_succ hsum
    have hmul := Nat.mul_le_mul_left 4 hsucc_le
    omega
  have hright :
      (q + 1) * (4 * ell) * ell <= 512 * wordBits := by
    have hrewrite :
        (q + 1) * (4 * ell) * ell =
      4 * ((q + 1) * denom) := by
      simp [denom, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
    simpa [hrewrite] using hqdenom_budget
  exact Nat.le_trans hfirst hright

theorem falseSelectCeilDiv_mul_le_add
    (n stride : Nat) :
    falseSelectCeilDiv n stride * stride <= n + stride := by
  unfold falseSelectCeilDiv
  have hdiv :
      ((n + stride - 1) / stride) * stride <=
        n + stride - 1 := Nat.div_mul_le_self _ _
  omega

theorem falseSelectLocalSlotsPerSuper_mul_localStride_le_add
    (superStride localStride : Nat) :
    falseSelectLocalSlotsPerSuper superStride localStride *
        localStride <=
      superStride + localStride := by
  unfold falseSelectLocalSlotsPerSuper
  have hdiv :
      ((superStride + localStride - 1) / localStride) *
          localStride <=
        superStride + localStride - 1 := Nat.div_mul_le_self _ _
  omega

theorem nat_succ_square_le_four_mul_two_pow (q : Nat) :
    (q + 1) * (q + 1) <= 4 * 2 ^ q := by
  by_cases hlarge : 6 <= q
  · have hsq := nat_succ_square_le_two_pow_of_six_le q hlarge
    exact Nat.le_trans hsq (by
      have hpos : 0 < 2 ^ q := Nat.pow_pos (by omega : 0 < 2)
      omega)
  · have hq : q = 0 ∨ q = 1 ∨ q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 5 := by
      omega
    rcases hq with hq | hq | hq | hq | hq | hq
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide
    · subst q
      decide

theorem machineWordBits_sq_le_four_mul_self_of_pos
    {n : Nat} (hn : 0 < n) :
    SuccinctRankProposal.machineWordBits n *
        SuccinctRankProposal.machineWordBits n <=
      4 * n := by
  let q := Nat.log2 n
  have hn_ne : n ≠ 0 := by omega
  have hpow : 2 ^ q <= n := by
    simpa [q] using Nat.log2_self_le hn_ne
  have hsq :
      (q + 1) * (q + 1) <= 4 * 2 ^ q :=
    nat_succ_square_le_four_mul_two_pow q
  have hscale :
      4 * 2 ^ q <= 4 * n := Nat.mul_le_mul_left 4 hpow
  exact Nat.le_trans (by
    simpa [q, SuccinctRankProposal.machineWordBits] using hsq) hscale

theorem sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectWordBits shape <=
      2 * sparseDenseFalseSelectLocalStride shape *
        (sparseDenseFalseSelectEll shape *
          sparseDenseFalseSelectEll shape) := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let denom := ell * ell
  let q := wordBits / denom
  let localStride := sparseDenseFalseSelectLocalStride shape
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hdenom_pos : 0 < denom := Nat.mul_pos hell_pos hell_pos
  have hlt : wordBits < q * denom + denom := by
    simpa [q, denom] using Nat.lt_div_mul_add hdenom_pos (a := wordBits)
  have hsucc_le :
      q + 1 <= 2 * localStride := by
    have hlocal_def : localStride = max 1 q := by
      simp [localStride, q, denom, ell, wordBits,
        sparseDenseFalseSelectLocalStride, sparseDenseFalseSelectEll]
    by_cases hq : q = 0
    · have hlocal_ge : 1 <= localStride := by
        rw [hlocal_def]
        exact Nat.le_max_left 1 q
      omega
    · have hq_pos : 0 < q := Nat.pos_of_ne_zero hq
      have hlocal : localStride = q := by
        rw [hlocal_def]
        exact Nat.max_eq_right (by omega)
      rw [hlocal]
      omega
  have hmul :
      (q + 1) * denom <= 2 * localStride * denom := by
    simpa [Nat.mul_assoc] using Nat.mul_le_mul_right denom hsucc_le
  have hle : wordBits <= (q + 1) * denom := by
    rw [Nat.add_mul, Nat.one_mul]
    exact Nat.le_of_lt hlt
  exact Nat.le_trans hle (by
    simpa [wordBits, ell, denom, localStride, q,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
    (shape : Cartesian.CartesianShape) {payload scale : Nat}
    (hmul :
      payload * sparseDenseFalseSelectWordBits shape <=
        scale * shape.bpCode.length *
          (sparseDenseFalseSelectEll shape *
            (sparseDenseFalseSelectEll shape *
              sparseDenseFalseSelectEll shape))) :
    payload <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        (2 * scale) shape.bpCode.length := by
  let n := shape.bpCode.length
  let wordBits := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  have hwordPos : 0 < wordBits := by
    simpa [wordBits] using sparseDenseFalseSelectWordBits_pos shape
  by_cases hn : n = 0
  · have hzeroMul : payload * wordBits = 0 := by
      have hle0 : payload * wordBits <= 0 := by
        simpa [n, wordBits, ell, ell3, hn,
          sparseDenseFalseSelectWordBits, sparseDenseFalseSelectEll] using hmul
      omega
    have hpayload : payload = 0 := by
      cases payload with
      | zero =>
          rfl
      | succ payload =>
          have hpos : 0 < (payload + 1) * wordBits :=
            Nat.mul_pos (by omega) hwordPos
          omega
    simp [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      hpayload, n, hn]
  · have hnPos : 0 < n := Nat.pos_of_ne_zero hn
    have hwordLeN : wordBits <= n := by
      simpa [wordBits, sparseDenseFalseSelectWordBits] using
        machineWordBits_le_self_of_pos hnPos
    let q := n / wordBits
    have hqPos : 0 < q := Nat.div_pos hwordLeN hwordPos
    have hnLt : n < q * wordBits + wordBits := by
      simpa [q] using Nat.lt_div_mul_add hwordPos (a := n)
    have hnLeQ :
        n <= 2 * q * wordBits := by
      have hsucc : q + 1 <= 2 * q := by omega
      have hleSucc : n <= (q + 1) * wordBits := by
        rw [Nat.add_mul, Nat.one_mul]
        exact Nat.le_of_lt hnLt
      have hmul := Nat.mul_le_mul_right wordBits hsucc
      exact Nat.le_trans hleSucc (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
    have hbudget :
        scale * n * ell3 <=
          (2 * scale) * (q * ell3) * wordBits := by
      have hscaled := Nat.mul_le_mul_left scale hnLeQ
      have hell := Nat.mul_le_mul_right ell3 hscaled
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hell
    have hpayloadWord :
        payload * wordBits <=
          (2 * scale) * (q * ell3) * wordBits := by
      exact Nat.le_trans
        (by
          simpa [n, wordBits, ell, ell3,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul)
        hbudget
    have hpayloadWordLeft :
        wordBits * payload <=
          wordBits * ((2 * scale) * (q * ell3)) := by
      simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
        hpayloadWord
    have hpayloadLe :
        payload <= (2 * scale) * (q * ell3) :=
      Nat.le_of_mul_le_mul_left hpayloadWordLeft hwordPos
    simpa [SuccinctSpace.logLogCubedSampledDirectoryOverhead,
      n, wordBits, ell, ell3, q, sparseDenseFalseSelectWordBits,
      sparseDenseFalseSelectEll, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hpayloadLe

theorem sparseDenseFalseSelectLocalStride_le_superStride
    (shape : Cartesian.CartesianShape) :
    sparseDenseFalseSelectLocalStride shape <=
      sparseDenseFalseSelectSuperStride shape := by
  let wordBits := sparseDenseFalseSelectWordBits shape
  have hword_pos : 0 < wordBits := by
    simpa [wordBits] using sparseDenseFalseSelectWordBits_pos shape
  have hlocal_le_word :
      sparseDenseFalseSelectLocalStride shape <= wordBits := by
    unfold sparseDenseFalseSelectLocalStride
    exact Nat.max_le.2
      ⟨by simpa [wordBits] using hword_pos,
        Nat.div_le_self wordBits
          (sparseDenseFalseSelectEll shape *
            sparseDenseFalseSelectEll shape)⟩
  have hword_le_square : wordBits <= wordBits * wordBits := by
    simpa using Nat.mul_le_mul_left wordBits (by omega : 1 <= wordBits)
  exact Nat.le_trans hlocal_le_word (by
    simpa [wordBits, sparseDenseFalseSelectSuperStride] using
      hword_le_square)

theorem builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRectangularFalseSelectLocalSlotCount shape *
        sparseDenseFalseSelectLocalStride shape <=
      10 * shape.bpCode.length := by
  let count := falseSelectOccurrenceCount shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  by_cases hcount : count = 0
  · have hsuperCount : superCount = 0 := by
      unfold superCount builtRectangularFalseSelectSuperSlotCount
        falseSelectCeilDiv
      rw [show falseSelectOccurrenceCount shape = 0 by
        simpa [count] using hcount]
      have hstride_pos : 0 < superStride := by
        simpa [superStride] using sparseDenseFalseSelectSuperStride_pos shape
      have hpred_lt : superStride - 1 < superStride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStride] using Nat.div_eq_of_lt hpred_lt
    simp [builtRectangularFalseSelectLocalSlotCount, superCount,
      hsuperCount]
  · have hcount_pos : 0 < count := Nat.pos_of_ne_zero hcount
    have hcountSize : count = shape.size := by
      simpa [count] using falseSelectOccurrenceCount_eq_size shape
    have hbpLen : shape.bpCode.length = 2 * shape.size := by
      exact Cartesian.CartesianShape.bpCode_length shape
    have hbp_pos : 0 < shape.bpCode.length := by
      omega
    have hcount_le_bp : count <= shape.bpCode.length := by
      omega
    have hsuperStride_le :
        superStride <= 4 * shape.bpCode.length := by
      have hsq :=
        machineWordBits_sq_le_four_mul_self_of_pos
          (n := shape.bpCode.length) hbp_pos
      simpa [superStride, sparseDenseFalseSelectSuperStride,
        sparseDenseFalseSelectWordBits] using hsq
    have hsuperCountMul :
        superCount * superStride <= count + superStride := by
      simpa [superCount, count, superStride,
        builtRectangularFalseSelectSuperSlotCount] using
        falseSelectCeilDiv_mul_le_add count superStride
    have hslotsMul :
        slots * localStride <= superStride + localStride := by
      simpa [slots, superStride, localStride,
        builtRectangularFalseSelectLocalSlotsPerSuper] using
        falseSelectLocalSlotsPerSuper_mul_localStride_le_add
          superStride localStride
    have hlocal_le_super :
        localStride <= superStride := by
      simpa [localStride, superStride] using
        sparseDenseFalseSelectLocalStride_le_superStride shape
    have hslotsMul' :
        slots * localStride <= 2 * superStride := by
      omega
    have hlocalPayload :
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape <=
          2 * (superCount * superStride) := by
      have hmul := Nat.mul_le_mul_left superCount hslotsMul'
      simpa [builtRectangularFalseSelectLocalSlotCount, superCount,
        slots, localStride, superStride, Nat.mul_assoc,
        Nat.mul_left_comm, Nat.mul_comm] using hmul
    have hsuperBudget :
        2 * (superCount * superStride) <=
          10 * shape.bpCode.length := by
      have hscaled := Nat.mul_le_mul_left 2 hsuperCountMul
      have hbudget : 2 * (count + superStride) <=
          10 * shape.bpCode.length := by
        omega
      exact Nat.le_trans (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          hscaled) hbudget
    exact Nat.le_trans hlocalPayload hsuperBudget

theorem falseSelectRelativeOffsetsOrZero_length
    (bits : List Bool) (baseOccurrence count endOccurrence
      basePosition : Nat) :
    (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
      endOccurrence basePosition).length = count := by
  simp [falseSelectRelativeOffsetsOrZero]

theorem builtRelativeSplitFalseSelectSparseExceptionFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).length =
      builtRectangularFalseSelectLocalSlotCount shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionFlagBits]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length =
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape <=
      builtRectangularFalseSelectLocalSlotCount shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_left _ _

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_count
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        shape <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
  exact Nat.min_le_right _ _

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_get?
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)[globalLocalSlot]? =
      some
        (builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot) := by
  simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
    List.getElem?_map, List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_prefix_eq
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot <=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
          shape) globalLocalSlot =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        globalLocalSlot := by
  have htake :
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
          shape) =
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).take
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape) := by
    apply List.ext_getElem?
    intro i
    by_cases hi :
        i <
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape
    · have hfull :
          i < builtRectangularFalseSelectLocalSlotCount shape := by
        exact Nat.lt_of_lt_of_le hi
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
            shape)
      simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
        builtRelativeSplitFalseSelectSparseExceptionFlagBits,
        List.getElem?_map, List.getElem?_range hfull, hi]
    · have heff :
          (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
            shape)[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits,
          Nat.le_of_not_gt hi]
      have htakeNone :
          ((builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).take
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
              shape))[i]? = none := by
        rw [List.getElem?_eq_none_iff]
        simp [List.length_take,
          builtRelativeSplitFalseSelectSparseExceptionFlagBits_length,
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
            shape,
          Nat.le_of_not_gt hi]
      rw [heff, htakeNone]
  rw [htake]
  exact
    RMQ.Succinct.rankPrefix_take_eq_of_le
      true (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (n :=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape)
      (limit := globalLocalSlot)
      (by
        rw [List.length_take]
        rw [builtRelativeSplitFalseSelectSparseExceptionFlagBits_length]
        exact Nat.le_min.mpr
          ⟨hslot,
            Nat.le_trans hslot
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
                shape)⟩)

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_length
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape globalLocalSlot).length =
      if builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot then
        sparseDenseFalseSelectLocalStride shape
      else
        0 := by
  by_cases h :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true
  · simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      h, falseSelectRelativeOffsetsOrZero_length]
  · have hfalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = false := by
      cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hfalse]

theorem builtRelativeSplitFalseSelectSuperIsLong_false_span_le
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    (hshort :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false) :
    builtRelativeSplitFalseSelectSuperSpan shape superSlot <=
      sparseDenseFalseSelectSuperLongSpan shape := by
  unfold builtRelativeSplitFalseSelectSuperIsLong at hshort
  by_cases hlt :
      sparseDenseFalseSelectSuperLongSpan shape <
        builtRelativeSplitFalseSelectSuperSpan shape superSlot
  · simp [hlt] at hshort
  · omega

theorem builtRelativeSplitFalseSelectLocalIsSparseException_true_short
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true) :
    builtRelativeSplitFalseSelectSuperIsLong shape
        (builtRelativeSplitFalseSelectLocalSuperSlot
          shape globalLocalSlot) = false /\
      sparseDenseFalseSelectWordBits shape <
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot := by
  unfold builtRelativeSplitFalseSelectLocalIsSparseException at hflag
  cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape
        (builtRelativeSplitFalseSelectLocalSuperSlot
          shape globalLocalSlot)
  · simp [hlong] at hflag
    exact ⟨rfl, hflag⟩
  · simp [hlong] at hflag

theorem falseSelect_occurrence_lt_count_of_select
    (shape : Cartesian.CartesianShape) {occurrence pos : Nat}
    (hselect :
      RMQ.Succinct.select false shape.bpCode occurrence = some pos) :
    occurrence < falseSelectOccurrenceCount shape := by
  have hsucc := rankPrefix_succ_of_select hselect
  have hpos : pos < shape.bpCode.length :=
    RMQ.Succinct.select_bounds hselect
  have hmono :
      RMQ.Succinct.rankPrefix false shape.bpCode (pos + 1) <=
        RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length :=
    RMQ.Succinct.rankPrefix_mono_limit false shape.bpCode
      (Nat.succ_le_of_lt hpos)
  rw [hsucc] at hmono
  have hcount : occurrence + 1 <= falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hmono
  omega

theorem falseSelect_exists_of_lt_occurrence_count
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hocc : occurrence < falseSelectOccurrenceCount shape) :
    exists pos,
      RMQ.Succinct.select false shape.bpCode occurrence = some pos := by
  simpa [falseSelectOccurrenceCount] using
    select_exists_of_lt_rankPrefix
      (target := false) (bits := shape.bpCode)
      (occurrence := occurrence) (limit := shape.bpCode.length)
      hocc

theorem builtRelativeSplitFalseSelectPosition_eq_of_select
    (shape : Cartesian.CartesianShape) {occurrence pos : Nat}
    (hselect :
      RMQ.Succinct.select false shape.bpCode occurrence = some pos) :
    builtRelativeSplitFalseSelectPosition shape occurrence = pos := by
  simp [builtRelativeSplitFalseSelectPosition, hselect]

theorem builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hcount : falseSelectOccurrenceCount shape <= occurrence) :
    builtRelativeSplitFalseSelectPosition shape occurrence =
      shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectPosition
  have hnone :
      RMQ.Succinct.select false shape.bpCode occurrence = none :=
    select_none_of_rankPrefix_length_le (target := false)
      (bits := shape.bpCode) (occurrence := occurrence)
      (by simpa [falseSelectOccurrenceCount] using hcount)
  simp [hnone]

theorem builtRelativeSplitFalseSelectPosition_mono
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hle : lo <= hi) :
    builtRelativeSplitFalseSelectPosition shape lo <=
      builtRelativeSplitFalseSelectPosition shape hi := by
  by_cases hhi : hi < falseSelectOccurrenceCount shape
  · have hlo : lo < falseSelectOccurrenceCount shape := by omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hlo with ⟨loPos, hloSelect⟩
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hhi with ⟨hiPos, hhiSelect⟩
    have hmono :
        loPos <= hiPos :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := lo) (hi := hi) hle hloSelect hhiSelect
    rw [builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hloSelect]
    rw [builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hhiSelect]
    exact hmono
  · have hhiCount : falseSelectOccurrenceCount shape <= hi := by
      omega
    rw [builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hhiCount]
    by_cases hlo : lo < falseSelectOccurrenceCount shape
    · rcases falseSelect_exists_of_lt_occurrence_count
        shape hlo with ⟨loPos, hloSelect⟩
      rw [builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hloSelect]
      exact Nat.le_of_lt (RMQ.Succinct.select_bounds hloSelect)
    · have hloCount : falseSelectOccurrenceCount shape <= lo := by
        omega
      rw [builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
        shape hloCount]
      exact Nat.le_refl _

theorem falseSelectOccurrenceCount_pos_of_rectangular_local_slot
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    0 < falseSelectOccurrenceCount shape := by
  by_cases hpos : 0 < falseSelectOccurrenceCount shape
  · exact hpos
  · have hcountZero : falseSelectOccurrenceCount shape = 0 := by omega
    have hsuperZero :
        builtRectangularFalseSelectSuperSlotCount shape = 0 := by
      unfold builtRectangularFalseSelectSuperSlotCount falseSelectCeilDiv
      rw [hcountZero]
      have hstride := sparseDenseFalseSelectSuperStride_pos shape
      have hlt :
          sparseDenseFalseSelectSuperStride shape - 1 <
            sparseDenseFalseSelectSuperStride shape :=
        Nat.pred_lt (Nat.ne_of_gt hstride)
      simpa using Nat.div_eq_of_lt hlt
    have hlocalZero :
        builtRectangularFalseSelectLocalSlotCount shape = 0 := by
      simp [builtRectangularFalseSelectLocalSlotCount, hsuperZero]
    omega

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.le_trans (Nat.min_le_right _ _) (by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    exact Nat.min_le_right _ _)

theorem builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_pos
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    0 <
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot := by
  have hcountPos :=
    falseSelectOccurrenceCount_pos_of_rectangular_local_slot
      shape hslot
  have hlocalPos := sparseDenseFalseSelectLocalStride_pos shape
  have hsuperStridePos := sparseDenseFalseSelectSuperStride_pos shape
  have hsuperEndPos :
      0 <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot) := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨by omega, hcountPos⟩
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEndPos⟩

theorem builtRelativeSplitFalseSelectShortSuperLocalBase_lt_end_of_base_lt_count
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <
        falseSelectOccurrenceCount shape) :
    builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot <
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
        shape globalLocalSlot := by
  have hlocalPos := sparseDenseFalseSelectLocalStride_pos shape
  have hboundary :=
    builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
      shape globalLocalSlot
  have hsuperEnd :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot) := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
      builtRelativeSplitFalseSelectLocalSuperSlot
    exact Nat.lt_min.mpr ⟨by
      simpa using hboundary, hbaseCount⟩
  unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hsuperEnd⟩

theorem builtRelativeSplitFalseSelectShortSuperLocalSpan_le_next_gap
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpan
        shape globalLocalSlot <=
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape (globalLocalSlot + 1)) -
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot) := by
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let endOcc :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let next :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape (globalLocalSlot + 1)
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  let nextPos := builtRelativeSplitFalseSelectPosition shape next
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
        shape globalLocalSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_pos
        shape hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_next_base
        shape globalLocalSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using
      builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
        shape globalLocalSlot
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hlastBounds : lastWitness < shape.bpCode.length :=
    RMQ.Succinct.select_bounds hlastSelect
  by_cases hbaseCount : base < falseSelectOccurrenceCount shape
  · have hbaseEnd :
        base < endOcc := by
      simpa [base, endOcc] using
        builtRelativeSplitFalseSelectShortSuperLocalBase_lt_end_of_base_lt_count
          shape globalLocalSlot hbaseCount
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
    have hbaseEq : basePos = baseWitness := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_of_select
          shape hbaseSelect
    have hbaseLast :
        baseWitness <= lastWitness := by
      have hmono :=
        select_index_mono (target := false) (bits := shape.bpCode)
          (lo := base) (hi := endOcc - 1)
          (posLo := baseWitness) (posHi := lastWitness)
          (by omega) hbaseSelect hlastSelect
      exact hmono
    have hlastNext : lastWitness + 1 <= nextPos := by
      by_cases hnextCount : next < falseSelectOccurrenceCount shape
      · rcases falseSelect_exists_of_lt_occurrence_count
          shape hnextCount with ⟨nextWitness, hnextSelect⟩
        have hstrict :
            lastWitness < nextWitness :=
          select_index_strict_mono (target := false)
            (bits := shape.bpCode)
            (lo := endOcc - 1) (hi := next)
            (posLo := lastWitness) (posHi := nextWitness)
            (by omega) hlastSelect hnextSelect
        have hnextEq : nextPos = nextWitness := by
          simpa [nextPos] using
            builtRelativeSplitFalseSelectPosition_eq_of_select
              shape hnextSelect
        rw [hnextEq]
        omega
      · have hnextCountLe :
            falseSelectOccurrenceCount shape <= next := by
          omega
        have hnextEq :
            nextPos = shape.bpCode.length := by
          simpa [nextPos] using
            builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
              shape hnextCountLe
        rw [hnextEq]
        omega
    unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq]
    omega
  · have hbaseCountLe :
        falseSelectOccurrenceCount shape <= base := by
      omega
    have hnextCountLe :
        falseSelectOccurrenceCount shape <= next := by
      exact Nat.le_trans hbaseCountLe hbaseNext
    have hbaseEq :
        basePos = shape.bpCode.length := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
          shape hbaseCountLe
    have hnextEq :
        nextPos = shape.bpCode.length := by
      simpa [nextPos] using
        builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
          shape hnextCountLe
    unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
    change lastPos + 1 - basePos <= nextPos - basePos
    rw [hlastEq, hbaseEq, hnextEq]
    omega

theorem builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    {localBaseOccurrence q pos : Nat}
    (hshort :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false)
    (hsuperBase :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
        localBaseOccurrence)
    (hlocalBase : localBaseOccurrence <= q)
    (hqEnd :
      q <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    pos -
        builtRelativeSplitFalseSelectPosition
          shape localBaseOccurrence <
      sparseDenseFalseSelectSuperLongSpan shape := by
  let superBase :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let superEnd :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  have hqCount : q < falseSelectOccurrenceCount shape :=
    falseSelect_occurrence_lt_count_of_select shape hselect
  have hlocalCount : localBaseOccurrence < falseSelectOccurrenceCount shape := by
    omega
  have hsuperCount : superBase < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlocalCount with
    ⟨localBasePos, hlocalSelect⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hsuperCount with
    ⟨superBasePos, hsuperSelect⟩
  have hsuperEndLeCount :
      superEnd <= falseSelectOccurrenceCount shape := by
    exact Nat.min_le_right
      (superBase + sparseDenseFalseSelectSuperStride shape)
      (falseSelectOccurrenceCount shape)
  have hsuperEndPos : 0 < superEnd := by
    omega
  have hlastCount : superEnd - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with
    ⟨lastPos, hlastSelect⟩
  have hsuperBasePos_le_localBasePos :
      superBasePos <= localBasePos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := superBase) (hi := localBaseOccurrence)
      (posLo := superBasePos) (posHi := localBasePos)
      (by simpa [superBase] using hsuperBase)
      hsuperSelect hlocalSelect
  have hlocalBasePos_le_pos :
      localBasePos <= pos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := localBaseOccurrence) (hi := q)
      (posLo := localBasePos) (posHi := pos)
      hlocalBase hlocalSelect hselect
  have hqLeLast : q <= superEnd - 1 := by
    omega
  have hpos_le_last :
      pos <= lastPos := by
    exact select_index_mono
      (target := false) (bits := shape.bpCode)
      (lo := q) (hi := superEnd - 1)
      (posLo := pos) (posHi := lastPos)
      hqLeLast hselect hlastSelect
  have hspanLe :=
    builtRelativeSplitFalseSelectSuperIsLong_false_span_le
      shape superSlot hshort
  have hsuperSelect' :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) =
        some superBasePos := by
    simpa [superBase] using hsuperSelect
  have hlastSelect' :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperEndOccurrence
            shape superSlot - 1) =
        some lastPos := by
    simpa [superEnd] using hlastSelect
  have hsuperSelectRaw :
      RMQ.Succinct.select false shape.bpCode
          (superSlot * sparseDenseFalseSelectSuperStride shape) =
        some superBasePos := by
    simpa [builtRelativeSplitFalseSelectSuperBaseOccurrence] using
      hsuperSelect'
  have hlastSelectRaw :
      RMQ.Succinct.select false shape.bpCode
          ((superSlot * sparseDenseFalseSelectSuperStride shape +
              sparseDenseFalseSelectSuperStride shape).min
            (falseSelectOccurrenceCount shape) -
            1) =
        some lastPos := by
    simpa [builtRelativeSplitFalseSelectSuperEndOccurrence,
      builtRelativeSplitFalseSelectSuperBaseOccurrence] using
      hlastSelect'
  have hspanEq :
      builtRelativeSplitFalseSelectSuperSpan shape superSlot =
        lastPos + 1 - superBasePos := by
    simp [builtRelativeSplitFalseSelectSuperSpan,
      builtRelativeSplitFalseSelectSuperBaseOccurrence,
      builtRelativeSplitFalseSelectSuperEndOccurrence,
      builtRelativeSplitFalseSelectPosition, hsuperSelectRaw,
      hlastSelectRaw]
  rw [hspanEq] at hspanLe
  have hlocalPosEq :
      builtRelativeSplitFalseSelectPosition
        shape localBaseOccurrence = localBasePos :=
    builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hlocalSelect
  rw [hlocalPosEq]
  have hoffLt :
      pos - localBasePos < lastPos + 1 - superBasePos := by
    omega
  omega

theorem falseSelectRelativeOffsetsOrZero_mem_cases
    {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition entry : Nat}
    (hmem :
      List.Mem entry
        (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
          endOccurrence basePosition)) :
    entry = 0 \/
      exists offset pos,
        offset < count /\
          baseOccurrence + offset < endOccurrence /\
          RMQ.Succinct.select false bits
            (baseOccurrence + offset) = some pos /\
          entry = pos - basePosition := by
  unfold falseSelectRelativeOffsetsOrZero at hmem
  rcases List.mem_map.mp hmem with ⟨offset, hoffMem, hentry⟩
  have hoff : offset < count := by
    simpa using (List.mem_range.mp hoffMem)
  by_cases hlt : baseOccurrence + offset < endOccurrence
  · cases hselect :
      RMQ.Succinct.select false bits
        (baseOccurrence + offset) with
    | none =>
        left
        simpa [hlt, hselect] using hentry.symm
    | some pos =>
        right
        refine ⟨offset, pos, hoff, hlt, hselect, ?_⟩
        simpa [hlt, hselect] using hentry.symm
  · left
    simpa [hlt] using hentry.symm

theorem falseSelectRelativeOffsetsOrZero_lookup_exact
    {bits : List Bool} {baseOccurrence count endOccurrence
      basePosition localOccurrence pos : Nat}
    (hocc : localOccurrence < count)
    (hend : baseOccurrence + localOccurrence < endOccurrence)
    (hselect :
      RMQ.Succinct.select false bits
        (baseOccurrence + localOccurrence) = some pos) :
    (falseSelectRelativeOffsetsOrZero bits baseOccurrence count
      endOccurrence basePosition)[localOccurrence]? =
      some (pos - basePosition) := by
  simp [falseSelectRelativeOffsetsOrZero, List.getElem?_map,
    List.getElem?_range hocc, hend, hselect]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_mem_lt_width
    (shape : Cartesian.CartesianShape) {globalLocalSlot entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape globalLocalSlot)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
          shape := by
  by_cases hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true
  · let superSlot :=
      builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
    let localBase :=
      builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot
    let localBasePosition :=
      builtRelativeSplitFalseSelectPosition shape localBase
    have hshort :=
      (builtRelativeSplitFalseSelectLocalIsSparseException_true_short
        shape globalLocalSlot hflag).1
    have hmemOffsets :
        List.Mem entry
          (falseSelectRelativeOffsetsOrZero shape.bpCode localBase
            (sparseDenseFalseSelectLocalStride shape)
            (builtRelativeSplitFalseSelectSuperEndOccurrence
              shape superSlot)
            localBasePosition) := by
      simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
        hflag, superSlot, localBase, localBasePosition] using hmem
    rcases falseSelectRelativeOffsetsOrZero_mem_cases
        hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with
        ⟨offset, pos, _hoff, hqEnd, hselect, hentry⟩
      have hsuperBase :
          builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
            localBase := by
        simp [superSlot, localBase,
          builtRelativeSplitFalseSelectSuperBaseOccurrence,
          builtRelativeSplitFalseSelectLocalSuperSlot,
          builtRectangularFalseSelectLocalBaseOccurrence]
      have hoffSuper :
          pos - localBasePosition <
            sparseDenseFalseSelectSuperLongSpan shape := by
        simpa [localBase, localBasePosition, superSlot] using
          builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
            shape superSlot hshort hsuperBase
            (by omega)
            hqEnd hselect
      have hposLen : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < shape.bpCode.length := by
        rw [hentry]
        omega
      have hentrySuper :
          entry < sparseDenseFalseSelectSuperLongSpan shape := by
        rw [hentry]
        exact hoffSuper
      have hentryMin :
          entry <
            Nat.min shape.bpCode.length
              (sparseDenseFalseSelectSuperLongSpan shape) := by
        exact Nat.lt_min.mpr ⟨hentryLen, hentrySuper⟩
      exact Nat.lt_trans hentryMin
        (by
          simpa [builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
            SuccinctRankProposal.machineWordBits] using
            (Nat.lt_log2_self
              (n :=
                Nat.min shape.bpCode.length
                  (sparseDenseFalseSelectSuperLongSpan shape))))
  · have hfalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hfalse] at hmem
    cases hmem

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_mem_lt_width
    (shape : Cartesian.CartesianShape) {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth
          shape := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨globalLocalSlot, _hslot, hentry⟩
  exact
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_mem_lt_width
      shape hentry

def builtRelativeSplitFalseSelectSparseExceptionRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)
      (builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)
    (builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_mem_lt_width
          shape hmem)

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_profile
    (shape : Cartesian.CartesianShape) :
    let table :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
    table.payload.length =
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape).length *
          builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase =
          (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
            shape)[i]?) /\
      forall {word : List Bool},
        List.Mem word table.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let table :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
  constructor
  · exact table.payload_length_eq
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i, table.readCosted_erase i⟩
    · intro word hmem
      rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
      have hget : table.store.words[i]? = some word := by
        simpa [Array.getElem?_toList] using hgetList
      rw [table.read_word_length_of_some hget]
      exact
        builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine
          shape

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
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitFalseSelectSparseFlagBits shape).length

def builtRelativeSplitFalseSelectFlagRankBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectFlagRankWordSize shape

def builtRelativeSplitFalseSelectFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
      builtRelativeSplitFalseSelectFlagRankWordSize shape)

theorem builtRelativeSplitFalseSelectFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectFlagRankWordSize shape := by
  simp [builtRelativeSplitFalseSelectFlagRankWordSize,
    SuccinctRankProposal.machineWordBits_pos]

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
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n := (builtRelativeSplitFalseSelectSparseFlagBits shape).length))

theorem builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
        builtRelativeSplitFalseSelectFlagRankWordSize shape <
      2 ^ builtRelativeSplitFalseSelectFlagRankBlockWidth shape := by
  simpa [builtRelativeSplitFalseSelectFlagRankBlockWidth,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n :=
        builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape *
          builtRelativeSplitFalseSelectFlagRankWordSize shape))

def builtRelativeSplitFalseSelectFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectSparseFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectFlagRankBlockWidth shape)
      (builtRelativeSplitFalseSelectFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseFlagBits shape)
      (builtRelativeSplitFalseSelectFlagRankSuperOverhead shape)
      (builtRelativeSplitFalseSelectFlagRankBlockOverhead shape)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
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
        SuccinctRankProposal.machineWordBits
          (builtRelativeSplitFalseSelectSparseFlagBits shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits
              (builtRelativeSplitFalseSelectSparseFlagBits shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseFlagBits shape) pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
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
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape).length

def builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize shape

def builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
        shape *
      builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize shape)

theorem builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 <
      builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
        shape := by
  simp [builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize,
    SuccinctRankProposal.machineWordBits_pos]

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
    SuccinctRankProposal.machineWordBits] using
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
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n :=
        builtRelativeSplitFalseSelectSparseExceptionFlagRankBlocksPerSuper
            shape *
          builtRelativeSplitFalseSelectSparseExceptionFlagRankWordSize
            shape))

def builtRelativeSplitFalseSelectSparseExceptionFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
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
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
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
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionFlagRankBlockOverhead
        shape)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
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
        SuccinctRankProposal.machineWordBits
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits
            shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseExceptionFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape) pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
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
  SuccinctRankProposal.machineWordBits
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
    SuccinctRankProposal.machineWordBits_pos]

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
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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
    SuccinctRankProposal.machineWordBits] using
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
  (SuccinctRankProposal.canonicalSuperRankSampleTables
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
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
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
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
        shape)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape)
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
      shape)
    (by
      simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
        SuccinctRankProposal.machineWordBits])
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
        SuccinctRankProposal.machineWordBits shape.bpCode.length /\
      data.superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length /\
      data.blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
                shape) pos := by
  have hprofile :=
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
        shape)
      (by
        simp [builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize,
          SuccinctRankProposal.machineWordBits])
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
        SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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

theorem natList_sum_append (xs ys : List Nat) :
    (xs ++ ys).sum = xs.sum + ys.sum := by
  induction xs with
  | nil =>
      simp
  | cons x xs ih =>
      simp [ih, Nat.add_assoc]

def builtRelativeSplitFalseSelectShortSuperLocalSpanSum
    (shape : Cartesian.CartesianShape) (slotCount : Nat) : Nat :=
  (List.range slotCount).map
    (builtRelativeSplitFalseSelectShortSuperLocalSpan shape)
    |>.sum

theorem builtRelativeSplitFalseSelectShortSuperLocalSpanSum_prefix_le_position
    (shape : Cartesian.CartesianShape) {slotCount : Nat}
    (hslotCount :
      slotCount <= builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape slotCount <=
      builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape slotCount) := by
  induction slotCount with
  | zero =>
      simp [builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
  | succ slotCount ih =>
      have hprefix :
          slotCount <= builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have hslot :
          slotCount < builtRectangularFalseSelectLocalSlotCount shape := by
        omega
      have ih' := ih hprefix
      let prefixSum :=
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum
          shape slotCount
      let span :=
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape slotCount
      let basePos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape slotCount)
      let nextPos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        simpa [span, basePos, nextPos] using
          builtRelativeSplitFalseSelectShortSuperLocalSpan_le_next_gap
            shape hslot
      have hbaseNext :
          builtRectangularFalseSelectLocalBaseOccurrence
              shape slotCount <=
            builtRectangularFalseSelectLocalBaseOccurrence
              shape (slotCount + 1) :=
        builtRectangularFalseSelectLocalBaseOccurrence_le_next_base
          shape slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using
          builtRelativeSplitFalseSelectPosition_mono shape hbaseNext
      unfold builtRelativeSplitFalseSelectShortSuperLocalSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem falseSelectCeilDiv_mul_ge_of_pos
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride := by
  unfold falseSelectCeilDiv
  cases n with
  | zero =>
      simp
  | succ n =>
      have hleStride : stride <= n + 1 + stride - 1 := by
        omega
      have hlt :
          n + 1 + stride - 1 - stride <
          (n + 1 + stride - 1) / stride * stride :=
        Nat.lt_div_mul_self hstride hleStride
      omega

theorem falseSelectCeilDiv_slot_mul_lt
    {n stride slot : Nat} (hstride : 0 < stride)
    (hslot : slot < falseSelectCeilDiv n stride) :
    slot * stride < n := by
  unfold falseSelectCeilDiv at hslot
  have hsucc :
      slot + 1 <= (n + stride - 1) / stride := by
    omega
  have hmul :
      (slot + 1) * stride <= n + stride - 1 := by
    exact (Nat.le_div_iff_mul_le hstride).mp hsucc
  cases n with
  | zero =>
      have hstrideLe :
          stride <= (slot + 1) * stride := by
        have hslot : 1 <= slot + 1 := by omega
        have hmulSlot := Nat.mul_le_mul_right stride hslot
        simpa [Nat.mul_comm] using hmulSlot
      omega
  | succ n =>
      have hleft :
          (slot + 1) * stride = slot * stride + stride := by
        simp [Nat.add_mul, Nat.one_mul]
      have hright :
          n + 1 + stride - 1 = n + stride := by
        omega
      rw [hleft, hright] at hmul
      omega

theorem builtRectangularFalseSelectFinalLocalBaseOccurrence
    (shape : Cartesian.CartesianShape) :
    builtRectangularFalseSelectLocalBaseOccurrence shape
        (builtRectangularFalseSelectLocalSlotCount shape) =
      builtRectangularFalseSelectSuperSlotCount shape *
        sparseDenseFalseSelectSuperStride shape := by
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superCount := builtRectangularFalseSelectSuperSlotCount shape
  have hslots : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hdiv :
      (builtRectangularFalseSelectLocalSlotCount shape) / slots =
        superCount := by
    simp [builtRectangularFalseSelectLocalSlotCount, superCount, slots,
      Nat.mul_div_left, hslots]
  have hmod :
      (builtRectangularFalseSelectLocalSlotCount shape) % slots = 0 := by
    simp [builtRectangularFalseSelectLocalSlotCount, slots,
      Nat.mul_mod_left]
  rw [builtRectangularFalseSelectLocalBaseOccurrence_mod]
  change
    ((builtRectangularFalseSelectLocalSlotCount shape) / slots) *
        sparseDenseFalseSelectSuperStride shape +
      ((builtRectangularFalseSelectLocalSlotCount shape) % slots) *
        sparseDenseFalseSelectLocalStride shape =
      superCount * sparseDenseFalseSelectSuperStride shape
  rw [hdiv, hmod]
  simp [superCount]

theorem builtRelativeSplitFalseSelectShortSuperLocalSpanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
        (builtRectangularFalseSelectLocalSlotCount shape) <=
      shape.bpCode.length := by
  have hprefix :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum_prefix_le_position
      shape (Nat.le_refl _)
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape)
  have hbase :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectLocalBaseOccurrence shape
          (builtRectangularFalseSelectLocalSlotCount shape) := by
    rw [builtRectangularFalseSelectFinalLocalBaseOccurrence]
    exact hocc
  have hpos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence shape
            (builtRectangularFalseSelectLocalSlotCount shape)) =
        shape.bpCode.length :=
    builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hbase
  rwa [hpos] at hprefix

theorem builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
      falseSelectOccurrenceCount shape := by
  simpa [builtRectangularFalseSelectSuperSlotCount,
    builtRelativeSplitFalseSelectSuperBaseOccurrence] using
    falseSelectCeilDiv_slot_mul_lt
      (n := falseSelectOccurrenceCount shape)
      (stride := sparseDenseFalseSelectSuperStride shape)
      (slot := superSlot)
      (sparseDenseFalseSelectSuperStride_pos shape) hslot

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_le_count
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot <=
      falseSelectOccurrenceCount shape := by
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.min_le_right _ _

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_pos
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    0 < builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
  have hbaseCount :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
      shape hslot
  have hstride := sparseDenseFalseSelectSuperStride_pos shape
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, by omega⟩

theorem builtRelativeSplitFalseSelectSuperEndOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot <=
      builtRelativeSplitFalseSelectSuperBaseOccurrence
        shape (superSlot + 1) := by
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    builtRelativeSplitFalseSelectSuperBaseOccurrence
  have hleft :
      Nat.min
          (superSlot * sparseDenseFalseSelectSuperStride shape +
            sparseDenseFalseSelectSuperStride shape)
          (falseSelectOccurrenceCount shape) <=
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape :=
    Nat.min_le_left _ _
  simpa [Nat.add_mul, Nat.one_mul, Nat.add_assoc, Nat.add_comm,
    Nat.add_left_comm] using hleft

theorem builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <=
      builtRelativeSplitFalseSelectSuperBaseOccurrence
        shape (superSlot + 1) := by
  unfold builtRelativeSplitFalseSelectSuperBaseOccurrence
  exact
    Nat.mul_le_mul_right
      (sparseDenseFalseSelectSuperStride shape)
      (Nat.le_succ superSlot)

theorem builtRelativeSplitFalseSelectSuperBase_lt_end_of_base_lt_count
    (shape : Cartesian.CartesianShape) (superSlot : Nat)
    (hbaseCount :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
        falseSelectOccurrenceCount shape) :
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
      builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
  have hstride := sparseDenseFalseSelectSuperStride_pos shape
  unfold builtRelativeSplitFalseSelectSuperEndOccurrence
  exact Nat.lt_min.mpr ⟨by omega, hbaseCount⟩

theorem builtRelativeSplitFalseSelectSuperSpan_le_next_gap
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectSuperSpan shape superSlot <=
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape (superSlot + 1)) -
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) := by
  let base :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let endOcc :=
    builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot
  let next :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape (superSlot + 1)
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  let nextPos := builtRelativeSplitFalseSelectPosition shape next
  have hbaseCount : base < falseSelectOccurrenceCount shape := by
    simpa [base] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
        shape hslot
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_le_count
        shape superSlot
  have hendPos : 0 < endOcc := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_pos
        shape hslot
  have hendNext : endOcc <= next := by
    simpa [endOcc, next] using
      builtRelativeSplitFalseSelectSuperEndOccurrence_le_next_base
        shape superSlot
  have hbaseNext : base <= next := by
    simpa [base, next] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
        shape superSlot
  have hbaseEnd : base < endOcc := by
    simpa [base, endOcc] using
      builtRelativeSplitFalseSelectSuperBase_lt_end_of_base_lt_count
        shape superSlot hbaseCount
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hbaseEq : basePos = baseWitness := by
    simpa [basePos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
  have hlastEq : lastPos = lastWitness := by
    simpa [lastPos] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hbaseLast :
      baseWitness <= lastWitness := by
    exact
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := base) (hi := endOcc - 1)
        (posLo := baseWitness) (posHi := lastWitness)
        (by omega) hbaseSelect hlastSelect
  have hlastNext : lastWitness + 1 <= nextPos := by
    by_cases hnextCount : next < falseSelectOccurrenceCount shape
    · rcases falseSelect_exists_of_lt_occurrence_count
        shape hnextCount with ⟨nextWitness, hnextSelect⟩
      have hstrict :
          lastWitness < nextWitness :=
        select_index_strict_mono (target := false)
          (bits := shape.bpCode)
          (lo := endOcc - 1) (hi := next)
          (posLo := lastWitness) (posHi := nextWitness)
          (by omega) hlastSelect hnextSelect
      have hnextEq : nextPos = nextWitness := by
        simpa [nextPos] using
          builtRelativeSplitFalseSelectPosition_eq_of_select
            shape hnextSelect
      rw [hnextEq]
      omega
    · have hnextCountLe :
          falseSelectOccurrenceCount shape <= next := by
        omega
      have hnextEq :
          nextPos = shape.bpCode.length := by
        simpa [nextPos] using
          builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
            shape hnextCountLe
      have hlastBounds : lastWitness < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hlastSelect
      rw [hnextEq]
      omega
  unfold builtRelativeSplitFalseSelectSuperSpan
  change lastPos + 1 - basePos <= nextPos - basePos
  rw [hlastEq, hbaseEq]
  omega

theorem builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectLocalSlotCount shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape) n *
        sparseDenseFalseSelectWordBits shape <=
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix,
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
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
      have ih' := ih hn'
      rw [hrank]
      unfold builtRelativeSplitFalseSelectShortSuperLocalSpanSum
      rw [List.range_succ]
      rw [List.map_append, natList_sum_append]
      simp
      by_cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            true
      · have hspanLt :=
          (builtRelativeSplitFalseSelectLocalIsSparseException_true_short
            shape n hflag).2
        have hwordLe :
            sparseDenseFalseSelectWordBits shape <=
              builtRelativeSplitFalseSelectShortSuperLocalSpan
                shape n := by
          omega
        have hcalc :
            (RMQ.Succinct.rankPrefix true
                  (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                    shape) n +
                1) *
                sparseDenseFalseSelectWordBits shape <=
              builtRelativeSplitFalseSelectShortSuperLocalSpanSum
                  shape n +
                builtRelativeSplitFalseSelectShortSuperLocalSpan
                  shape n := by
          rw [Nat.add_mul]
          simp
          omega
        simpa [hflag, builtRelativeSplitFalseSelectShortSuperLocalSpanSum,
          Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc]
          using hcalc
      · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparseException shape n =
            false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparseException shape n
          · rfl
          · contradiction
        simpa [hfalse, builtRelativeSplitFalseSelectShortSuperLocalSpanSum]
          using
          Nat.le_trans ih'
            (Nat.le_add_right
              (builtRelativeSplitFalseSelectShortSuperLocalSpanSum
                shape n)
              (builtRelativeSplitFalseSelectShortSuperLocalSpan
                shape n))

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_of_span_product_bound
    (shape : Cartesian.CartesianShape) {budget : Nat}
    (hspanProduct :
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) *
          sparseDenseFalseSelectLocalStride shape *
          builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape <=
        sparseDenseFalseSelectWordBits shape * budget) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length <= budget := by
  let count :=
    RMQ.Succinct.rankPrefix true
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRectangularFalseSelectLocalSlotCount shape)
  let spanSum :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
      (builtRectangularFalseSelectLocalSlotCount shape)
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  have hcountWord :
      count * wordBits <= spanSum := by
    simpa [count, spanSum, wordBits] using
      builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
        shape (Nat.le_refl _)
  have hscaled :
      (count * wordBits) * (localStride * relativeWidth) <=
        spanSum * (localStride * relativeWidth) :=
    Nat.mul_le_mul_right (localStride * relativeWidth) hcountWord
  have hspan' :
      spanSum * (localStride * relativeWidth) <= budget * wordBits := by
    simpa [spanSum, localStride, relativeWidth, wordBits, Nat.mul_assoc,
      Nat.mul_left_comm, Nat.mul_comm] using hspanProduct
  have hpayloadMul :
      (count * localStride * relativeWidth) * wordBits <=
        budget * wordBits := by
    have h := Nat.le_trans hscaled hspan'
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
  have hpayloadMulLeft :
      wordBits * (count * localStride * relativeWidth) <=
        wordBits * budget := by
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul
  have hwordBits : 0 < wordBits := by
    simp [wordBits, sparseDenseFalseSelectWordBits,
      SuccinctRankProposal.machineWordBits_pos]
  apply
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_of_count_bound
      shape
  exact Nat.le_of_mul_le_mul_left hpayloadMulLeft hwordBits

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length *
        sparseDenseFalseSelectEll shape <=
      512 *
        builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) := by
  let count :=
    RMQ.Succinct.rankPrefix true
      (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
      (builtRectangularFalseSelectLocalSlotCount shape)
  let localStride := sparseDenseFalseSelectLocalStride shape
  let relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  let ell := sparseDenseFalseSelectEll shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let spanSum :=
    builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
      (builtRectangularFalseSelectLocalSlotCount shape)
  have hpayload :
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
          shape).payload.length =
        count * localStride * relativeWidth := by
    simpa [count, localStride, relativeWidth] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_length
        shape
  have hcodec :
      localStride * relativeWidth * ell <= 512 * wordBits := by
    simpa [localStride, relativeWidth, ell, wordBits] using
      builtRelativeSplitFalseSelectSparseException_localStride_mul_width_mul_ell_le_const_wordBits
        shape
  have hpayloadEll :
      count * localStride * relativeWidth * ell <=
        count * (512 * wordBits) := by
    have hmul := Nat.mul_le_mul_left count hcodec
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hcountWord :
      count * wordBits <= spanSum := by
    simpa [count, wordBits, spanSum] using
      builtRelativeSplitFalseSelectSparseExceptionCount_wordBits_le_spanSum
        shape (Nat.le_refl _)
  have hcountScaled :
      count * (512 * wordBits) <= 512 * spanSum := by
    have hmul := Nat.mul_le_mul_left 512 hcountWord
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  rw [hpayload]
  exact Nat.le_trans hpayloadEll hcountScaled

def sparseExceptionRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 512 (2 * n) + 512

theorem sparseExceptionRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear sparseExceptionRelativeTableOverhead := by
  unfold sparseExceptionRelativeTableOverhead
  exact
    ((SuccinctSpace.idDivLogLogOverhead_littleO 512).comp_two_mul_arg).add_const
      512

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (hspan :
      builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
          (builtRectangularFalseSelectLocalSlotCount shape) <=
        shape.bpCode.length) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      sparseExceptionRelativeTableOverhead shape.size := by
  let payload :=
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).payload.length
  let ell := sparseDenseFalseSelectEll shape
  let n := shape.bpCode.length
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hpayloadEll :
      payload * ell <= 512 * n := by
    have hscaled :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_mul_ell_le_const_spanSum
        shape
    have hspanScaled :
        512 *
            builtRelativeSplitFalseSelectShortSuperLocalSpanSum shape
              (builtRectangularFalseSelectLocalSlotCount shape) <=
          512 * n := by
      exact Nat.mul_le_mul_left 512 (by simpa [n] using hspan)
    exact Nat.le_trans (by simpa [payload, ell] using hscaled) hspanScaled
  let overheadLen := 512 * (n / ell) + 512
  have hn_lt :
      n < n / ell * ell + ell :=
    Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict :
      512 * n < overheadLen * ell := by
    have hmul :=
      Nat.mul_lt_mul_of_pos_left hn_lt (by decide : 0 < 512)
    simpa [overheadLen, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm, Nat.left_distrib, Nat.right_distrib] using hmul
  have hpayloadStrict :
      payload * ell < overheadLen * ell :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft :
      ell * payload < ell * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  have hbp : n = 2 * shape.size := by
    simpa [n] using Cartesian.CartesianShape.bpCode_length shape
  simpa [payload, overheadLen, sparseExceptionRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ell, n, hbp,
    sparseDenseFalseSelectEll, sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).payload.length <=
      sparseExceptionRelativeTableOverhead shape.size := by
  exact
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
      shape
      (builtRelativeSplitFalseSelectShortSuperLocalSpanSum_le_bpCode_length
        shape)

def builtRelativeSplitFalseSelectLongSuperFlagBits
    (shape : Cartesian.CartesianShape) : List Bool :=
  (List.range (builtRectangularFalseSelectSuperSlotCount shape)).map
    (builtRelativeSplitFalseSelectSuperIsLong shape)

def builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    List Nat :=
  if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
    let baseOccurrence :=
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
      (sparseDenseFalseSelectSuperStride shape)
      (builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
      basePosition
  else
    []

def builtRelativeSplitFalseSelectLongSuperRelativeEntries
    (shape : Cartesian.CartesianShape) : List Nat :=
  (List.range (builtRectangularFalseSelectSuperSlotCount shape)).flatMap
    (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot shape)

def builtRelativeSplitFalseSelectLongSuperRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_get?
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape)[superSlot]? =
      some (builtRelativeSplitFalseSelectSuperIsLong shape superSlot) := by
  simp [builtRelativeSplitFalseSelectLongSuperFlagBits,
    List.getElem?_map, List.getElem?_range hslot]

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
      shape superSlot).length =
      if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
        sparseDenseFalseSelectSuperStride shape
      else
        0 := by
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hlong, falseSelectRelativeOffsetsOrZero_length]
  · have hfalse :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hfalse]

theorem compactLongSuperFlagRank_eq_segmentIndex
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectSuperSlotCount shape) :
    ((List.range n).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
          sparseDenseFalseSelectSuperStride shape := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectLongSuperFlagBits_get?
          shape (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          (n := n)
          hget
      have hprefix :
          (List.map
              (List.length ∘
                builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
                  shape)
              (List.range n)).sum =
            RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
                sparseDenseFalseSelectSuperStride shape := by
        simpa [List.length_flatMap, Function.comp] using ih hn'
      rw [List.range_succ]
      rw [List.flatMap_append]
      simp [List.flatMap,
        builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length,
        hrank]
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape n = true
      · rw [hprefix]
        simp [hlong, Nat.add_mul, Nat.add_comm]
      · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape n = false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape n
          · rfl
          · contradiction
        rw [hprefix]
        simp [hfalse]

theorem compactLongSuperRelativeEntries_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape).length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape) *
          sparseDenseFalseSelectSuperStride shape := by
  simpa [builtRelativeSplitFalseSelectLongSuperRelativeEntries] using
    compactLongSuperFlagRank_eq_segmentIndex shape (Nat.le_refl _)

def builtRelativeSplitFalseSelectLongSuperSpanSum
    (shape : Cartesian.CartesianShape) (slotCount : Nat) : Nat :=
  (List.range slotCount).map
    (fun superSlot =>
      if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
        builtRelativeSplitFalseSelectSuperSpan shape superSlot
      else
        0)
    |>.sum

theorem builtRelativeSplitFalseSelectLongSuperSpanSum_prefix_le_position
    (shape : Cartesian.CartesianShape) {slotCount : Nat}
    (hslotCount :
      slotCount <= builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectLongSuperSpanSum shape slotCount <=
      builtRelativeSplitFalseSelectPosition shape
        (builtRelativeSplitFalseSelectSuperBaseOccurrence shape slotCount) := by
  induction slotCount with
  | zero =>
      simp [builtRelativeSplitFalseSelectLongSuperSpanSum,
        builtRelativeSplitFalseSelectSuperBaseOccurrence,
        builtRelativeSplitFalseSelectPosition]
  | succ slotCount ih =>
      have hprefix :
          slotCount <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          slotCount < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have ih' := ih hprefix
      let prefixSum :=
        builtRelativeSplitFalseSelectLongSuperSpanSum shape slotCount
      let span :=
        if builtRelativeSplitFalseSelectSuperIsLong shape slotCount then
          builtRelativeSplitFalseSelectSuperSpan shape slotCount
        else
          0
      let basePos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape slotCount)
      let nextPos :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape (slotCount + 1))
      have ihPrefix : prefixSum <= basePos := by
        simpa [prefixSum, basePos] using ih'
      have hgap : span <= nextPos - basePos := by
        by_cases hlong :
            builtRelativeSplitFalseSelectSuperIsLong shape slotCount =
              true
        · have hspanGap :
              builtRelativeSplitFalseSelectSuperSpan shape slotCount <=
                nextPos - basePos := by
            simpa [basePos, nextPos] using
              builtRelativeSplitFalseSelectSuperSpan_le_next_gap
                shape hslot
          simpa [span, hlong] using hspanGap
        · have hfalse :
            builtRelativeSplitFalseSelectSuperIsLong shape slotCount =
              false := by
            cases h :
                builtRelativeSplitFalseSelectSuperIsLong shape slotCount
            · rfl
            · contradiction
          simp [span, hfalse]
      have hbaseNext :
          builtRelativeSplitFalseSelectSuperBaseOccurrence shape slotCount <=
            builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape (slotCount + 1) :=
        builtRelativeSplitFalseSelectSuperBaseOccurrence_le_next_base
          shape slotCount
      have hposMono : basePos <= nextPos := by
        simpa [basePos, nextPos] using
          builtRelativeSplitFalseSelectPosition_mono shape hbaseNext
      unfold builtRelativeSplitFalseSelectLongSuperSpanSum
      rw [List.range_succ, List.map_append, natList_sum_append]
      simp
      change prefixSum + span <= nextPos
      omega

theorem builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongSuperSpanSum shape
        (builtRectangularFalseSelectSuperSlotCount shape) <=
      shape.bpCode.length := by
  have hprefix :=
    builtRelativeSplitFalseSelectLongSuperSpanSum_prefix_le_position
      shape (Nat.le_refl _)
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      falseSelectCeilDiv_mul_ge_of_pos
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape)
  have hbase :
      falseSelectOccurrenceCount shape <=
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape
          (builtRectangularFalseSelectSuperSlotCount shape) := by
    simpa [builtRelativeSplitFalseSelectSuperBaseOccurrence] using hocc
  have hpos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
            (builtRectangularFalseSelectSuperSlotCount shape)) =
        shape.bpCode.length :=
    builtRelativeSplitFalseSelectPosition_eq_length_of_count_le
      shape hbase
  rwa [hpos] at hprefix

theorem longSuperExceptionCount_mul_superLongSpan_le_spanSum
    (shape : Cartesian.CartesianShape) {n : Nat}
    (hn :
      n <= builtRectangularFalseSelectSuperSlotCount shape) :
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape) n *
        sparseDenseFalseSelectSuperLongSpan shape <=
      builtRelativeSplitFalseSelectLongSuperSpanSum shape n := by
  induction n with
  | zero =>
      simp [RMQ.Succinct.rankPrefix,
        builtRelativeSplitFalseSelectLongSuperSpanSum]
  | succ n ih =>
      have hn' :
          n <= builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hslot :
          n < builtRectangularFalseSelectSuperSlotCount shape := by
        omega
      have hget :=
        builtRelativeSplitFalseSelectLongSuperFlagBits_get?
          shape (superSlot := n) hslot
      have hrank :=
        rankPrefix_succ_eq_of_get?
          (target := true)
          (bits := builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          (n := n)
          hget
      have ih' := ih hn'
      unfold builtRelativeSplitFalseSelectLongSuperSpanSum
      rw [List.range_succ]
      rw [List.map_append, natList_sum_append]
      simp [hrank]
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape n = true
      · have hspan :
            sparseDenseFalseSelectSuperLongSpan shape <=
              builtRelativeSplitFalseSelectSuperSpan shape n := by
          unfold builtRelativeSplitFalseSelectSuperIsLong at hlong
          by_cases hlt :
              sparseDenseFalseSelectSuperLongSpan shape <
                builtRelativeSplitFalseSelectSuperSpan shape n
          · omega
          · simp [hlt] at hlong
        simp [hlong]
        have hadd := Nat.add_le_add ih' hspan
        simpa [builtRelativeSplitFalseSelectLongSuperSpanSum,
          Nat.add_mul, Nat.one_mul, Nat.add_assoc,
          Nat.add_comm, Nat.add_left_comm] using hadd
      · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape n = false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape n
          · rfl
          · contradiction
        simp [hfalse]
        exact ih'

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {superSlot : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape) :
    builtRelativeSplitFalseSelectLongSuperRelativeEntries shape =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape superSlot ++
      (((List.range
            (builtRectangularFalseSelectSuperSlotCount shape -
              superSlot - 1)).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectLongSuperRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectSuperSlotCount shape - superSlot - 1
  have hcount :
      builtRectangularFalseSelectSuperSlotCount shape =
        superSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectSuperSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) =
      (List.range (superSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) := by
        rw [hcount]
    _ =
      ((List.range superSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => superSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
        rw [List.range_add]
    _ =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => superSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range superSlot).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape superSlot ++
      (((List.range tailCount).map
          (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem builtRelativeSplitFalseSelectLongSuperRelativeEntries_mem_lt_width
    {shape : Cartesian.CartesianShape} {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)) :
    entry <
      2 ^
        builtRelativeSplitFalseSelectLongSuperRelativeWidth shape := by
  unfold builtRelativeSplitFalseSelectLongSuperRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with ⟨superSlot, _hslotMem, hentryMem⟩
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · let baseOccurrence :=
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    have hmemOffsets :
        List.Mem entry
          (falseSelectRelativeOffsetsOrZero shape.bpCode baseOccurrence
            (sparseDenseFalseSelectSuperStride shape)
            (builtRelativeSplitFalseSelectSuperEndOccurrence
              shape superSlot)
            basePosition) := by
      simpa [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
        hlong, baseOccurrence, basePosition] using hentryMem
    rcases falseSelectRelativeOffsetsOrZero_mem_cases
        hmemOffsets with hzero | hsome
    · subst entry
      exact Nat.pow_pos (by omega : 0 < 2)
    · rcases hsome with
        ⟨offset, pos, _hoff, _hend, hselect, hentry⟩
      have hposLen : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      have hentryLen : entry < shape.bpCode.length := by
        rw [hentry]
        omega
      exact Nat.lt_trans hentryLen
        (by
          simpa [builtRelativeSplitFalseSelectLongSuperRelativeWidth,
            SuccinctRankProposal.machineWordBits] using
            (Nat.lt_log2_self (n := shape.bpCode.length)))
  · have hfalse :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hfalse] at hentryMem

def builtRelativeSplitFalseSelectLongSuperRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)
      (builtRelativeSplitFalseSelectLongSuperRelativeWidth shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)
    (builtRelativeSplitFalseSelectLongSuperRelativeWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectLongSuperRelativeEntries_mem_lt_width
          hmem)

theorem compactLongSuperRelativeTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).payload.length =
      RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        (builtRectangularFalseSelectSuperSlotCount shape) *
          sparseDenseFalseSelectSuperStride shape *
          builtRelativeSplitFalseSelectLongSuperRelativeWidth shape := by
  rw [(builtRelativeSplitFalseSelectLongSuperRelativeTable
    shape).payload_length_eq]
  rw [compactLongSuperRelativeEntries_length]

theorem compactLongSuperRelativeTable_payload_mul_ell_le_spanSum
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length *
        sparseDenseFalseSelectEll shape <=
      builtRelativeSplitFalseSelectLongSuperSpanSum shape
        (builtRectangularFalseSelectSuperSlotCount shape) := by
  have hcount :=
    longSuperExceptionCount_mul_superLongSpan_le_spanSum
      shape (Nat.le_refl _)
  rw [compactLongSuperRelativeTable_payload_length]
  simpa [builtRelativeSplitFalseSelectLongSuperRelativeWidth,
    sparseDenseFalseSelectSuperLongSpan,
    sparseDenseFalseSelectWordBits,
    Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hcount

def compactLongSuperRelativeTableOverhead (n : Nat) : Nat :=
  SuccinctSpace.idDivLogLogOverhead 1 (2 * n) + 1

theorem compactLongSuperRelativeTableOverhead_littleO :
    SuccinctSpace.LittleOLinear
      compactLongSuperRelativeTableOverhead := by
  unfold compactLongSuperRelativeTableOverhead
  exact
    ((SuccinctSpace.idDivLogLogOverhead_littleO 1).comp_two_mul_arg).add_const
      1

theorem compactLongSuperRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (hspan :
      builtRelativeSplitFalseSelectLongSuperSpanSum shape
          (builtRectangularFalseSelectSuperSlotCount shape) <=
        shape.bpCode.length) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      compactLongSuperRelativeTableOverhead shape.size := by
  let payload :=
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length
  let ell := sparseDenseFalseSelectEll shape
  let n := shape.bpCode.length
  have hell_pos : 0 < ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hpayloadEll :
      payload * ell <= n := by
    have hscaled :=
      compactLongSuperRelativeTable_payload_mul_ell_le_spanSum shape
    exact Nat.le_trans (by simpa [payload, ell] using hscaled)
      (by simpa [n] using hspan)
  let overheadLen := n / ell + 1
  have hn_lt :
      n < n / ell * ell + ell :=
    Nat.lt_div_mul_add hell_pos (a := n)
  have hscaledStrict :
      n < overheadLen * ell := by
    simpa [overheadLen, Nat.add_mul, Nat.one_mul, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hn_lt
  have hpayloadStrict :
      payload * ell < overheadLen * ell :=
    Nat.lt_of_le_of_lt hpayloadEll hscaledStrict
  have hpayloadStrictLeft :
      ell * payload < ell * overheadLen := by
    simpa [Nat.mul_comm] using hpayloadStrict
  have hpayloadLe : payload <= overheadLen :=
    Nat.le_of_mul_le_mul_left (Nat.le_of_lt hpayloadStrictLeft) hell_pos
  have hbp : n = 2 * shape.size := by
    simpa [n] using Cartesian.CartesianShape.bpCode_length shape
  simpa [payload, overheadLen, compactLongSuperRelativeTableOverhead,
    SuccinctSpace.idDivLogLogOverhead, ell, n, hbp,
    sparseDenseFalseSelectEll, sparseDenseFalseSelectWordBits,
    SuccinctRankProposal.machineWordBits] using hpayloadLe

theorem compactLongSuperRelativeTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperRelativeTable shape).payload.length <=
      compactLongSuperRelativeTableOverhead shape.size := by
  exact
    compactLongSuperRelativeTable_payload_le_overhead_of_spanSum_le_bpCode_length
      shape
      (builtRelativeSplitFalseSelectLongSuperSpanSum_le_bpCode_length
        shape)

def builtRelativeSplitFalseSelectLongFlagRankWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length

def builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
    (_shape : Cartesian.CartesianShape) : Nat := 1

def builtRelativeSplitFalseSelectLongFlagRankBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectLongFlagRankWordSize shape

theorem builtRelativeSplitFalseSelectLongFlagRankWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectLongFlagRankWordSize shape := by
  simp [builtRelativeSplitFalseSelectLongFlagRankWordSize,
    SuccinctRankProposal.machineWordBits_pos]

theorem builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape := by
  simp [builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper]

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length <
      2 ^ builtRelativeSplitFalseSelectLongFlagRankWordSize shape := by
  simpa [builtRelativeSplitFalseSelectLongFlagRankWordSize,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self
      (n := (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length))

theorem builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape *
        builtRelativeSplitFalseSelectLongFlagRankWordSize shape <
      2 ^ builtRelativeSplitFalseSelectLongFlagRankBlockWidth shape := by
  have hsucc :=
    SuccinctSpace.nat_succ_le_two_pow
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
  simpa [builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper,
    builtRelativeSplitFalseSelectLongFlagRankBlockWidth] using
    (by omega :
      builtRelativeSplitFalseSelectLongFlagRankWordSize shape <
        2 ^ builtRelativeSplitFalseSelectLongFlagRankWordSize shape)

def builtRelativeSplitFalseSelectLongFlagRankSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalSuperRankSampleTables
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectLongFlagRankBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockWidth shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow
        shape)).payload.length

def builtRelativeSplitFalseSelectLongFlagRankData
    (shape : Cartesian.CartesianShape) :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape)
      4 :=
  SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock
    (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
    (builtRelativeSplitFalseSelectLongFlagRankWordSize_pos shape)
    (by simp [builtRelativeSplitFalseSelectLongFlagRankWordSize])
    (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
    (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
      shape)
    (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow shape)
    (by omega)

theorem builtRelativeSplitFalseSelectLongFlagRankData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitFalseSelectLongFlagRankData shape
    data.auxPayload.length =
        builtRelativeSplitFalseSelectLongFlagRankSuperOverhead shape +
          builtRelativeSplitFalseSelectLongFlagRankBlockOverhead shape /\
      data.wordSize <=
        SuccinctRankProposal.machineWordBits
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape).length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        builtRelativeSplitFalseSelectLongSuperFlagBits shape /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits
              (builtRelativeSplitFalseSelectLongSuperFlagBits
                shape).length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= 4 /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target
              (builtRelativeSplitFalseSelectLongSuperFlagBits
                shape) pos := by
  exact
    SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile
      (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
      (builtRelativeSplitFalseSelectLongFlagRankWordSize_pos shape)
      (by simp [builtRelativeSplitFalseSelectLongFlagRankWordSize])
      (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper_pos shape)
      (builtRelativeSplitFalseSelectLongSuperFlagBits_length_lt_rank_word_pow
        shape)
      (builtRelativeSplitFalseSelectLongFlagRankBlockSpan_lt_pow shape)
      (by omega)

def builtRelativeSplitCompactLongSuperReadCosted
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
      true superSlot)
    fun exceptionRank =>
      Costed.map (fun offset? => offset?.map (fun offset => base + offset))
        ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
          (exceptionRank * sparseDenseFalseSelectSuperStride shape +
            localOccurrence))

theorem builtRelativeSplitCompactLongSuperReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape base superSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitCompactLongSuperReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
        true superSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted_cost_le_four
      true superSlot
  have hread :
      ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
        (((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
            true superSlot).value *
          sparseDenseFalseSelectSuperStride shape +
            localOccurrence)).cost <= 1 :=
    (builtRelativeSplitFalseSelectLongSuperRelativeTable
      shape).readCosted_cost_le_one _
  simp [Costed.bind, Costed.map] at *
  omega

theorem builtRelativeSplitCompactLongSuperReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base superSlot localOccurrence : Nat) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape base superSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
              superSlot *
            sparseDenseFalseSelectSuperStride shape +
            localOccurrence]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted_exact
      true superSlot
  change
      ((builtRelativeSplitFalseSelectLongFlagRankData shape).rankCosted
        true superSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot at hrank
  let slot :=
    RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
        superSlot *
      sparseDenseFalseSelectSuperStride shape +
      localOccurrence
  have hread :
      ((builtRelativeSplitFalseSelectLongSuperRelativeTable shape).readCosted
        slot).value =
        (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectLongSuperRelativeTable
        shape).readCosted_erase slot
  unfold builtRelativeSplitCompactLongSuperReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem compactLongSuperRelativeTable_lookup_exact
    (shape : Cartesian.CartesianShape)
    {superSlot localOccurrence pos : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape)
    (hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true)
    (hocc : localOccurrence < sparseDenseFalseSelectSuperStride shape)
    (hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
              superSlot +
            localOccurrence) =
        some pos) :
    (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) := by
  let pre :=
    (List.range superSlot).flatMap
      (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
        shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
      shape superSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectSuperSlotCount shape -
          superSlot - 1)).map
      (fun offset => superSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectLongSuperRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectLongSuperRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape := by
    simpa [pre] using
      compactLongSuperFlagRank_eq_segmentIndex
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        falseSelectRelativeOffsetsOrZero shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot)
          (sparseDenseFalseSelectSuperStride shape)
          (builtRelativeSplitFalseSelectSuperEndOccurrence shape
            superSlot)
          (builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot,
      hlong]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [builtRelativeSplitFalseSelectLongSuperRelativeEntriesForSlot_length]
    simp [hlong]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
          superSlot *
            sparseDenseFalseSelectSuperStride shape +
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
    falseSelectRelativeOffsetsOrZero_lookup_exact
      (bits := shape.bpCode)
      (baseOccurrence :=
        builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
      (count := sparseDenseFalseSelectSuperStride shape)
      (endOccurrence :=
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          superSlot)
      (basePosition :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem builtRelativeSplitCompactLongSuperReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {superSlot localOccurrence pos : Nat}
    (hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape)
    (hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true)
    (hocc : localOccurrence < sparseDenseFalseSelectSuperStride shape)
    (hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape
              superSlot +
            localOccurrence) =
        some pos) :
    (builtRelativeSplitCompactLongSuperReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot))
      superSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot))) := by
  rw [builtRelativeSplitCompactLongSuperReadCosted_erase]
  have hlookup :=
    compactLongSuperRelativeTable_lookup_exact
      shape hslot hlong hocc hend hselect
  simpa using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot) +
            offset))
      hlookup

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectSparseRelativeEntries shape =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range
            (builtRectangularFalseSelectLocalSlotCount shape -
              globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectSparseRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectLocalSlotCount shape -
      globalLocalSlot - 1
  have hcount :
      builtRectangularFalseSelectLocalSlotCount shape =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)) ++
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_decompose
    (shape : Cartesian.CartesianShape) {globalLocalSlot : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape) :
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range
            (builtRectangularFalseSelectLocalSlotCount shape -
              globalLocalSlot - 1)).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
  unfold builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
  let tailCount :=
    builtRectangularFalseSelectLocalSlotCount shape -
      globalLocalSlot - 1
  have hcount :
      builtRectangularFalseSelectLocalSlotCount shape =
        globalLocalSlot + (1 + tailCount) := by
    simp [tailCount]
    omega
  calc
    (List.range (builtRectangularFalseSelectLocalSlotCount shape)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) =
      (List.range (globalLocalSlot + (1 + tailCount))).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) := by
        rw [hcount]
    _ =
      ((List.range globalLocalSlot ++
          (List.range (1 + tailCount)).map
            (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
        rw [List.range_add]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      ((List.range (1 + tailCount)).map
          (fun offset => globalLocalSlot + offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape) := by
        simp [List.flatMap_append]
    _ =
      ((List.range globalLocalSlot).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) ++
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape globalLocalSlot ++
      (((List.range tailCount).map
          (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)) := by
        have hsucc : 1 + tailCount = tailCount + 1 := by omega
        rw [hsucc, List.range_succ_eq_map]
        simp [List.map, List.flatMap, List.map_map]
        apply congrArg List.flatten
        apply List.map_congr_left
        intro offset _hmem
        rfl

theorem falseSelectPositions_length
    (bits : List Bool) (base count : Nat) :
    (falseSelectPositions bits base count).length = count := by
  simp [falseSelectPositions]

theorem falseSelectPositions_mem_le_length
    {bits : List Bool} {base count pos : Nat}
    (hmem : List.Mem pos (falseSelectPositions bits base count)) :
    pos <= bits.length := by
  rcases List.mem_map.mp hmem with ⟨offset, _hoffset, rfl⟩
  cases hselect : RMQ.Succinct.select false bits (base + offset) with
  | none =>
      simp
  | some selected =>
      have hbound : selected < bits.length :=
        RMQ.Succinct.select_bounds hselect
      simp
      omega

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_mem_lt_word_pow
    {shape : Cartesian.CartesianShape} {entry : Nat}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape)) :
    entry < 2 ^ sparseDenseFalseSelectWordBits shape := by
  unfold builtRelativeSplitFalseSelectSparseRelativeEntries at hmem
  rcases List.mem_flatMap.mp hmem with
    ⟨globalLocalSlot, _hslotMem, hentryMem⟩
  unfold builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot at hentryMem
  by_cases hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse shape globalLocalSlot = true
  · simp [hsparse] at hentryMem
    rcases hentryMem with ⟨pos, hposMem, hentryEq⟩
    subst entry
    have hposLe :
        pos <= shape.bpCode.length :=
      falseSelectPositions_mem_le_length hposMem
    have hlenLt :
        shape.bpCode.length < 2 ^ sparseDenseFalseSelectWordBits shape := by
      simpa [sparseDenseFalseSelectWordBits,
        SuccinctRankProposal.machineWordBits] using
        (Nat.lt_log2_self (n := shape.bpCode.length))
    omega
  · simp [hsparse] at hentryMem

def builtRelativeSplitFalseSelectSparseRelativeTable
    (shape : Cartesian.CartesianShape) :
    SuccinctSpace.FixedWidthNatTable
      (builtRelativeSplitFalseSelectSparseRelativeEntries shape)
      (sparseDenseFalseSelectWordBits shape) :=
  SuccinctSpace.FixedWidthNatTable.ofEntries
    (builtRelativeSplitFalseSelectSparseRelativeEntries shape)
    (sparseDenseFalseSelectWordBits shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSparseRelativeEntries_mem_lt_word_pow
          hmem)

theorem builtRelativeSplitFalseSelectSparseRelativeTable_profile
    (shape : Cartesian.CartesianShape) :
    let table :=
      builtRelativeSplitFalseSelectSparseRelativeTable shape
    table.payload.length =
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape).length *
          sparseDenseFalseSelectWordBits shape /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase =
          (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[i]?) /\
      forall {word : List Bool},
        List.Mem word table.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let table := builtRelativeSplitFalseSelectSparseRelativeTable shape
  constructor
  · exact table.payload_length_eq
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i, table.readCosted_erase i⟩
    · intro word hmem
      rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
      have hget : table.store.words[i]? = some word := by
        simpa [Array.getElem?_toList] using hgetList
      rw [table.read_word_length_of_some hget]
      simp [sparseDenseFalseSelectWordBits]

theorem builtRelativeSplitFalseSelectSparseRelativeTable_payload_length
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseRelativeTable shape).payload.length =
      (builtRelativeSplitFalseSelectSparseRelativeEntries shape).length *
        sparseDenseFalseSelectWordBits shape := by
  exact
    (builtRelativeSplitFalseSelectSparseRelativeTable
      shape).payload_length_eq

theorem fullWidthSparseRelativePayload_not_littleO_of_linear_family
    {overhead : Nat -> Nat}
    (hlinear :
      forall n : Nat,
        exists shape : Cartesian.CartesianShape,
          shape.size = n /\
            n <=
              (builtRelativeSplitFalseSelectSparseRelativeTable
                shape).payload.length)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        (builtRelativeSplitFalseSelectSparseRelativeTable
          shape).payload.length <= overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  rcases hlinear n with ⟨shape, hsize, hpayload⟩
  have hbudget := hbound shape
  have hle : n <= overhead shape.size :=
    Nat.le_trans hpayload hbudget
  simpa [hsize] using hle

theorem falseSelectPositions_lookup_exact
    {bits : List Bool} {base count q pos : Nat}
    (hlo : base <= q)
    (hhi : q < base + count)
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    (falseSelectPositions bits base count)[q - base]? =
      RMQ.Succinct.select false bits q := by
  have hoff : q - base < count := by omega
  have hq : base + (q - base) = q := by omega
  simp [falseSelectPositions, List.getElem?_map,
    List.getElem?_range hoff, hq, hselect]

theorem falseSelectExplicitTable_lookup_exact
    {bits : List Bool} {pre post entries : List Nat}
    {base count q pos : Nat}
    (hentries :
      entries =
        pre ++ falseSelectPositions bits base count ++ post)
    (hlo : base <= q)
    (hhi : q < base + count)
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    entries[pre.length + (q - base)]? =
      RMQ.Succinct.select false bits q := by
  rw [hentries]
  rw [List.append_assoc]
  rw [List.getElem?_append_right (by omega)]
  have hidx : pre.length + (q - base) - pre.length = q - base := by
    omega
  rw [hidx]
  have hoff : q - base < (falseSelectPositions bits base count).length := by
    rw [falseSelectPositions_length]
    omega
  rw [List.getElem?_append_left hoff]
  exact falseSelectPositions_lookup_exact hlo hhi hselect

theorem builtRelativeSplitFalseSelectSparseRelativeEntries_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
      shape globalLocalSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectLocalSlotCount shape -
          globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectSparseRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectSparseRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape := by
    simpa [pre] using
      builtRelativeSplitFalseSelectSparseRelativePrefix_length
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        (falseSelectPositions shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape)).map
          (fun selected =>
            selected -
              builtRelativeSplitFalseSelectPosition shape
                (builtRectangularFalseSelectLocalBaseOccurrence
                  shape globalLocalSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectSparseRelativeEntriesForSlot,
      hsparse]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [hslotEntries]
    simp [falseSelectPositions_length]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
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
  have hlookup :
      (falseSelectPositions shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape))[localOccurrence]? =
        RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) := by
    have hlo :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot <=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence := by
      omega
    have hhi :
        builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence <
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot +
            sparseDenseFalseSelectLocalStride shape := by
      omega
    simpa using
      falseSelectPositions_lookup_exact
        (bits := shape.bpCode)
        (base :=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
        (count := sparseDenseFalseSelectLocalStride shape)
        (q :=
          builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence)
        (pos := pos)
        hlo hhi hselect
  simp [List.getElem?_map, hlookup, hselect]

theorem builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hend :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot + localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape)[
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
          localOccurrence]? =
      some
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
  let pre :=
    (List.range globalLocalSlot).flatMap
      (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
        shape)
  let slotEntries :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
      shape globalLocalSlot
  let post :=
    ((List.range
        (builtRectangularFalseSelectLocalSlotCount shape -
          globalLocalSlot - 1)).map
      (fun offset => globalLocalSlot + Nat.succ offset)).flatMap
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot
          shape)
  have hentries :
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape =
        pre ++ slotEntries ++ post := by
    simpa [pre, slotEntries, post] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_decompose
        shape hslot
  have hpre :
      pre.length =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape := by
    simpa [pre] using
      builtRelativeSplitFalseSelectSparseExceptionRelativePrefix_length
        shape (Nat.le_of_lt hslot)
  have hslotEntries :
      slotEntries =
        falseSelectRelativeOffsetsOrZero shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot)
          (sparseDenseFalseSelectLocalStride shape)
          (builtRelativeSplitFalseSelectSuperEndOccurrence shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape globalLocalSlot))
          (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot)) := by
    simp [slotEntries,
      builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot,
      hflag]
  have hslotLen :
      localOccurrence < slotEntries.length := by
    rw [builtRelativeSplitFalseSelectSparseExceptionRelativeEntriesForSlot_length]
    simp [hflag]
    exact hocc
  have hidx :
      RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          globalLocalSlot *
            sparseDenseFalseSelectLocalStride shape +
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
    falseSelectRelativeOffsetsOrZero_lookup_exact
      (bits := shape.bpCode)
      (baseOccurrence :=
        builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot)
      (count := sparseDenseFalseSelectLocalStride shape)
      (endOccurrence :=
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
      (basePosition :=
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot))
      (localOccurrence := localOccurrence)
      (pos := pos)
      hocc hend hselect

theorem falseSelectSuperEntry_lookup_exact
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth q superStride : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    {entry : SparseDenseFalseSelectLocatorEntry}
    (hlookup :
      entries[falseSelectSuperSlot q superStride]? = some entry) :
    (table.readCosted (q / superStride)).erase = some entry := by
  rw [FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
  simpa [falseSelectSuperSlot] using hlookup

theorem falseSelectLocalEntry_lookup_exact
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {fieldWidth q superStride localSlotsPerSuper localStride : Nat}
    (table :
      FixedWidthSparseDenseFalseSelectLocatorEntryTable
        entries fieldWidth)
    {super loc : SparseDenseFalseSelectLocatorEntry}
    (hlookup :
      entries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = some loc) :
    (table.readCosted
        (falseSelectLocalSlot q superStride localSlotsPerSuper
          localStride super)).erase =
      some loc := by
  rw [FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
  simpa [falseSelectLocalSlot] using hlookup

theorem falseSelectSuperEntry_missing_exact
    {bits : List Bool}
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {q superStride : Nat}
    (hcovered :
      forall pos,
        RMQ.Succinct.select false bits q = some pos ->
          exists entry,
            entries[falseSelectSuperSlot q superStride]? = some entry)
    (hmissing :
      entries[falseSelectSuperSlot q superStride]? = none) :
    RMQ.Succinct.select false bits q = none := by
  cases hselect : RMQ.Succinct.select false bits q with
  | none =>
      rfl
  | some pos =>
      have hsome := hcovered pos hselect
      cases hsome with
      | intro entry hentry =>
          rw [hmissing] at hentry
          contradiction

theorem falseSelectLocalEntry_missing_exact
    {bits : List Bool}
    {entries : List SparseDenseFalseSelectLocatorEntry}
    {q superStride localSlotsPerSuper localStride : Nat}
    {super : SparseDenseFalseSelectLocatorEntry}
    (hcovered :
      forall pos,
        RMQ.Succinct.select false bits q = some pos ->
          exists loc,
            entries[
                falseSelectLocalSlot q superStride localSlotsPerSuper
                  localStride super]? = some loc)
    (hmissing :
      entries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = none) :
    RMQ.Succinct.select false bits q = none := by
  cases hselect : RMQ.Succinct.select false bits q with
  | none =>
      rfl
  | some pos =>
      have hsome := hcovered pos hselect
      cases hsome with
      | intro loc hloc =>
          rw [hmissing] at hloc
          contradiction

theorem longSuperExplicitEntry_lookup_exact
    {bits : List Bool} {pre post entries : List Nat}
    {q count : Nat}
    {super : SparseDenseFalseSelectLocatorEntry}
    (hptr : super.pointer = pre.length)
    (hentries :
      entries =
        pre ++
          falseSelectPositions bits super.baseOccurrence count ++ post)
    (hlo : super.baseOccurrence <= q)
    (hhi : q < super.baseOccurrence + count)
    {pos : Nat}
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    entries[super.pointer + (q - super.baseOccurrence)]? =
      RMQ.Succinct.select false bits q := by
  rw [hptr]
  exact falseSelectExplicitTable_lookup_exact hentries hlo hhi hselect

theorem sparseLocalExplicitEntry_lookup_exact
    {bits : List Bool} {pre post entries : List Nat}
    {q count explicitBase : Nat}
    {loc : SparseDenseFalseSelectLocatorEntry}
    (hbase : explicitBase = pre.length)
    (hentries :
      entries =
        pre ++ falseSelectPositions bits loc.baseOccurrence count ++ post)
    (hlo : loc.baseOccurrence <= q)
    (hhi : q < loc.baseOccurrence + count)
    {pos : Nat}
    (hselect : RMQ.Succinct.select false bits q = some pos) :
    entries[explicitBase + (q - loc.baseOccurrence)]? =
      RMQ.Succinct.select false bits q := by
  rw [hbase]
  exact falseSelectExplicitTable_lookup_exact hentries hlo hhi hselect

structure FalseSelectAlignedBitWords
    (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize) :
    Prop where
  get_eq_take_drop :
    forall {i : Nat} {word : List Bool},
      bitWords.store.words[i]? = some word ->
        word = (bits.drop (i * wordSize)).take wordSize
  get_some_of_mul_lt :
    forall {i : Nat},
      i * wordSize < bits.length ->
        exists word, bitWords.store.words[i]? = some word

theorem falseSelectAlignedBitWords_ofChunks
    (bits : List Bool) {wordSize : Nat} (hword : 0 < wordSize) :
    FalseSelectAlignedBitWords bits wordSize
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hword) := by
  exact {
    get_eq_take_drop := by
      intro i word hget
      have hchunk :
          (SuccinctSpace.chunkPayloadWords wordSize bits)[i]? =
            some word := by
        simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
          Array.getElem?_toList] using hget
      exact SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
    get_some_of_mul_lt := by
      intro i hi
      have h :=
        SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
          (wordSize := wordSize) hword (payload := bits) (i := i) hi
      cases h with
      | intro word hchunk =>
          exact Exists.intro word (by
            simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
              Array.getElem?_toList] using hchunk) }

def falseSelectDenseLocalFirstStart
    (wordSize baseWordIndex : Nat) : Nat :=
  baseWordIndex * wordSize

def falseSelectDenseLocalSecondStart
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 1) * wordSize

def falseSelectDenseLocalSpanEnd
    (wordSize baseWordIndex : Nat) : Nat :=
  (baseWordIndex + 2) * wordSize

def falseSelectDenseLocalFirstWord
    (bits : List Bool) (wordSize baseWordIndex : Nat) : List Bool :=
  (bits.drop (falseSelectDenseLocalFirstStart wordSize baseWordIndex)).take
    wordSize

def falseSelectDenseLocalFirstCount
    (bits : List Bool) (wordSize baseWordIndex firstOffset : Nat) : Nat :=
  RMQ.RAM.boolRankPrefix false
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex).length -
    RMQ.RAM.boolRankPrefix false
      (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
      firstOffset

structure FalseSelectDenseLocalPayloadRoutingFacts
    (bits : List Bool) (wordSize basePosition baseOccurrence q : Nat) where
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat
  baseWordIndex_eq :
    baseWordIndex = basePosition / wordSize
  rankBefore_eq :
    rankBefore =
      RMQ.Succinct.rankPrefix false bits
        (falseSelectDenseLocalFirstStart wordSize baseWordIndex)
  firstOffset_eq :
    firstOffset =
      basePosition - falseSelectDenseLocalFirstStart wordSize baseWordIndex
  firstWordStart_readable :
    falseSelectDenseLocalFirstStart wordSize baseWordIndex < bits.length
  rankBefore_le_query :
    rankBefore <= q
  first_branch_rank :
    q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset ->
      q <
        RMQ.Succinct.rankPrefix false bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex)
  first_local_occurrence :
    RMQ.RAM.boolRankPrefix false
        (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
        firstOffset +
        (q - baseOccurrence) =
      q - rankBefore
  second_branch_rank :
    Not (q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset) ->
      RMQ.Succinct.rankPrefix false bits
          (falseSelectDenseLocalSecondStart wordSize baseWordIndex) <= q /\
        q <
          RMQ.Succinct.rankPrefix false bits
            (falseSelectDenseLocalSpanEnd wordSize baseWordIndex) /\
          falseSelectDenseLocalSecondStart wordSize baseWordIndex <
            bits.length
  second_local_occurrence :
    Not (q - baseOccurrence <
        falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset) ->
      q - baseOccurrence -
          falseSelectDenseLocalFirstCount
            bits wordSize baseWordIndex firstOffset =
        q -
          RMQ.Succinct.rankPrefix false bits
            (falseSelectDenseLocalSecondStart wordSize baseWordIndex)

structure FalseSelectDenseLocalSpanCertificate
    (bits : List Bool) (wordSize : Nat)
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) where
  firstWord : List Bool
  first_read :
    bitWords.store.words[basePosition / wordSize]? = some firstWord
  first_branch_exact :
    q - baseOccurrence <
      RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix false firstWord
          (basePosition - basePosition / wordSize * wordSize) ->
      (RMQ.RAM.boolSelectInWord false firstWord
        (RMQ.RAM.boolRankPrefix false firstWord
            (basePosition - basePosition / wordSize * wordSize) +
          (q - baseOccurrence))).map
        (fun offset => basePosition / wordSize * wordSize + offset) =
          RMQ.Succinct.select false bits q
  second_branch_exact :
    Not (q - baseOccurrence <
      RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
        RMQ.RAM.boolRankPrefix false firstWord
          (basePosition - basePosition / wordSize * wordSize)) ->
      exists secondWord,
        bitWords.store.words[basePosition / wordSize + 1]? =
            some secondWord /\
          (RMQ.RAM.boolSelectInWord false secondWord
            (q - baseOccurrence -
              (RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
                RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize)))).map
            (fun offset =>
              (basePosition / wordSize + 1) * wordSize + offset) =
              RMQ.Succinct.select false bits q

def falseSelectDenseLocalSpanCertificate_of_payload_routing_facts
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        bits wordSize basePosition baseOccurrence q) :
    FalseSelectDenseLocalSpanCertificate
      bits wordSize bitWords basePosition baseOccurrence q := by
  let firstStart :=
    falseSelectDenseLocalFirstStart wordSize hfacts.baseWordIndex
  let secondStart :=
    falseSelectDenseLocalSecondStart wordSize hfacts.baseWordIndex
  let spanEnd :=
    falseSelectDenseLocalSpanEnd wordSize hfacts.baseWordIndex
  let firstWord :=
    falseSelectDenseLocalFirstWord bits wordSize hfacts.baseWordIndex
  have hfirstReadAtBase :
      bitWords.store.words[hfacts.baseWordIndex]? = some firstWord := by
    cases haligned.get_some_of_mul_lt
        hfacts.firstWordStart_readable with
    | intro word hread =>
        have hword := haligned.get_eq_take_drop hread
        simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
          falseSelectDenseLocalFirstStart, hword] using hread
  have hfirstRead :
      bitWords.store.words[basePosition / wordSize]? = some firstWord := by
    rw [<- hfacts.baseWordIndex_eq]
    exact hfirstReadAtBase
  have hoffset :
      basePosition - basePosition / wordSize * wordSize =
        hfacts.firstOffset := by
    rw [<- hfacts.baseWordIndex_eq]
    simpa [firstStart, falseSelectDenseLocalFirstStart] using
      hfacts.firstOffset_eq.symm
  have hfirstStartDiv :
      basePosition / wordSize * wordSize = firstStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hsecondStartDiv :
      (basePosition / wordSize + 1) * wordSize = secondStart := by
    rw [<- hfacts.baseWordIndex_eq]
    rfl
  have hfirstEnd :
      secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEnd :
      spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  refine {
    firstWord := firstWord
    first_read := hfirstRead
    first_branch_exact := ?_
    second_branch_exact := ?_ }
  · intro hchoose
    have hchoiceFacts :
        q - baseOccurrence <
          falseSelectDenseLocalFirstCount
            bits wordSize hfacts.baseWordIndex hfacts.firstOffset := by
      simpa [firstWord, falseSelectDenseLocalFirstCount,
        falseSelectDenseLocalFirstWord, hoffset] using hchoose
    have hqFirstRank := hfacts.first_branch_rank hchoiceFacts
    have hqFirstRankAtSecond :
        q < RMQ.Succinct.rankPrefix false bits secondStart := by
      simpa [secondStart] using hqFirstRank
    cases select_exists_of_lt_rankPrefix
        (target := false) (bits := bits) (occurrence := q)
        (limit := secondStart) hqFirstRankAtSecond with
    | intro pos hselect =>
        have hrankBeforeLe :
            RMQ.Succinct.rankPrefix false bits firstStart <= q := by
          simpa [firstStart] using
            (by
              rw [<- hfacts.rankBefore_eq]
              exact hfacts.rankBefore_le_query)
        have hstart_le_pos : firstStart <= pos := by
          by_cases hle : firstStart <= pos
          · exact hle
          · have hpos_lt_start : pos < firstStart :=
              Nat.lt_of_not_ge hle
            have hocc_lt :=
              occurrence_lt_rankPrefix_of_select_lt hselect hpos_lt_start
            omega
        have hpos_lt_second : pos < secondStart := by
          by_cases hlt : pos < secondStart
          · exact hlt
          · have hsecond_le_pos : secondStart <= pos := Nat.le_of_not_gt hlt
            have hprefix_le :=
              RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                hselect hsecond_le_pos
            omega
        have hpos_lt_word : pos < firstStart + wordSize := by
          omega
        have hstartLen : firstStart <= bits.length :=
          Nat.le_of_lt hfacts.firstWordStart_readable
        have hlocal :=
          RMQ.Succinct.select_drop_take_eq_sub_of_select
            (target := false) (bits := bits) (occurrence := q)
            (idx := pos) (start := firstStart) (width := wordSize)
            hselect hstart_le_pos hpos_lt_word hstartLen hrankBeforeLe
        have hlocalOccurrence :
            RMQ.RAM.boolRankPrefix false firstWord hfacts.firstOffset +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix false bits firstStart := by
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            hfacts.rankBefore_eq] using hfacts.first_local_occurrence
        have hlocalOccurrenceCert :
            RMQ.RAM.boolRankPrefix false firstWord
                (basePosition - basePosition / wordSize * wordSize) +
                (q - baseOccurrence) =
              q - RMQ.Succinct.rankPrefix false bits firstStart := by
          simpa [hoffset] using hlocalOccurrence
        have hselectWord :
            RMQ.Succinct.select false firstWord
                (RMQ.RAM.boolRankPrefix false firstWord
                    (basePosition -
                      basePosition / wordSize * wordSize) +
                  (q - baseOccurrence)) =
              some (pos - firstStart) := by
          rw [hlocalOccurrenceCert]
          simpa [firstWord, falseSelectDenseLocalFirstWord, firstStart,
            falseSelectDenseLocalFirstStart] using hlocal
        calc
          (RMQ.RAM.boolSelectInWord false firstWord
              (RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) =
            (RMQ.Succinct.select false firstWord
              (RMQ.RAM.boolRankPrefix false firstWord
                  (basePosition -
                    basePosition / wordSize * wordSize) +
                (q - baseOccurrence))).map
              (fun offset =>
                basePosition / wordSize * wordSize + offset) := by
              simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
          _ = some
              (basePosition / wordSize * wordSize +
                (pos - firstStart)) := by
              simp [hselectWord]
          _ = some pos := by
              have hposEq :
                  basePosition / wordSize * wordSize +
                      (pos - firstStart) = pos := by
                omega
              simp [hposEq]
          _ = RMQ.Succinct.select false bits q := hselect.symm
  · intro hnot
    have hnotFacts :
        Not (q - baseOccurrence <
          falseSelectDenseLocalFirstCount
            bits wordSize hfacts.baseWordIndex hfacts.firstOffset) := by
      intro hchoice
      exact hnot (by
        simpa [firstWord, falseSelectDenseLocalFirstCount,
          falseSelectDenseLocalFirstWord, hoffset] using hchoice)
    have hbranch := hfacts.second_branch_rank hnotFacts
    cases hbranch with
    | intro hsecondRankLe hbranch =>
        cases hbranch with
        | intro hqSpan hsecondReadable =>
            have hsecondRankLeAt :
                RMQ.Succinct.rankPrefix false bits secondStart <= q := by
              simpa [secondStart] using hsecondRankLe
            have hqSpanAt :
                q < RMQ.Succinct.rankPrefix false bits spanEnd := by
              simpa [spanEnd] using hqSpan
            cases haligned.get_some_of_mul_lt hsecondReadable with
            | intro secondWord hsecondReadAtBase =>
                have hsecondWord :=
                  haligned.get_eq_take_drop hsecondReadAtBase
                have hsecondRead :
                    bitWords.store.words[basePosition / wordSize + 1]? =
                      some secondWord := by
                  rw [<- hfacts.baseWordIndex_eq]
                  exact hsecondReadAtBase
                refine ⟨secondWord, hsecondRead, ?_⟩
                cases select_exists_of_lt_rankPrefix
                    (target := false) (bits := bits) (occurrence := q)
                    (limit := spanEnd) hqSpanAt with
                | intro pos hselect =>
                    have hsecond_le_pos : secondStart <= pos := by
                      by_cases hle : secondStart <= pos
                      · exact hle
                      · have hpos_lt_second :
                            pos < secondStart := Nat.lt_of_not_ge hle
                        have hocc_lt :=
                          occurrence_lt_rankPrefix_of_select_lt
                            hselect hpos_lt_second
                        omega
                    have hpos_lt_span : pos < spanEnd := by
                      by_cases hlt : pos < spanEnd
                      · exact hlt
                      · have hend_le_pos : spanEnd <= pos :=
                          Nat.le_of_not_gt hlt
                        have hprefix_le :=
                          RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
                            hselect hend_le_pos
                        omega
                    have hpos_lt_word : pos < secondStart + wordSize := by
                      omega
                    have hstartLen : secondStart <= bits.length :=
                      Nat.le_of_lt hsecondReadable
                    have hlocal :=
                      RMQ.Succinct.select_drop_take_eq_sub_of_select
                        (target := false) (bits := bits) (occurrence := q)
                        (idx := pos) (start := secondStart)
                        (width := wordSize) hselect hsecond_le_pos
                        hpos_lt_word hstartLen hsecondRankLeAt
                    have hlocalOccurrence :
                        q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize * wordSize)) =
                          q -
                            RMQ.Succinct.rankPrefix false bits
                              secondStart := by
                      simpa [firstWord, falseSelectDenseLocalFirstCount,
                        falseSelectDenseLocalFirstWord, secondStart,
                        hoffset] using
                        hfacts.second_local_occurrence hnotFacts
                    have hselectWord :
                        RMQ.Succinct.select false secondWord
                            (q - baseOccurrence -
                              (RMQ.RAM.boolRankPrefix false firstWord
                                  firstWord.length -
                                RMQ.RAM.boolRankPrefix false firstWord
                                  (basePosition -
                                    basePosition / wordSize *
                                      wordSize))) =
                          some (pos - secondStart) := by
                      rw [hsecondWord]
                      rw [hlocalOccurrence]
                      simpa [secondStart,
                        falseSelectDenseLocalSecondStart] using hlocal
                    calc
                      (RMQ.RAM.boolSelectInWord false secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) =
                        (RMQ.Succinct.select false secondWord
                          (q - baseOccurrence -
                            (RMQ.RAM.boolRankPrefix false firstWord
                                firstWord.length -
                              RMQ.RAM.boolRankPrefix false firstWord
                                (basePosition -
                                  basePosition / wordSize *
                                    wordSize)))).map
                          (fun offset =>
                            (basePosition / wordSize + 1) * wordSize +
                              offset) := by
                          simp [RMQ.Succinct.ram_boolSelectInWord_eq_select]
                      _ = some
                          ((basePosition / wordSize + 1) * wordSize +
                            (pos - secondStart)) := by
                          simp [hselectWord]
                      _ = some pos := by
                          have hposEq :
                              (basePosition / wordSize + 1) * wordSize +
                                  (pos - secondStart) = pos := by
                            omega
                          simp [hposEq]
                      _ = RMQ.Succinct.select false bits q := hselect.symm

set_option linter.unusedSimpArgs false in
theorem denseTwoWordFalseSelectCosted_exact_of_local_span
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (hcert :
      FalseSelectDenseLocalSpanCertificate
        bits wordSize bitWords basePosition baseOccurrence q) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select false bits q := by
  by_cases hchoose :
      q - baseOccurrence <
        RMQ.RAM.boolRankPrefix false hcert.firstWord
          hcert.firstWord.length -
          RMQ.RAM.boolRankPrefix false hcert.firstWord
            (basePosition - basePosition / wordSize * wordSize)
  case pos =>
    have hexact := hcert.first_branch_exact hchoose
    simp [denseTwoWordFalseSelectCosted,
      SuccinctSpace.PayloadWordStore.readWordCosted,
      RMQ.RAM.readArray?, Costed.bind, Costed.map,
      Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
      hcert.first_read, hchoose, hexact]
  case neg =>
    have hsecond := hcert.second_branch_exact hchoose
    cases hsecond with
    | intro secondWord hpair =>
        cases hpair with
        | intro hread hexact =>
            simp [denseTwoWordFalseSelectCosted,
              SuccinctSpace.PayloadWordStore.readWordCosted,
              RMQ.RAM.readArray?, Costed.bind, Costed.map,
              Costed.pure, Costed.erase, RMQ.RAM.Exec.toCosted,
              hcert.first_read, hchoose, hread, hexact]

theorem denseTwoWordFalseSelectCosted_exact_of_payload_routing_facts
    {bits : List Bool} {wordSize : Nat}
    {bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize}
    {basePosition baseOccurrence q : Nat}
    (haligned : FalseSelectAlignedBitWords bits wordSize bitWords)
    (hfacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        bits wordSize basePosition baseOccurrence q) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).erase =
      RMQ.Succinct.select false bits q := by
  exact
    denseTwoWordFalseSelectCosted_exact_of_local_span
      (falseSelectDenseLocalSpanCertificate_of_payload_routing_facts
        haligned hfacts)

def falseSelectDenseLocalPayloadRoutingFacts_of_selected_span
    {bits : List Bool} {wordSize basePosition baseOccurrence q pos : Nat}
    (hwordSize : 0 < wordSize)
    (hbaseSelect :
      RMQ.Succinct.select false bits baseOccurrence = some basePosition)
    (hselect : RMQ.Succinct.select false bits q = some pos)
    (hbaseLe : baseOccurrence <= q)
    (hposSpan : pos < basePosition + wordSize) :
    FalseSelectDenseLocalPayloadRoutingFacts
      bits wordSize basePosition baseOccurrence q := by
  let baseWordIndex := basePosition / wordSize
  let firstStart := falseSelectDenseLocalFirstStart wordSize baseWordIndex
  let secondStart := falseSelectDenseLocalSecondStart wordSize baseWordIndex
  let spanEnd := falseSelectDenseLocalSpanEnd wordSize baseWordIndex
  let firstOffset := basePosition - firstStart
  let rankBefore := RMQ.Succinct.rankPrefix false bits firstStart
  have hfirstStartLeBase : firstStart <= basePosition := by
    simpa [firstStart, baseWordIndex, falseSelectDenseLocalFirstStart] using
      Nat.div_mul_le_self basePosition wordSize
  have hbaseLtSecond : basePosition < secondStart := by
    have hmodLt : basePosition % wordSize < wordSize :=
      Nat.mod_lt basePosition hwordSize
    have hdecomp :
        basePosition / wordSize * wordSize +
            basePosition % wordSize = basePosition := by
      rw [Nat.mul_comm]
      exact Nat.div_add_mod basePosition wordSize
    simp [secondStart, baseWordIndex,
      falseSelectDenseLocalSecondStart, Nat.succ_mul]
    omega
  have hsecondEq : secondStart = firstStart + wordSize := by
    simp [secondStart, firstStart, falseSelectDenseLocalSecondStart,
      falseSelectDenseLocalFirstStart, Nat.succ_mul]
  have hspanEndEq : spanEnd = secondStart + wordSize := by
    simp [spanEnd, secondStart, falseSelectDenseLocalSpanEnd,
      falseSelectDenseLocalSecondStart, Nat.add_assoc, Nat.succ_mul]
  have hfirstStartReadable : firstStart < bits.length := by
    have hbaseBounds : basePosition < bits.length :=
      RMQ.Succinct.select_bounds hbaseSelect
    exact Nat.lt_of_le_of_lt hfirstStartLeBase hbaseBounds
  have hrankBeforeLeBase : rankBefore <= baseOccurrence := by
    simpa [rankBefore] using
      RMQ.Succinct.rankPrefix_le_occurrence_of_le_select
        hbaseSelect hfirstStartLeBase
  have hrankBeforeLeQ : rankBefore <= q := by
    omega
  have hposLtSpanEnd : pos < spanEnd := by
    have hbaseLtFirstEnd : basePosition < firstStart + wordSize := by
      omega
    rw [hspanEndEq, hsecondEq]
    omega
  have hqLtSpanRank :
      q < RMQ.Succinct.rankPrefix false bits spanEnd := by
    exact occurrence_lt_rankPrefix_of_select_lt hselect hposLtSpanEnd
  let hi := Nat.min secondStart bits.length
  have hhiLen : hi <= bits.length := Nat.min_le_right _ _
  have hfirstStartHi : firstStart <= hi := by
    exact Nat.le_min.mpr
      ⟨by omega, Nat.le_of_lt hfirstStartReadable⟩
  have hhiSub :
      hi - firstStart =
        Nat.min wordSize (bits.drop firstStart).length := by
    by_cases hcase : secondStart <= bits.length
    · have hhiEq : hi = secondStart := by
        exact Nat.min_eq_left hcase
      have hdropLenGe :
          wordSize <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length = wordSize :=
        Nat.min_eq_left hdropLenGe
      rw [hhiEq, hminEq, hsecondEq]
      omega
    · have hhiEq : hi = bits.length := by
        exact Nat.min_eq_right (Nat.le_of_not_ge hcase)
      have hdropLenLe :
          (bits.drop firstStart).length <= wordSize := by
        simp [List.length_drop]
        omega
      have hminEq :
          Nat.min wordSize (bits.drop firstStart).length =
            (bits.drop firstStart).length :=
        Nat.min_eq_right hdropLenLe
      rw [hhiEq, hminEq]
      simp [List.length_drop]
  have hdrop :=
    RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
      false bits hfirstStartHi hhiLen
  have hbitsHiRank :
      RMQ.Succinct.rankPrefix false bits hi =
        RMQ.Succinct.rankPrefix false bits secondStart := by
    simpa [hi] using
      RMQ.Succinct.rankPrefix_min_length_eq false bits secondStart
  have hdropWordRank :
      RMQ.Succinct.rankPrefix false (bits.drop firstStart)
          wordSize =
        RMQ.Succinct.rankPrefix false (bits.drop firstStart)
          (hi - firstStart) := by
    have hmin :=
      RMQ.Succinct.rankPrefix_min_length_eq
        false (bits.drop firstStart) wordSize
    rw [<- hmin]
    rw [hhiSub]
  have hfirstTotal :
      RMQ.RAM.boolRankPrefix false
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          (falseSelectDenseLocalFirstWord bits wordSize
            baseWordIndex).length =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix false
          ((bits.drop firstStart).take wordSize)
          ((bits.drop firstStart).take wordSize).length =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart
    rw [rankPrefix_take_length_eq]
    change
      RMQ.Succinct.rankPrefix false
          (bits.drop firstStart) wordSize =
        RMQ.Succinct.rankPrefix false bits secondStart -
          RMQ.Succinct.rankPrefix false bits firstStart
    rw [hdropWordRank]
    rw [hdrop]
    rw [hbitsHiRank]
  have hfirstOffsetRank :
      RMQ.RAM.boolRankPrefix false
          (falseSelectDenseLocalFirstWord bits wordSize baseWordIndex)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix false bits firstStart := by
    rw [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix]
    change
      RMQ.Succinct.rankPrefix false
          ((bits.drop firstStart).take wordSize)
          firstOffset =
        baseOccurrence -
          RMQ.Succinct.rankPrefix false bits firstStart
    have hoffLen : firstOffset <=
        (falseSelectDenseLocalFirstWord bits wordSize
          baseWordIndex).length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      have hoffWord : firstOffset <= wordSize := by
        omega
      have hoffDrop : firstOffset <= (bits.drop firstStart).length := by
        simp [List.length_drop]
        omega
      simpa [falseSelectDenseLocalFirstWord] using
        (Nat.le_min.mpr ⟨hoffWord, hoffDrop⟩)
    have htake :=
      RMQ.Succinct.rankPrefix_take_eq_of_le
        false (bits.drop firstStart) (n := wordSize)
        (limit := firstOffset) hoffLen
    rw [htake]
    have hlimit : firstStart + firstOffset <= bits.length := by
      have hbaseLen : basePosition < bits.length :=
        RMQ.Succinct.select_bounds hbaseSelect
      omega
    have hdropOffset :=
      RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
        false bits (start := firstStart)
        (limit := firstStart + firstOffset)
        (by omega) hlimit
    have hbaseEq : firstStart + firstOffset = basePosition := by
      simp [firstOffset]
      omega
    rw [hbaseEq] at hdropOffset
    have hbaseRank :
        RMQ.Succinct.rankPrefix false bits basePosition =
          baseOccurrence := by
      exact RMQ.Succinct.select_rankPrefix_eq hbaseSelect
    rw [hdropOffset, hbaseRank]
  have hbaseLtSecondRank :
      baseOccurrence <
        RMQ.Succinct.rankPrefix false bits secondStart :=
    occurrence_lt_rankPrefix_of_select_lt hbaseSelect hbaseLtSecond
  have hfirstCountEq :
      falseSelectDenseLocalFirstCount
          bits wordSize baseWordIndex firstOffset =
        RMQ.Succinct.rankPrefix false bits secondStart - baseOccurrence := by
    unfold falseSelectDenseLocalFirstCount
    rw [hfirstTotal, hfirstOffsetRank]
    omega
  refine {
    baseWordIndex := baseWordIndex
    rankBefore := rankBefore
    firstOffset := firstOffset
    baseWordIndex_eq := rfl
    rankBefore_eq := rfl
    firstOffset_eq := rfl
    firstWordStart_readable := hfirstStartReadable
    rankBefore_le_query := hrankBeforeLeQ
    first_branch_rank := ?_
    first_local_occurrence := ?_
    second_branch_rank := ?_
    second_local_occurrence := ?_ }
  · intro hchoice
    rw [hfirstCountEq] at hchoice
    have hq :
        q < RMQ.Succinct.rankPrefix false bits secondStart := by
      omega
    simpa [secondStart] using hq
  · rw [hfirstOffsetRank]
    have hcalc :
        baseOccurrence -
            RMQ.Succinct.rankPrefix false bits firstStart +
            (q - baseOccurrence) =
          q - rankBefore := by
      simp [rankBefore]
      omega
    exact hcalc
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix false bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix false bits secondStart
      · have hchoice :
            q - baseOccurrence <
              falseSelectDenseLocalFirstCount
                bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    have hsecondReadable :
        secondStart < bits.length := by
      by_cases hle : secondStart <= pos
      · exact Nat.lt_of_le_of_lt hle (RMQ.Succinct.select_bounds hselect)
      · have hposLtSecond : pos < secondStart := Nat.lt_of_not_ge hle
        have hoccLt :=
          occurrence_lt_rankPrefix_of_select_lt hselect hposLtSecond
        omega
    exact
      ⟨by simpa [secondStart] using hsecondLe,
        by simpa [spanEnd] using hqLtSpanRank,
        by simpa [secondStart] using hsecondReadable⟩
  · intro hnot
    have hsecondLe :
        RMQ.Succinct.rankPrefix false bits secondStart <= q := by
      by_cases hlt :
          q < RMQ.Succinct.rankPrefix false bits secondStart
      · have hchoice :
            q - baseOccurrence <
              falseSelectDenseLocalFirstCount
                bits wordSize baseWordIndex firstOffset := by
          rw [hfirstCountEq]
          omega
        exact False.elim (hnot hchoice)
      · exact Nat.le_of_not_gt hlt
    rw [hfirstCountEq]
    simpa [secondStart] using
      (by
        omega :
          q - baseOccurrence -
              (RMQ.Succinct.rankPrefix false bits secondStart -
                baseOccurrence) =
            q - RMQ.Succinct.rankPrefix false bits secondStart)

structure SparseDenseFalseSelectBranchObligations
    (shape : Cartesian.CartesianShape)
    (wordSize superStride localSlotsPerSuper localStride : Nat)
    (superEntries : List SparseDenseFalseSelectLocatorEntry)
    (longSuperExplicitEntries : List Nat)
    (localEntries : List SparseDenseFalseSelectLocatorEntry)
    (sparseLocalExplicitEntries : List Nat)
    (denseLocalEntries : List SparseDenseFalseSelectDenseLocalEntry)
    (bitWords :
      SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize) :
    Prop where
  super_missing_exact :
    forall q,
      superEntries[q / superStride]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  long_explicit_exact :
    forall q super,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = true ->
        longSuperExplicitEntries[
            super.pointer + (q - super.baseOccurrence)]? =
          RMQ.Succinct.select false shape.bpCode q
  local_missing_exact :
    forall q super,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  sparse_explicit_exact :
    forall q super loc,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = some loc ->
      sparseDenseFalseSelectEntryIsMarked loc = true ->
        sparseLocalExplicitEntries[
            falseSelectSparseLocalExplicitSlot
              (falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super)
              q localStride loc]? =
          RMQ.Succinct.select false shape.bpCode q
  dense_exact :
    forall q super loc,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = some loc ->
      sparseDenseFalseSelectEntryIsMarked loc = false ->
        (match denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? with
          | none => Costed.pure none
          | some dense => denseLocalEntryFalseSelectCosted bitWords dense q
        ).erase =
          RMQ.Succinct.select false shape.bpCode q

theorem sparseDenseFalseSelectBranchObligations_of_built_entries
    {shape : Cartesian.CartesianShape}
    {wordSize superStride localSlotsPerSuper localStride : Nat}
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {denseLocalEntries : List SparseDenseFalseSelectDenseLocalEntry}
    {bitWords :
      SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize}
    (hsuperCovered :
      forall q pos,
        RMQ.Succinct.select false shape.bpCode q = some pos ->
          exists super,
            superEntries[falseSelectSuperSlot q superStride]? =
              some super)
    (hlongCover :
      forall q super,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = true ->
          exists count, exists pre, exists post, exists pos,
            super.pointer = pre.length /\
            longSuperExplicitEntries =
              pre ++
                falseSelectPositions shape.bpCode
                  super.baseOccurrence count ++ post /\
            super.baseOccurrence <= q /\
            q < super.baseOccurrence + count /\
            RMQ.Succinct.select false shape.bpCode q = some pos)
    (hlocalCovered :
      forall q super pos,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        RMQ.Succinct.select false shape.bpCode q = some pos ->
          exists loc,
            localEntries[
                falseSelectLocalSlot q superStride localSlotsPerSuper
                  localStride super]? = some loc)
    (hsparseCover :
      forall q super loc,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = true ->
          exists count, exists pre, exists post, exists pos,
            falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super * localStride =
              pre.length /\
            sparseLocalExplicitEntries =
              pre ++
                falseSelectPositions shape.bpCode
                  loc.baseOccurrence count ++ post /\
            loc.baseOccurrence <= q /\
            q < loc.baseOccurrence + count /\
            RMQ.Succinct.select false shape.bpCode q = some pos)
    (hdenseMissing :
      forall q super loc,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = false ->
        denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? = none ->
          RMQ.Succinct.select false shape.bpCode q = none)
    (hdenseCert :
      forall q super loc dense,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = false ->
        denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? = some dense ->
          FalseSelectDenseLocalSpanCertificate
            shape.bpCode wordSize bitWords
            (sparseDenseFalseSelectDenseLocalEntryBasePosition
              wordSize dense)
            dense.baseOccurrence q) :
    SparseDenseFalseSelectBranchObligations
      shape wordSize superStride localSlotsPerSuper localStride superEntries
      longSuperExplicitEntries localEntries sparseLocalExplicitEntries
      denseLocalEntries bitWords := by
  exact {
    super_missing_exact := by
      intro q hmissing
      exact
        falseSelectSuperEntry_missing_exact
          (bits := shape.bpCode) (entries := superEntries)
          (q := q) (superStride := superStride)
          (fun pos hselect => hsuperCovered q pos hselect)
          (by simpa [falseSelectSuperSlot] using hmissing)
    long_explicit_exact := by
      intro q super hsuper hmark
      have hslot :
          superEntries[falseSelectSuperSlot q superStride]? =
            some super := by
        simpa [falseSelectSuperSlot] using hsuper
      have hcover := hlongCover q super hslot hmark
      cases hcover with
      | intro count hcover =>
          cases hcover with
          | intro pre hcover =>
              cases hcover with
              | intro post hcover =>
                  cases hcover with
                  | intro pos hcover =>
                      cases hcover with
                      | intro hptr hcover =>
                          cases hcover with
                          | intro hentries hcover =>
                              cases hcover with
                              | intro hlo hcover =>
                                  cases hcover with
                                  | intro hhi hselect =>
                                      exact
                                        longSuperExplicitEntry_lookup_exact
                                          (bits := shape.bpCode)
                                          (pre := pre) (post := post)
                                          (entries :=
                                            longSuperExplicitEntries)
                                          (q := q) (count := count)
                                          (super := super)
                                          hptr hentries hlo hhi hselect
    local_missing_exact := by
      intro q super hsuper hmark hmissing
      have hslot :
          superEntries[falseSelectSuperSlot q superStride]? =
            some super := by
        simpa [falseSelectSuperSlot] using hsuper
      exact
        falseSelectLocalEntry_missing_exact
          (bits := shape.bpCode) (entries := localEntries)
          (q := q) (superStride := superStride)
          (localSlotsPerSuper := localSlotsPerSuper)
          (localStride := localStride) (super := super)
          (fun pos hselect =>
            hlocalCovered q super pos hslot hmark hselect)
          (by simpa [falseSelectLocalSlot] using hmissing)
    sparse_explicit_exact := by
      intro q super loc hsuper hmark hlocal hsparse
      have hslot :
          superEntries[falseSelectSuperSlot q superStride]? =
            some super := by
        simpa [falseSelectSuperSlot] using hsuper
      have hlocalSlot :
          localEntries[
              falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super]? =
            some loc := by
        simpa [falseSelectLocalSlot] using hlocal
      have hcover :=
        hsparseCover q super loc hslot hmark hlocalSlot hsparse
      cases hcover with
      | intro count hcover =>
          cases hcover with
          | intro pre hcover =>
              cases hcover with
              | intro post hcover =>
                  cases hcover with
                  | intro pos hcover =>
                      cases hcover with
                      | intro hptr hcover =>
                          cases hcover with
                          | intro hentries hcover =>
                              cases hcover with
                              | intro hlo hcover =>
                                  cases hcover with
                                  | intro hhi hselect =>
                                      exact
                                        sparseLocalExplicitEntry_lookup_exact
                                          (bits := shape.bpCode)
                                          (pre := pre) (post := post)
                                          (entries :=
                                            sparseLocalExplicitEntries)
                                          (explicitBase :=
                                            falseSelectLocalSlot q superStride
                                              localSlotsPerSuper localStride
                                              super * localStride)
                                          (q := q) (count := count)
                                          (loc := loc)
                                          hptr hentries hlo hhi hselect
    dense_exact := by
      intro q super loc hsuper hmark hlocal hdense
      have hslot :
          superEntries[falseSelectSuperSlot q superStride]? =
            some super := by
        simpa [falseSelectSuperSlot] using hsuper
      have hlocalSlot :
          localEntries[
              falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super]? =
            some loc := by
        simpa [falseSelectLocalSlot] using hlocal
      cases hdenseEntry :
          denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? with
      | none =>
          simpa [hdenseEntry] using
            (hdenseMissing q super loc hslot hmark hlocalSlot hdense
              hdenseEntry).symm
      | some dense =>
          simpa [hdenseEntry, denseLocalEntryFalseSelectCosted] using
            denseTwoWordFalseSelectCosted_exact_of_local_span
              (hdenseCert q super loc dense hslot hmark hlocalSlot
                hdense hdenseEntry) }

theorem sparseDenseFalseSelectBranchObligations_of_built_entries_and_dense_payload_facts
    {shape : Cartesian.CartesianShape}
    {wordSize superStride localSlotsPerSuper localStride : Nat}
    {superEntries : List SparseDenseFalseSelectLocatorEntry}
    {longSuperExplicitEntries : List Nat}
    {localEntries : List SparseDenseFalseSelectLocatorEntry}
    {sparseLocalExplicitEntries : List Nat}
    {denseLocalEntries : List SparseDenseFalseSelectDenseLocalEntry}
    {bitWords :
      SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize}
    (haligned :
      FalseSelectAlignedBitWords shape.bpCode wordSize bitWords)
    (hsuperCovered :
      forall q pos,
        RMQ.Succinct.select false shape.bpCode q = some pos ->
          exists super,
            superEntries[falseSelectSuperSlot q superStride]? =
              some super)
    (hlongCover :
      forall q super,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = true ->
          exists count, exists pre, exists post, exists pos,
            super.pointer = pre.length /\
            longSuperExplicitEntries =
              pre ++
                falseSelectPositions shape.bpCode
                  super.baseOccurrence count ++ post /\
            super.baseOccurrence <= q /\
            q < super.baseOccurrence + count /\
            RMQ.Succinct.select false shape.bpCode q = some pos)
    (hlocalCovered :
      forall q super pos,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        RMQ.Succinct.select false shape.bpCode q = some pos ->
          exists loc,
            localEntries[
                falseSelectLocalSlot q superStride localSlotsPerSuper
                  localStride super]? = some loc)
    (hsparseCover :
      forall q super loc,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = true ->
          exists count, exists pre, exists post, exists pos,
            falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super * localStride =
              pre.length /\
            sparseLocalExplicitEntries =
              pre ++
                falseSelectPositions shape.bpCode
                  loc.baseOccurrence count ++ post /\
            loc.baseOccurrence <= q /\
            q < loc.baseOccurrence + count /\
            RMQ.Succinct.select false shape.bpCode q = some pos)
    (hdenseMissing :
      forall q super loc,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = false ->
        denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? = none ->
          RMQ.Succinct.select false shape.bpCode q = none)
    (hdenseFacts :
      forall q super loc dense,
        superEntries[falseSelectSuperSlot q superStride]? = some super ->
        sparseDenseFalseSelectEntryIsMarked super = false ->
        localEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? =
          some loc ->
        sparseDenseFalseSelectEntryIsMarked loc = false ->
        denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? = some dense ->
          FalseSelectDenseLocalPayloadRoutingFacts
            shape.bpCode wordSize
            (sparseDenseFalseSelectDenseLocalEntryBasePosition
              wordSize dense)
            dense.baseOccurrence q) :
    SparseDenseFalseSelectBranchObligations
      shape wordSize superStride localSlotsPerSuper localStride superEntries
      longSuperExplicitEntries localEntries sparseLocalExplicitEntries
      denseLocalEntries bitWords := by
  exact
    sparseDenseFalseSelectBranchObligations_of_built_entries
      (shape := shape) (wordSize := wordSize)
      (superStride := superStride) (localStride := localStride)
      (localSlotsPerSuper := localSlotsPerSuper)
      (superEntries := superEntries)
      (longSuperExplicitEntries := longSuperExplicitEntries)
      (localEntries := localEntries)
      (sparseLocalExplicitEntries := sparseLocalExplicitEntries)
      (denseLocalEntries := denseLocalEntries)
      (bitWords := bitWords)
      hsuperCovered hlongCover hlocalCovered hsparseCover hdenseMissing
      (fun q super loc dense hsuper hmark hlocal hdense hdenseEntry =>
        falseSelectDenseLocalSpanCertificate_of_payload_routing_facts
          haligned
          (hdenseFacts q super loc dense hsuper hmark hlocal hdense
            hdenseEntry))

/--
Concrete sparse/dense false-select close data for one Cartesian shape.

The sparse/explicit payload classes are carried by
`SparseDenseFalseSelectCodecTables`; the dense-local branch additionally reads
`denseLocalTable`, whose split fields avoid putting a full BP base position in
the packed local locator entry.
-/
structure SparseDenseFalseSelectCloseData
    (shape : Cartesian.CartesianShape) where
  wordSize : Nat
  wordSize_eq :
    wordSize = sparseDenseFalseSelectWordBits shape
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits shape.bpCode.length
  superStride : Nat
  superStride_eq :
    superStride = sparseDenseFalseSelectSuperStride shape
  superStride_pos : 0 < superStride
  localStride : Nat
  localStride_eq :
    localStride = sparseDenseFalseSelectLocalStride shape
  localStride_pos : 0 < localStride
  localSlotsPerSuper : Nat
  localSlotsPerSuper_eq :
    localSlotsPerSuper =
      falseSelectLocalSlotsPerSuper superStride localStride
  superEntries : List SparseDenseFalseSelectLocatorEntry
  longSuperExplicitEntries : List Nat
  localEntries : List SparseDenseFalseSelectLocatorEntry
  sparseLocalExplicitEntries : List Nat
  denseLocalEntries : List SparseDenseFalseSelectDenseLocalEntry
  superFieldWidth : Nat
  longSuperExplicitWidth : Nat
  localFieldWidth : Nat
  sparseLocalExplicitWidth : Nat
  denseLocalFieldWidth : Nat
  tables :
    SparseDenseFalseSelectCodecTables
      superEntries longSuperExplicitEntries localEntries
      sparseLocalExplicitEntries superFieldWidth longSuperExplicitWidth
      localFieldWidth sparseLocalExplicitWidth
  denseLocalTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      denseLocalEntries denseLocalFieldWidth
  bitWords : SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize
  payload_length_le :
    (tables.payload ++ denseLocalTable.payload).length <=
      canonicalSparseDenseFalseSelectOverhead shape.size
  tables_read_words_length_le_machine :
    tables.ReadWordsLengthLeMachine shape.bpCode.length
  denseLocal_read_words_length_le_machine :
    denseLocalTable.ReadWordsLengthLeMachine shape.bpCode.length
  super_missing_exact :
    forall q,
      superEntries[q / superStride]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  long_explicit_exact :
    forall q super,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = true ->
        longSuperExplicitEntries[
            super.pointer + (q - super.baseOccurrence)]? =
          RMQ.Succinct.select false shape.bpCode q
  local_missing_exact :
    forall q super,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  sparse_explicit_exact :
    forall q super loc,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = some loc ->
      sparseDenseFalseSelectEntryIsMarked loc = true ->
        sparseLocalExplicitEntries[
            falseSelectSparseLocalExplicitSlot
              (falseSelectLocalSlot q superStride localSlotsPerSuper
                localStride super)
              q localStride loc]? =
          RMQ.Succinct.select false shape.bpCode q
  dense_exact :
    forall q super loc,
      superEntries[q / superStride]? = some super ->
      sparseDenseFalseSelectEntryIsMarked super = false ->
      localEntries[
          falseSelectLocalSlot q superStride localSlotsPerSuper
            localStride super]? = some loc ->
      sparseDenseFalseSelectEntryIsMarked loc = false ->
        (match denseLocalEntries[
            falseSelectLocalSlot q superStride localSlotsPerSuper
              localStride super]? with
          | none => Costed.pure none
          | some dense => denseLocalEntryFalseSelectCosted bitWords dense q
        ).erase =
          RMQ.Succinct.select false shape.bpCode q

namespace SparseDenseFalseSelectCloseData

def payload
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) : List Bool :=
  data.tables.payload ++ data.denseLocalTable.payload

def readWords
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) : List (List Bool) :=
  ((((data.tables.superTable.store.words.toList ++
        data.tables.longSuperExplicitTable.store.words.toList) ++
      data.tables.localTable.store.words.toList) ++
    data.tables.sparseLocalExplicitTable.store.words.toList) ++
      data.denseLocalTable.readWords) ++
        data.bitWords.store.words.toList

def queryOccurrence
    {shape : Cartesian.CartesianShape}
    (_data : SparseDenseFalseSelectCloseData shape) (idx : Nat) : Nat :=
  Nat.min idx shape.bpCode.length

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  let superSlot := q / data.superStride
  Costed.bind (data.tables.superTable.readCosted superSlot) fun super? =>
    match super? with
    | none => Costed.pure none
    | some super =>
        if sparseDenseFalseSelectEntryIsMarked super = true then
          data.tables.longSuperExplicitTable.readCosted
            (super.pointer + (q - super.baseOccurrence))
        else
          let localSlot :=
            falseSelectLocalSlot q data.superStride
              data.localSlotsPerSuper data.localStride super
          Costed.bind (data.tables.localTable.readCosted localSlot) fun local? =>
            match local? with
            | none => Costed.pure none
            | some loc =>
                if sparseDenseFalseSelectEntryIsMarked loc = true then
                  data.tables.sparseLocalExplicitTable.readCosted
                    (falseSelectSparseLocalExplicitSlot localSlot q
                      data.localStride loc)
                else
                  Costed.bind
                    (data.denseLocalTable.readCosted localSlot)
                    fun dense? =>
                      match dense? with
                      | none => Costed.pure none
                      | some dense =>
                          denseLocalEntryFalseSelectCosted
                            data.bitWords dense q

theorem payload_length_le_overhead
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) :
    data.payload.length <=
      canonicalSparseDenseFalseSelectOverhead shape.size := by
  simpa [payload] using data.payload_length_le

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <= SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  rcases data.tables_read_words_length_le_machine with
    ⟨hsuper, hlong, hlocal, hsparse⟩
  rw [readWords] at hmem
  rcases List.mem_append.mp hmem with hprefix0 | hbitsMem
  · rcases List.mem_append.mp hprefix0 with hprefix1 | hdenseMem
    · rcases List.mem_append.mp hprefix1 with hprefix2 | hsparseMem
      · rcases List.mem_append.mp hprefix2 with hprefix3 | hlocalMem
        · rcases List.mem_append.mp hprefix3 with hsuperMem | hlongMem
          · rcases (List.mem_iff_getElem?.mp hsuperMem) with
              ⟨i, hgetList⟩
            have hget :
                data.tables.superTable.store.words[i]? = some word := by
              simpa [Array.getElem?_toList] using hgetList
            exact hsuper hget
          · rcases (List.mem_iff_getElem?.mp hlongMem) with
              ⟨i, hgetList⟩
            have hget :
                data.tables.longSuperExplicitTable.store.words[i]? =
                  some word := by
              simpa [Array.getElem?_toList] using hgetList
            exact hlong hget
        · rcases (List.mem_iff_getElem?.mp hlocalMem) with ⟨i, hgetList⟩
          have hget :
              data.tables.localTable.store.words[i]? = some word := by
            simpa [Array.getElem?_toList] using hgetList
          exact hlocal hget
      · rcases (List.mem_iff_getElem?.mp hsparseMem) with ⟨i, hgetList⟩
        have hget :
            data.tables.sparseLocalExplicitTable.store.words[i]? =
              some word := by
          simpa [Array.getElem?_toList] using hgetList
        exact hsparse hget
    · exact data.denseLocalTable.read_word_length_le_machine
        data.denseLocal_read_words_length_le_machine hdenseMem
  · exact Nat.le_trans (data.bitWords.word_length_le hbitsMem)
      data.wordSize_le_machine

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <= SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact data.read_word_length_le_machine hmem

theorem super_locator_entry_word_width_le_machine
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {super : SparseDenseFalseSelectLocatorEntry}
    (hget : data.superEntries[i]? = some super) :
    sparseDenseFalseSelectLocatorEntryWordWidth data.superFieldWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hread := data.tables.superTable.read_exact i
  rw [hget] at hread
  rcases data.tables_read_words_length_le_machine with
    ⟨hsuper, _hlong, _hlocal, _hsparse⟩
  cases hword : data.tables.superTable.store.words[i]? with
  | none =>
      simp [hword] at hread
  | some word =>
      have hlen :
          word.length =
            sparseDenseFalseSelectLocatorEntryWordWidth
              data.superFieldWidth :=
        data.tables.superTable.read_word_length_of_some hword
      have hle :
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length :=
        hsuper hword
      rwa [hlen] at hle

theorem local_locator_entry_word_width_le_machine
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc) :
    sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hread := data.tables.localTable.read_exact i
  rw [hget] at hread
  rcases data.tables_read_words_length_le_machine with
    ⟨_hsuper, _hlong, hlocal, _hsparse⟩
  cases hword : data.tables.localTable.store.words[i]? with
  | none =>
      simp [hword] at hread
  | some word =>
      have hlen :
          word.length =
            sparseDenseFalseSelectLocatorEntryWordWidth
              data.localFieldWidth :=
        data.tables.localTable.read_word_length_of_some hword
      have hle :
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length :=
        hlocal hword
      rwa [hlen] at hle

theorem super_locator_entry_fields_lt
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {super : SparseDenseFalseSelectLocatorEntry}
    (hget : data.superEntries[i]? = some super) :
    super.baseOccurrence < 2 ^ data.superFieldWidth /\
      super.basePosition < 2 ^ data.superFieldWidth /\
        super.spanClass < 2 ^ data.superFieldWidth /\
          super.pointer < 2 ^ data.superFieldWidth := by
  exact data.tables.superTable.entry_fields_lt hget

theorem local_locator_entry_fields_lt
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc) :
    loc.baseOccurrence < 2 ^ data.localFieldWidth /\
      loc.basePosition < 2 ^ data.localFieldWidth /\
        loc.spanClass < 2 ^ data.localFieldWidth /\
          loc.pointer < 2 ^ data.localFieldWidth := by
  exact data.tables.localTable.entry_fields_lt hget

theorem local_locator_dense_pointer_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc)
    (hneeds : 2 ^ data.localFieldWidth <= loc.pointer) :
    False := by
  have hptr := (data.local_locator_entry_fields_lt hget).2.2.2
  omega

theorem local_locator_baseOccurrence_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc)
    (hneeds : 2 ^ data.localFieldWidth <= loc.baseOccurrence) :
    False := by
  have hbase := (data.local_locator_entry_fields_lt hget).1
  omega

theorem local_locator_basePosition_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc)
    (hneeds : 2 ^ data.localFieldWidth <= loc.basePosition) :
    False := by
  have hbase := (data.local_locator_entry_fields_lt hget).2.1
  omega

theorem dense_local_entry_fields_lt
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hget : data.denseLocalEntries[i]? = some entry) :
    entry.baseOccurrence < 2 ^ data.denseLocalFieldWidth /\
      entry.baseWordIndex < 2 ^ data.denseLocalFieldWidth /\
        entry.rankBefore < 2 ^ data.denseLocalFieldWidth /\
          entry.firstOffset < 2 ^ data.denseLocalFieldWidth := by
  exact data.denseLocalTable.entry_fields_lt hget

theorem dense_local_baseOccurrence_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hget : data.denseLocalEntries[i]? = some entry)
    (hneeds : 2 ^ data.denseLocalFieldWidth <= entry.baseOccurrence) :
    False := by
  have hbase := (data.dense_local_entry_fields_lt hget).1
  omega

theorem dense_local_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
          data.denseLocalEntries data.denseLocalFieldWidth) :
    False := by
  have hdensePayloadLe :
      data.denseLocalTable.payload.length <=
        (data.tables.payload ++ data.denseLocalTable.payload).length := by
    simp
  have hle :=
    Nat.le_trans hdensePayloadLe data.payload_length_le
  have hlen := data.denseLocalTable.payload_length
  rw [hlen] at hle
  omega

theorem dense_local_rows_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {rowCount : Nat}
    (hrows : rowCount <= data.denseLocalEntries.length)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        rowCount * data.denseLocalFieldWidth +
          rowCount * data.denseLocalFieldWidth +
            rowCount * data.denseLocalFieldWidth +
              rowCount * data.denseLocalFieldWidth) :
    False := by
  apply data.dense_local_payload_capacity_obstruction
  unfold sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget
  have hmul :
      rowCount * data.denseLocalFieldWidth <=
        data.denseLocalEntries.length * data.denseLocalFieldWidth :=
    Nat.mul_le_mul_right data.denseLocalFieldWidth hrows
  omega

theorem local_locator_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        data.localEntries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth) :
    False := by
  have hlocalPayloadLeTables :
      data.tables.localTable.payload.length <=
        data.tables.payload.length := by
    simp [SparseDenseFalseSelectCodecTables.payload]
    omega
  have htablesPayloadLe :
      data.tables.payload.length <=
        (data.tables.payload ++ data.denseLocalTable.payload).length := by
    simp
  have hlocalPayloadLe :
      data.tables.localTable.payload.length <=
        (data.tables.payload ++ data.denseLocalTable.payload).length :=
    Nat.le_trans hlocalPayloadLeTables htablesPayloadLe
  have hle := Nat.le_trans hlocalPayloadLe data.payload_length_le
  have hlen := data.tables.localTable.payload_length
  rw [hlen] at hle
  omega

theorem local_locator_rows_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {rowCount : Nat}
    (hrows : rowCount <= data.localEntries.length)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        rowCount *
          sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth) :
    False := by
  apply data.local_locator_payload_capacity_obstruction
  have hmul :
      rowCount *
          sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth <=
        data.localEntries.length *
          sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth :=
    Nat.mul_le_mul_right
      (sparseDenseFalseSelectLocatorEntryWordWidth data.localFieldWidth)
      hrows
  omega

theorem sparse_local_explicit_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        data.sparseLocalExplicitEntries.length *
          data.sparseLocalExplicitWidth) :
    False := by
  have hsparsePayloadLeTables :
      data.tables.sparseLocalExplicitTable.payload.length <=
        data.tables.payload.length := by
    simp [SparseDenseFalseSelectCodecTables.payload]
    omega
  have htablesPayloadLe :
      data.tables.payload.length <=
        (data.tables.payload ++ data.denseLocalTable.payload).length := by
    simp
  have hsparsePayloadLe :
      data.tables.sparseLocalExplicitTable.payload.length <=
        (data.tables.payload ++ data.denseLocalTable.payload).length :=
    Nat.le_trans hsparsePayloadLeTables htablesPayloadLe
  have hle := Nat.le_trans hsparsePayloadLe data.payload_length_le
  have hlen := data.tables.sparseLocalExplicitTable.payload_length
  rw [hlen] at hle
  omega

theorem sparse_local_explicit_rows_payload_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {rowCount : Nat}
    (hrows : rowCount <= data.sparseLocalExplicitEntries.length)
    (hneeds :
      canonicalSparseDenseFalseSelectOverhead shape.size <
        rowCount * data.sparseLocalExplicitWidth) :
    False := by
  apply data.sparse_local_explicit_payload_capacity_obstruction
  have hmul :
      rowCount * data.sparseLocalExplicitWidth <=
        data.sparseLocalExplicitEntries.length *
          data.sparseLocalExplicitWidth :=
    Nat.mul_le_mul_right data.sparseLocalExplicitWidth hrows
  omega

theorem short_super_local_pointer_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q : Nat} {super : SparseDenseFalseSelectLocatorEntry}
    (hsuper : data.superEntries[q / data.superStride]? = some super)
    (hneeds : 2 ^ data.superFieldWidth <= super.pointer) :
    False := by
  have hptr := (data.super_locator_entry_fields_lt hsuper).2.2.2
  omega

theorem short_super_baseOccurrence_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q : Nat} {super : SparseDenseFalseSelectLocatorEntry}
    (hsuper : data.superEntries[q / data.superStride]? = some super)
    (hneeds : 2 ^ data.superFieldWidth <= super.baseOccurrence) :
    False := by
  have hbase := (data.super_locator_entry_fields_lt hsuper).1
  omega

theorem dense_branch_packed_local_pointer_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q : Nat} {super loc : SparseDenseFalseSelectLocatorEntry}
    (_hsuper : data.superEntries[q / data.superStride]? = some super)
    (_hshort : sparseDenseFalseSelectEntryIsMarked super = false)
    (hlocal :
      data.localEntries[
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super]? =
        some loc)
    (_hdense : sparseDenseFalseSelectEntryIsMarked loc = false)
    (hneeds : 2 ^ data.localFieldWidth <= loc.pointer) :
    False := by
  exact data.local_locator_dense_pointer_capacity_obstruction
    hlocal hneeds

theorem rectangular_local_absolute_base_capacity_obstruction
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q : Nat} {super loc : SparseDenseFalseSelectLocatorEntry}
    (_hsuper : data.superEntries[q / data.superStride]? = some super)
    (_hshort : sparseDenseFalseSelectEntryIsMarked super = false)
    (hlocal :
      data.localEntries[
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super]? =
        some loc)
    (hneeds : 2 ^ data.localFieldWidth <= loc.baseOccurrence) :
    False := by
  exact data.local_locator_baseOccurrence_capacity_obstruction
    hlocal hneeds

theorem sparse_branch_padded_explicit_slot_lt_length
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q pos : Nat} {super loc : SparseDenseFalseSelectLocatorEntry}
    (hsuper : data.superEntries[q / data.superStride]? = some super)
    (hshort : sparseDenseFalseSelectEntryIsMarked super = false)
    (hlocal :
      data.localEntries[
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super]? =
        some loc)
    (hsparse : sparseDenseFalseSelectEntryIsMarked loc = true)
    (hselect : RMQ.Succinct.select false shape.bpCode q = some pos) :
    falseSelectSparseLocalExplicitSlot
        (falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
          data.localStride super)
        q data.localStride loc <
      data.sparseLocalExplicitEntries.length := by
  have hget :
      data.sparseLocalExplicitEntries[
          falseSelectSparseLocalExplicitSlot
            (falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
              data.localStride super)
            q data.localStride loc]? = some pos := by
    simpa [hselect] using
      data.sparse_explicit_exact q super loc hsuper hshort hlocal hsparse
  exact (List.getElem?_eq_some_iff.mp hget).1

theorem dense_branch_rectangular_slot_lt_length
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {q : Nat} {super loc : SparseDenseFalseSelectLocatorEntry}
    {dense : SparseDenseFalseSelectDenseLocalEntry}
    (_hsuper : data.superEntries[q / data.superStride]? = some super)
    (_hshort : sparseDenseFalseSelectEntryIsMarked super = false)
    (_hlocal :
      data.localEntries[
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super]? =
        some loc)
    (_hdenseBranch : sparseDenseFalseSelectEntryIsMarked loc = false)
    (hdense :
      data.denseLocalEntries[
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super]? =
        some dense) :
    falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
        data.localStride super <
      data.denseLocalEntries.length := by
  exact (List.getElem?_eq_some_iff.mp hdense).1

theorem super_locator_full_machine_field_impossible
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {super : SparseDenseFalseSelectLocatorEntry}
    (hget : data.superEntries[i]? = some super) :
    data.superFieldWidth ≠
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro hwidth
  have hbounded := data.super_locator_entry_word_width_le_machine hget
  rw [hwidth] at hbounded
  exact
    sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded
      shape.bpCode.length hbounded

theorem local_locator_full_machine_field_impossible
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape)
    {i : Nat} {loc : SparseDenseFalseSelectLocatorEntry}
    (hget : data.localEntries[i]? = some loc) :
    data.localFieldWidth ≠
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro hwidth
  have hbounded := data.local_locator_entry_word_width_le_machine hget
  rw [hwidth] at hbounded
  exact
    sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded
      shape.bpCode.length hbounded

set_option linter.unusedSimpArgs false in
theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) (idx : Nat) :
    (data.selectCloseCosted idx).cost <= sparseDenseFalseSelectQueryCost := by
  unfold selectCloseCosted sparseDenseFalseSelectQueryCost
  simp only [queryOccurrence]
  cases hsuperValue :
      (data.tables.superTable.readCosted
        ((Nat.min idx shape.bpCode.length) / data.superStride)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hsuperValue] <;> omega
  | some super =>
      by_cases hlong : sparseDenseFalseSelectEntryIsMarked super = true
      · have hlongCost :=
          data.tables.longSuperExplicitTable.readCosted_cost_le_one
            (super.pointer +
              (Nat.min idx shape.bpCode.length - super.baseOccurrence))
        simp [Costed.bind, Costed.pure, hsuperValue, hlong] <;> omega
      · let localSlot :=
          falseSelectLocalSlot (Nat.min idx shape.bpCode.length)
            data.superStride data.localSlotsPerSuper data.localStride super
        cases hlocalValue :
            (data.tables.localTable.readCosted localSlot).value with
        | none =>
            simp [Costed.bind, Costed.pure, hsuperValue, hlong,
              localSlot, hlocalValue] <;> omega
        | some loc =>
            by_cases hsparse :
                sparseDenseFalseSelectEntryIsMarked loc = true
            · have hsparseCost :=
                data.tables.sparseLocalExplicitTable.readCosted_cost_le_one
                  (falseSelectSparseLocalExplicitSlot localSlot
                    (Nat.min idx shape.bpCode.length) data.localStride loc)
              simp [Costed.bind, Costed.pure, hsuperValue, hlong,
                localSlot, hlocalValue, hsparse] <;> omega
            · have hdense :=
                data.denseLocalTable.readCosted_cost_le_four localSlot
              cases hdenseValue :
                  (data.denseLocalTable.readCosted localSlot).value with
              | none =>
                  simp [Costed.bind, Costed.pure, hsuperValue, hlong,
                    localSlot, hlocalValue, hsparse, hdenseValue] <;> omega
              | some dense =>
                  have hdenseSelect :=
                    denseLocalEntryFalseSelectCosted_cost_le_five
                      data.bitWords dense
                      (Nat.min idx shape.bpCode.length)
                  simp [Costed.bind, Costed.pure, hsuperValue, hlong,
                    localSlot, hlocalValue, hsparse, hdenseValue] <;> omega

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) (idx : Nat) :
    (data.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  let q := Nat.min idx shape.bpCode.length
  have hclamp :
      RMQ.Succinct.select false shape.bpCode q =
        SuccinctSpace.bpCloseOfInorder? shape idx := by
    calc
      RMQ.Succinct.select false shape.bpCode q =
          RMQ.Succinct.select false shape.bpCode idx := by
            simpa [q] using
              RMQ.Succinct.select_min_length_eq false shape.bpCode idx
      _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
            exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?
              shape idx
  unfold selectCloseCosted queryOccurrence
  simp only [Costed.erase_bind,
    FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
  cases hsuper :
      data.superEntries[q / data.superStride]? with
  | none =>
      simp
      rw [<- hclamp]
      exact (data.super_missing_exact q hsuper).symm
  | some super =>
      by_cases hlong : sparseDenseFalseSelectEntryIsMarked super = true
      · simp [hlong, SuccinctSpace.FixedWidthNatTable.readCosted_erase]
        rw [<- hclamp]
        exact data.long_explicit_exact q super hsuper hlong
      · have hlongFalse :
            sparseDenseFalseSelectEntryIsMarked super = false := by
          cases hmark : sparseDenseFalseSelectEntryIsMarked super
          · rfl
          · contradiction
        let localSlot :=
          falseSelectLocalSlot q data.superStride data.localSlotsPerSuper
            data.localStride super
        cases hlocal : data.localEntries[localSlot]? with
        | none =>
            simp [hlong,
              FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
            have hlocal' :
                data.localEntries[
                    falseSelectLocalSlot q data.superStride
                      data.localSlotsPerSuper data.localStride super]? =
                  none := by
              simpa [localSlot] using hlocal
            rw [hlocal']
            simp
            rw [<- hclamp]
            exact (data.local_missing_exact q super hsuper hlongFalse
              hlocal').symm
        | some loc =>
            by_cases hsparse :
                sparseDenseFalseSelectEntryIsMarked loc = true
            · simp [hlong,
                FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
              have hlocal' :
                  data.localEntries[
                      falseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                    some loc := by
                simpa [localSlot] using hlocal
              rw [hlocal']
              simp [hsparse,
                SuccinctSpace.FixedWidthNatTable.readCosted_erase]
              rw [<- hclamp]
              exact data.sparse_explicit_exact q super loc hsuper
                hlongFalse hlocal' hsparse
            · have hsparseFalse :
                  sparseDenseFalseSelectEntryIsMarked loc = false := by
                cases hmark : sparseDenseFalseSelectEntryIsMarked loc
                · rfl
                · contradiction
              simp [hlong,
                FixedWidthSparseDenseFalseSelectLocatorEntryTable.readCosted_erase]
              have hlocal' :
                  data.localEntries[
                      falseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                    some loc := by
                simpa [localSlot] using hlocal
              rw [hlocal']
              simp [hsparse]
              rw [<- hclamp]
              simpa [q] using
                data.dense_exact q super loc hsuper hlongFalse
                  hlocal' hsparseFalse

theorem profile
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) :
    data.payload.length <=
        canonicalSparseDenseFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear canonicalSparseDenseFalseSelectOverhead /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  constructor
  · exact data.payload_length_le_overhead
  · constructor
    · exact canonicalSparseDenseFalseSelectOverhead_littleO
    · constructor
      · exact data.selectCloseCosted_cost_le
      · constructor
        · exact data.selectCloseCosted_exact
        · intro word hmem
          exact data.read_word_length_le_machine hmem

theorem rectangularSparseDenseFalseSelectCloseData_profile
    {shape : Cartesian.CartesianShape}
    (data : SparseDenseFalseSelectCloseData shape) :
    data.payload.length <=
        canonicalSparseDenseFalseSelectOverhead shape.size /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hprofile := data.profile
  exact
    ⟨hprofile.1, hprofile.2.2.1, hprofile.2.2.2.1,
      hprofile.2.2.2.2⟩

end SparseDenseFalseSelectCloseData

/-!
### Relative/split rectangular false-select close locator

This is the compact replacement surface for the old packed local locator.  It
uses the existing split four-Nat payload table for both levels:

* a low-frequency super row stores absolute `baseOccurrence`, absolute
  `baseWordIndex`, a long-super tag in `rankBefore`, and `firstOffset`;
* a high-frequency local row stores only occurrence and word-index deltas from
  its super row, a sparse-local tag in `rankBefore`, and `firstOffset`.

Long-super and sparse-local explicit tables store relative offsets in padded
blocks.  The query reconstructs absolute positions from charged table reads; it
does not use `super.pointer`, `loc.pointer`, or an absolute dense-local index.
-/

def relativeSplitFalseSelectEntryIsMarked
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Bool :=
  entry.rankBefore != 0

def relativeSplitFalseSelectEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

def relativeSplitFalseSelectLocalBaseOccurrence
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  super.baseOccurrence + loc.baseOccurrence

def relativeSplitFalseSelectLocalBasePosition
    (wordSize : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  (super.baseWordIndex + loc.baseWordIndex) * wordSize + loc.firstOffset

def relativeSplitFalseSelectLongExplicitSlot
    (q superStride : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  falseSelectSuperSlot q superStride * superStride +
    (q - super.baseOccurrence)

def relativeSplitFalseSelectLongFlagBits
    (superEntries : List SparseDenseFalseSelectDenseLocalEntry) :
    List Bool :=
  superEntries.map relativeSplitFalseSelectEntryIsMarked

def relativeSplitFalseSelectLongCompactSlot
    (exceptionRank localOccurrence superStride : Nat) : Nat :=
  exceptionRank * superStride + localOccurrence

def relativeSplitFalseSelectSparseExplicitSlot
    (localSlot q localStride : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  localSlot * localStride +
    (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)

def relativeSplitFalseSelectSparseCompactSlot
    (exceptionRank localOccurrence localStride : Nat) : Nat :=
  exceptionRank * localStride + localOccurrence

def relativeSplitFalseSelectLocalSlotInSuper
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (q localStride : Nat) : Nat :=
  (q - super.baseOccurrence) / localStride

def relativeSplitFalseSelectLocalSlot
    (q superStride localSlotsPerSuper localStride : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  falseSelectSuperSlot q superStride * localSlotsPerSuper +
    relativeSplitFalseSelectLocalSlotInSuper super q localStride

def relativeOffsetReadCosted
    {entries : List Nat} {width : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (base slot : Nat) : Costed (Option Nat) :=
  Costed.map (fun offset? => offset?.map (fun offset => base + offset))
    (table.readCosted slot)

def builtRelativeSplitSparseExceptionReadCosted
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
      true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted
        (builtRelativeSplitFalseSelectSparseRelativeTable shape)
        base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence
          (sparseDenseFalseSelectLocalStride shape))

theorem builtRelativeSplitSparseExceptionReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape base localSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitSparseExceptionReadCosted
    relativeOffsetReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
        true localSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectFlagRankData shape).rankCosted_cost_le_four
      true localSlot
  have hread :
      ((builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted
        (relativeSplitFalseSelectSparseCompactSlot
          (((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
            true localSlot).value)
          localOccurrence
          (sparseDenseFalseSelectLocalStride shape))).cost <= 1 :=
    (builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted_cost_le_one
      _
  simp [Costed.bind, Costed.map] at *
  omega

theorem builtRelativeSplitSparseExceptionReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape base localSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectSparseRelativeEntries shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseFlagBits shape)
              localSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectFlagRankData shape).rankCosted_exact
      true localSlot
  change
      ((builtRelativeSplitFalseSelectFlagRankData shape).rankCosted
        true localSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseFlagBits shape)
          localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseFlagBits shape)
        localSlot)
      localOccurrence
      (sparseDenseFalseSelectLocalStride shape)
  have hread :
      ((builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted
        slot).value =
        (builtRelativeSplitFalseSelectSparseRelativeEntries shape)[slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectSparseRelativeTable shape).readCosted_erase
        slot
  unfold builtRelativeSplitSparseExceptionReadCosted
    relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem builtRelativeSplitSparseExceptionReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (hsparse :
      builtRelativeSplitFalseSelectLocalIsSparse
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    (builtRelativeSplitSparseExceptionReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  rw [builtRelativeSplitSparseExceptionReadCosted_erase]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseRelativeEntries_lookup_exact
      shape hslot hsparse hocc hselect
  simpa [relativeSplitFalseSelectSparseCompactSlot] using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot) +
            offset))
      hlookup

def builtRelativeSplitSparseExceptionNarrowReadCosted
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind
    ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted
        (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
          shape)
        base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence
          (sparseDenseFalseSelectLocalStride shape))

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_cost_le_five
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape base localSlot localOccurrence).cost <= 5 := by
  unfold builtRelativeSplitSparseExceptionNarrowReadCosted
    relativeOffsetReadCosted
  have hrank :
      ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
        shape).rankCosted true localSlot).cost <= 4 :=
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted_cost_le_four true localSlot
  have hread :
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted
        (relativeSplitFalseSelectSparseCompactSlot
          (((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
            shape).rankCosted true localSlot).value)
          localOccurrence
          (sparseDenseFalseSelectLocalStride shape))).cost <= 1 :=
    (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
      shape).readCosted_cost_le_one _
  simp [Costed.bind, Costed.map] at *
  omega

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_erase
    (shape : Cartesian.CartesianShape)
    (base localSlot localOccurrence : Nat) :
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape base localSlot localOccurrence).erase =
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseExceptionFlagBits
                shape)
              localSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?).map
        (fun offset => base + offset) := by
  have hrank :=
    (builtRelativeSplitFalseSelectSparseExceptionFlagRankData
      shape).rankCosted_exact true localSlot
  change
      ((builtRelativeSplitFalseSelectSparseExceptionFlagRankData
        shape).rankCosted true localSlot).value =
        RMQ.Succinct.rankPrefix true
          (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
          localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true
        (builtRelativeSplitFalseSelectSparseExceptionFlagBits shape)
        localSlot)
      localOccurrence
      (sparseDenseFalseSelectLocalStride shape)
  have hread :
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted slot).value =
        (builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[slot]? := by
    simpa [Costed.erase] using
      (builtRelativeSplitFalseSelectSparseExceptionRelativeTable
        shape).readCosted_erase slot
  unfold builtRelativeSplitSparseExceptionNarrowReadCosted
    relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem builtRelativeSplitSparseExceptionNarrowReadCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hend :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot + localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    (builtRelativeSplitSparseExceptionNarrowReadCosted
      shape
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot
      localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  rw [builtRelativeSplitSparseExceptionNarrowReadCosted_erase]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
      shape hslot hflag hocc hend hselect
  simpa [relativeSplitFalseSelectSparseCompactSlot] using
    congrArg
      (Option.map
        (fun offset =>
          builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot) +
            offset))
      hlookup

theorem builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
    (shape : Cartesian.CartesianShape) (superSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot := by
  unfold builtRelativeSplitFalseSelectSuperEntry
  by_cases hlong :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
  · simp [relativeSplitFalseSelectEntryIsMarked, hlong]
  · have hfalse :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
          false := by
      cases h :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot
      · rfl
      · contradiction
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat) :
    relativeSplitFalseSelectEntryIsMarked
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
        (builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot &&
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot) := by
  unfold builtRelativeSplitFalseSelectLocalEntry
  by_cases hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true
  · by_cases hflag :
        builtRelativeSplitFalseSelectLocalIsSparseException
          shape globalLocalSlot = true
    · simp [relativeSplitFalseSelectEntryIsMarked, hlive, hflag]
    · have hfalse :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot = false := by
        cases h :
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot
        · rfl
        · contradiction
      simp [relativeSplitFalseSelectEntryIsMarked, hlive, hfalse]
  · have hfalse :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
          shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    simp [relativeSplitFalseSelectEntryIsMarked, hfalse]

theorem builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBaseOccurrence
      (builtRelativeSplitFalseSelectSuperEntry shape
        (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape))
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
      builtRectangularFalseSelectLocalBaseOccurrence
        shape globalLocalSlot := by
  let superBase :=
    globalLocalSlot /
        builtRectangularFalseSelectLocalSlotsPerSuper shape *
      sparseDenseFalseSelectSuperStride shape
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  have hbase_ge :
      superBase <= base := by
    simp [superBase, base, builtRectangularFalseSelectLocalBaseOccurrence,
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
  simp [relativeSplitFalseSelectLocalBaseOccurrence,
    builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectLocalEntry, hlive,
    builtRelativeSplitFalseSelectLocalSuperSlot]
  omega

theorem builtRelativeSplitFalseSelectLocalBasePosition_exact
    (shape : Cartesian.CartesianShape) (globalLocalSlot : Nat)
    (hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true) :
    relativeSplitFalseSelectLocalBasePosition
      (sparseDenseFalseSelectWordBits shape)
      (builtRelativeSplitFalseSelectSuperEntry shape
        (globalLocalSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape))
      (builtRelativeSplitFalseSelectLocalEntry shape globalLocalSlot) =
      builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot) := by
  let superSlot :=
    globalLocalSlot /
      builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superBase :=
    superSlot * sparseDenseFalseSelectSuperStride shape
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let superPos := builtRelativeSplitFalseSelectPosition shape superBase
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let wordSize := sparseDenseFalseSelectWordBits shape
  have hbase_ge : superBase <= base := by
    simp [superBase, base, superSlot,
      builtRectangularFalseSelectLocalBaseOccurrence,
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
  have hposMono : superPos <= basePos := by
    simpa [superPos, basePos] using
      builtRelativeSplitFalseSelectPosition_mono shape hbase_ge
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
  simpa [relativeSplitFalseSelectLocalBasePosition,
    builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectLocalEntry, hlive,
    builtRelativeSplitFalseSelectLocalSuperSlot,
    superSlot, superBase, base, superPos, basePos, wordSize]
    using hassembled

theorem falseSelectOccurrenceCount_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    falseSelectOccurrenceCount shape <= shape.bpCode.length := by
  have hcount : falseSelectOccurrenceCount shape = shape.size :=
    falseSelectOccurrenceCount_eq_size shape
  have hbp : shape.bpCode.length = 2 * shape.size :=
    Cartesian.CartesianShape.bpCode_length shape
  omega

theorem builtRelativeSplitFalseSelectPosition_le_length
    (shape : Cartesian.CartesianShape) (occurrence : Nat) :
    builtRelativeSplitFalseSelectPosition shape occurrence <=
      shape.bpCode.length := by
  unfold builtRelativeSplitFalseSelectPosition
  cases hselect :
      RMQ.Succinct.select false shape.bpCode occurrence with
  | none =>
      simp
  | some pos =>
      have hpos : pos < shape.bpCode.length :=
        RMQ.Succinct.select_bounds hselect
      simp
      omega

theorem builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
    (shape : Cartesian.CartesianShape) {occurrence : Nat}
    (hocc : occurrence < falseSelectOccurrenceCount shape) :
    builtRelativeSplitFalseSelectPosition shape occurrence <
      shape.bpCode.length := by
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hocc with ⟨pos, hselect⟩
  rw [builtRelativeSplitFalseSelectPosition_eq_of_select shape hselect]
  exact RMQ.Succinct.select_bounds hselect

def builtRelativeSplitFalseSelectSuperFieldWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape

def builtRelativeSplitFalseSelectLocalFieldWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape

theorem builtRelativeSplitFalseSelectSuperEntries_mem_fields_lt_width
    {shape : Cartesian.CartesianShape}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectSuperEntries shape)) :
    entry.baseOccurrence <
        2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
      entry.baseWordIndex <
        2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
        entry.rankBefore <
          2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape /\
          entry.firstOffset <
            2 ^ builtRelativeSplitFalseSelectSuperFieldWidth shape := by
  rcases List.mem_map.mp hmem with ⟨superSlot, hslotMem, rfl⟩
  have hslot :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape :=
    List.mem_range.mp hslotMem
  let wordSize := sparseDenseFalseSelectWordBits shape
  let baseOccurrence :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let basePosition :=
    builtRelativeSplitFalseSelectPosition shape baseOccurrence
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using sparseDenseFalseSelectWordBits_pos shape
  have hbaseCount :
      baseOccurrence < falseSelectOccurrenceCount shape := by
    simpa [baseOccurrence] using
      builtRelativeSplitFalseSelectSuperBaseOccurrence_lt_count
        shape hslot
  have hbaseLen :
      baseOccurrence < shape.bpCode.length := by
    exact Nat.lt_of_lt_of_le hbaseCount
      (falseSelectOccurrenceCount_le_bpCode_length shape)
  have hlenPow :
      shape.bpCode.length < 2 ^ wordSize := by
    simpa [wordSize, sparseDenseFalseSelectWordBits,
      SuccinctRankProposal.machineWordBits] using
      (Nat.lt_log2_self (n := shape.bpCode.length))
  have hbasePow : baseOccurrence < 2 ^ wordSize :=
    Nat.lt_trans hbaseLen hlenPow
  have hpositionLen : basePosition <= shape.bpCode.length := by
    simpa [basePosition] using
      builtRelativeSplitFalseSelectPosition_le_length
        shape baseOccurrence
  have hwordIndexPow :
      basePosition / wordSize < 2 ^ wordSize := by
    have hdivLe : basePosition / wordSize <= basePosition :=
      Nat.div_le_self basePosition wordSize
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hdivLe hpositionLen) hlenPow
  have hmarkPow :
      (if builtRelativeSplitFalseSelectSuperIsLong shape superSlot then
          1 else 0) < 2 ^ wordSize := by
    by_cases hlong :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
    · simp [hlong, one_lt_two_pow_of_pos hwordPos]
    · have hfalse :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
            false := by
        cases h :
            builtRelativeSplitFalseSelectSuperIsLong shape superSlot
        · rfl
        · contradiction
      simp [hfalse, Nat.pow_pos (by omega : 0 < 2)]
  have hoffsetLtWord :
      basePosition - basePosition / wordSize * wordSize < wordSize := by
    simpa [Nat.mod_eq_sub_div_mul] using
      Nat.mod_lt basePosition hwordPos
  have hoffsetPow : basePosition - basePosition / wordSize * wordSize <
      2 ^ wordSize :=
    Nat.lt_trans hoffsetLtWord
      (by
        have hsucc := SuccinctSpace.nat_succ_le_two_pow wordSize
        omega)
  simpa [builtRelativeSplitFalseSelectSuperEntry,
    builtRelativeSplitFalseSelectSuperFieldWidth, wordSize,
    baseOccurrence, basePosition] using
    ⟨hbasePow, hwordIndexPow, hmarkPow, hoffsetPow⟩

def builtRelativeSplitFalseSelectSuperTable
    (shape : Cartesian.CartesianShape) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (builtRelativeSplitFalseSelectSuperEntries shape)
      (builtRelativeSplitFalseSelectSuperFieldWidth shape) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (builtRelativeSplitFalseSelectSuperEntries shape)
    (builtRelativeSplitFalseSelectSuperFieldWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectSuperEntries_mem_fields_lt_width hmem)

theorem builtRelativeSplitFalseSelectSuperTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSuperTable shape).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 shape.bpCode.length := by
  let payload := (builtRelativeSplitFalseSelectSuperTable shape).payload.length
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
  have hpayload :
      payload = 4 * (superCount * wordBits) := by
    have hlen := (builtRelativeSplitFalseSelectSuperTable shape).payload_length
    simp [payload, superCount, wordBits,
      builtRelativeSplitFalseSelectSuperTable,
      builtRelativeSplitFalseSelectSuperFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      builtRelativeSplitFalseSelectSuperEntries_length] at hlen ⊢
    omega
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
      have hstride_pos : 0 < superStride := by
        simpa [superStride] using sparseDenseFalseSelectSuperStride_pos shape
      have hpred_lt : superStride - 1 < superStride :=
        Nat.pred_lt (Nat.ne_of_gt hstride_pos)
      simpa [superStride] using Nat.div_eq_of_lt hpred_lt
    simp [payload, hpayload, hsuperZero,
      SuccinctSpace.logLogCubedSampledDirectoryOverhead]
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
    have hpayloadMul :
        payload * wordBits <= 20 * (ell3 * n) := by
      rw [hpayload]
      calc
        4 * (superCount * wordBits) * wordBits =
            4 * (superCount * superStride) := by
              simp [superStride, wordBits,
                sparseDenseFalseSelectSuperStride,
                Nat.mul_left_comm, Nat.mul_comm]
        _ <= 4 * (falseSelectOccurrenceCount shape + superStride) := by
              exact Nat.mul_le_mul_left 4 hsuperCountMul
        _ <= 4 * (n + 4 * n) := by
              exact Nat.mul_le_mul_left 4
                (Nat.add_le_add hcountLe hsuperStrideLe)
        _ = 20 * n := by omega
        _ <= 20 * (ell3 * n) := by
              have hmul := Nat.mul_le_mul_right n hellOne
              have hscaled := Nat.mul_le_mul_left 20 hmul
              simpa [Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hscaled
    exact
      payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := payload) (scale := 20)
        (by
          simpa [wordBits, ell, ell3, n, Nat.mul_assoc,
            Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem builtRelativeSplitFalseSelectLocalEntries_mem_fields_lt_width
    {shape : Cartesian.CartesianShape}
    {entry : SparseDenseFalseSelectDenseLocalEntry}
    (hmem :
      List.Mem entry
        (builtRelativeSplitFalseSelectLocalEntries shape)) :
    entry.baseOccurrence <
        2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
      entry.baseWordIndex <
        2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
        entry.rankBefore <
          2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape /\
          entry.firstOffset <
            2 ^ builtRelativeSplitFalseSelectLocalFieldWidth shape := by
  rcases List.mem_map.mp hmem with ⟨globalLocalSlot, hslotMem, rfl⟩
  let superSlot :=
    builtRelativeSplitFalseSelectLocalSuperSlot shape globalLocalSlot
  let superBase :=
    builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence shape globalLocalSlot
  let superPos := builtRelativeSplitFalseSelectPosition shape superBase
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let wordSize := sparseDenseFalseSelectWordBits shape
  let superLongSpan := sparseDenseFalseSelectSuperLongSpan shape
  let relWidth := builtRelativeSplitFalseSelectLocalFieldWidth shape
  have hwordPos : 0 < wordSize := by
    simpa [wordSize] using sparseDenseFalseSelectWordBits_pos shape
  have hellPos : 0 < sparseDenseFalseSelectEll shape := by
    simp [sparseDenseFalseSelectEll]
  have hrelPos : 0 < relWidth := by
    simp [relWidth, builtRelativeSplitFalseSelectLocalFieldWidth,
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth,
      SuccinctRankProposal.machineWordBits_pos]
  have hpowPos : 0 < 2 ^ relWidth := Nat.pow_pos (by omega : 0 < 2)
  have hfield_of_lt_min :
      forall {x : Nat},
        x < shape.bpCode.length ->
        x < superLongSpan ->
          x < 2 ^ relWidth := by
    intro x hbp hlong
    have hmin :
        x <
          Nat.min shape.bpCode.length
            (sparseDenseFalseSelectSuperLongSpan shape) :=
      Nat.lt_min.mpr ⟨hbp, by simpa [superLongSpan] using hlong⟩
    simpa [relWidth, builtRelativeSplitFalseSelectLocalFieldWidth,
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth] using
      lt_two_pow_machineWordBits_of_lt hmin
  by_cases hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape globalLocalSlot = true
  · have hliveFacts :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false /\
          base < falseSelectOccurrenceCount shape := by
      unfold builtRelativeSplitFalseSelectCompactLocalEntryIsLive at hlive
      by_cases hlong :
          builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true
      · simp [superSlot, hlong] at hlive
      · have hfalse :
            builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
              false := by
          cases h :
              builtRelativeSplitFalseSelectSuperIsLong shape superSlot
          · rfl
          · contradiction
        simp [superSlot, hfalse] at hlive
        exact ⟨hfalse, hlive⟩
    rcases hliveFacts with ⟨hshort, hbaseCount⟩
    have hsuperBaseLeBase : superBase <= base := by
      simp [superBase, base, superSlot,
        builtRelativeSplitFalseSelectSuperBaseOccurrence,
        builtRelativeSplitFalseSelectLocalSuperSlot,
        builtRectangularFalseSelectLocalBaseOccurrence,
        builtRectangularFalseSelectLocalSlotInSuperOfGlobal]
    have hbaseBoundary :
        base <
          superBase + sparseDenseFalseSelectSuperStride shape := by
      simpa [base, superBase, superSlot,
        builtRelativeSplitFalseSelectSuperBaseOccurrence] using
        builtRectangularFalseSelectLocalBaseOccurrence_lt_superBoundary
          shape globalLocalSlot
    have hbaseEnd :
        base <
          builtRelativeSplitFalseSelectSuperEndOccurrence
            shape superSlot := by
      unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      exact Nat.lt_min.mpr
        ⟨by
          simpa [superBase,
            builtRelativeSplitFalseSelectSuperBaseOccurrence] using
            hbaseBoundary,
          hbaseCount⟩
    have hbaseBp :
        base < shape.bpCode.length := by
      exact Nat.lt_of_lt_of_le hbaseCount
        (falseSelectOccurrenceCount_le_bpCode_length shape)
    have hdeltaBp :
        base - superBase < shape.bpCode.length := by
      omega
    have hstrideLeLong :
        sparseDenseFalseSelectSuperStride shape <= superLongSpan := by
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= sparseDenseFalseSelectEll shape := by omega
      have h1 :
          sparseDenseFalseSelectSuperStride shape <=
            sparseDenseFalseSelectSuperStride shape * wordSize := by
        simpa using
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape) hwordOne
      have h2 :
          sparseDenseFalseSelectSuperStride shape * wordSize <=
            sparseDenseFalseSelectSuperStride shape * wordSize *
              sparseDenseFalseSelectEll shape := by
        simpa using
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape * wordSize) hellOne
      exact Nat.le_trans h1 (by
        simpa [superLongSpan, sparseDenseFalseSelectSuperLongSpan,
          sparseDenseFalseSelectSuperStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h2)
    have hdeltaLong :
        base - superBase < superLongSpan := by
      have hdeltaStride :
          base - superBase < sparseDenseFalseSelectSuperStride shape := by
        omega
      exact Nat.lt_of_lt_of_le hdeltaStride hstrideLeLong
    have hbaseField :
        base - superBase < 2 ^ relWidth :=
      hfield_of_lt_min hdeltaBp hdeltaLong
    have hsuperCount :
        superBase < falseSelectOccurrenceCount shape := by
      omega
    have hbasePosLt :
        basePos < shape.bpCode.length := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
          shape hbaseCount
    have hsuperPosLt :
        superPos < shape.bpCode.length := by
      simpa [superPos] using
        builtRelativeSplitFalseSelectPosition_lt_length_of_lt_count
          shape hsuperCount
    have hposMono : superPos <= basePos := by
      simpa [superPos, basePos] using
        builtRelativeSplitFalseSelectPosition_mono
          shape hsuperBaseLeBase
    have hindexDeltaLe :
        basePos / wordSize - superPos / wordSize <=
          basePos - superPos :=
      nat_div_sub_div_le_sub hwordPos hposMono
    have hindexBp :
        basePos / wordSize - superPos / wordSize <
          shape.bpCode.length := by
      have hdivLe : basePos / wordSize <= basePos :=
        Nat.div_le_self basePos wordSize
      omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
    have hbasePosEq : basePos = baseWitness := by
      simpa [basePos] using
        builtRelativeSplitFalseSelectPosition_eq_of_select
          shape hbaseSelect
    have hoffLongWitness :
        baseWitness - superPos < superLongSpan := by
      have hraw :=
        builtRelativeSplitFalseSelect_selected_offset_lt_superLongSpan
          shape superSlot
          (localBaseOccurrence := superBase)
          (q := base) (pos := baseWitness)
          hshort (by simp [superBase])
          hsuperBaseLeBase hbaseEnd hbaseSelect
      simpa [superPos, superBase, superLongSpan] using hraw
    have hoffLong :
        basePos - superPos < superLongSpan := by
      simpa [hbasePosEq] using hoffLongWitness
    have hindexLong :
        basePos / wordSize - superPos / wordSize < superLongSpan :=
      Nat.lt_of_le_of_lt hindexDeltaLe hoffLong
    have hindexField :
        basePos / wordSize - superPos / wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hindexBp hindexLong
    have hmarkField :
        (if builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot then 1 else 0) < 2 ^ relWidth := by
      by_cases hflag :
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape globalLocalSlot = true
      · have hone : 1 < 2 ^ relWidth :=
          one_lt_two_pow_of_pos hrelPos
        simpa [hflag] using hone
      · have hfalse :
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape globalLocalSlot = false := by
          cases h :
              builtRelativeSplitFalseSelectLocalIsSparseException
                shape globalLocalSlot
          · rfl
          · contradiction
        simp [hfalse, hpowPos]
    have hoffsetLtWord :
        basePos - basePos / wordSize * wordSize < wordSize := by
      simpa [Nat.mod_eq_sub_div_mul] using
        Nat.mod_lt basePos hwordPos
    have hbpLenPos : 0 < shape.bpCode.length := by
      omega
    have hwordLeBp : wordSize <= shape.bpCode.length := by
      simpa [wordSize, sparseDenseFalseSelectWordBits] using
        machineWordBits_le_self_of_pos hbpLenPos
    have hwordLeLong : wordSize <= superLongSpan := by
      have hstridePos := sparseDenseFalseSelectSuperStride_pos shape
      have hwordOne : 1 <= wordSize := by omega
      have hellOne : 1 <= sparseDenseFalseSelectEll shape := by omega
      have hleStride : wordSize <=
          sparseDenseFalseSelectSuperStride shape * wordSize := by
        have hmul :=
          Nat.mul_le_mul_right wordSize
            (by exact (show 1 <= sparseDenseFalseSelectSuperStride shape by omega))
        simpa [Nat.mul_comm] using hmul
      have hleLong :
          sparseDenseFalseSelectSuperStride shape * wordSize <=
            superLongSpan := by
        have hmul :=
          Nat.mul_le_mul_left
            (sparseDenseFalseSelectSuperStride shape * wordSize)
            hellOne
        simpa [superLongSpan, sparseDenseFalseSelectSuperLongSpan,
          sparseDenseFalseSelectSuperStride, wordSize,
          Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      exact Nat.le_trans hleStride hleLong
    have hoffsetBp :
        basePos - basePos / wordSize * wordSize <
          shape.bpCode.length :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeBp
    have hoffsetLong :
        basePos - basePos / wordSize * wordSize < superLongSpan :=
      Nat.lt_of_lt_of_le hoffsetLtWord hwordLeLong
    have hoffsetField :
        basePos - basePos / wordSize * wordSize < 2 ^ relWidth :=
      hfield_of_lt_min hoffsetBp hoffsetLong
    simpa [builtRelativeSplitFalseSelectLocalEntry, hlive,
      builtRelativeSplitFalseSelectLocalFieldWidth, relWidth,
      superSlot, superBase, base, superPos, basePos, wordSize] using
      ⟨hbaseField, hindexField, hmarkField, hoffsetField⟩
  · have hfalse :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
          shape globalLocalSlot = false := by
      cases h :
          builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape globalLocalSlot
      · rfl
      · exact False.elim (hlive h)
    have hzero : 0 < 2 ^ relWidth := hpowPos
    have htuple :
        0 < 2 ^ relWidth /\
          0 < 2 ^ relWidth /\
            0 < 2 ^ relWidth /\
              0 < 2 ^ relWidth := by
      exact ⟨hzero, hzero, hzero, hzero⟩
    simpa [builtRelativeSplitFalseSelectLocalEntry, hfalse,
      builtRelativeSplitFalseSelectLocalFieldWidth, relWidth] using
      htuple

def builtRelativeSplitFalseSelectLocalTable
    (shape : Cartesian.CartesianShape) :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      (builtRelativeSplitFalseSelectLocalEntries shape)
      (builtRelativeSplitFalseSelectLocalFieldWidth shape) :=
  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ofEntries
    (builtRelativeSplitFalseSelectLocalEntries shape)
    (builtRelativeSplitFalseSelectLocalFieldWidth shape)
    (by
      intro entry hmem
      exact
        builtRelativeSplitFalseSelectLocalEntries_mem_fields_lt_width hmem)

theorem builtRelativeSplitFalseSelectLocalTable_payload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectLocalTable shape).payload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        640 shape.bpCode.length := by
  let payload := (builtRelativeSplitFalseSelectLocalTable shape).payload.length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let relWidth := builtRelativeSplitFalseSelectLocalFieldWidth shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hpayload :
      payload = 4 * (m * relWidth) := by
    have hlen :=
      (builtRelativeSplitFalseSelectLocalTable shape).payload_length
    simp [payload, m, relWidth,
      builtRelativeSplitFalseSelectLocalTable,
      builtRelativeSplitFalseSelectLocalFieldWidth,
      sparseDenseFalseSelectDenseLocalEntryMultiwordPayloadBudget,
      builtRelativeSplitFalseSelectLocalEntries_length] at hlen ⊢
    omega
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwidth : relWidth <= 4 * ell := by
    simpa [relWidth, ell, builtRelativeSplitFalseSelectLocalFieldWidth] using
      builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_four_ell
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hcore :
      m * relWidth * wordBits <= 80 * (ell3 * n) := by
    calc
      m * relWidth * wordBits <=
          m * relWidth * (2 * localStride * ell2) := by
            exact Nat.mul_le_mul_left (m * relWidth) hwordLower
      _ = 2 * (m * localStride) * relWidth * ell2 := by
            simp [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * (4 * ell) * ell2 := by
            have hmul := Nat.mul_le_mul hslots hwidth
            have hmul2 := Nat.mul_le_mul_left 2 hmul
            have hmul3 := Nat.mul_le_mul_right ell2 hmul2
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul3
      _ = 80 * (ell3 * n) := by
            simp [ell2, ell3, Nat.mul_assoc, Nat.mul_left_comm,
              Nat.mul_comm]
            let t := ell * (ell * (ell * n))
            change 2 * (4 * (10 * t)) = 80 * t
            omega
  have hpayloadMul :
      payload * wordBits <= 320 * (ell3 * n) := by
    rw [hpayload]
    have hmul := Nat.mul_le_mul_left 4 hcore
    calc
      4 * (m * relWidth) * wordBits <=
          4 * (80 * (ell3 * n)) := by
            simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      _ = 320 * (ell3 * n) := by
            let t := ell3 * n
            change 4 * (80 * t) = 320 * t
            omega
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (shape := shape) (payload := payload) (scale := 320)
      (by
        simpa [payload, wordBits, ell, ell3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hpayloadMul)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_mul_wordBits_le
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length *
        sparseDenseFalseSelectWordBits shape <=
      20 * ((sparseDenseFalseSelectEll shape *
        (sparseDenseFalseSelectEll shape *
          sparseDenseFalseSelectEll shape)) *
        shape.bpCode.length) := by
  let flagLen :=
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m,
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length]
      using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
        shape
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hmul :
      flagLen * wordBits <= 20 * (ell3 * n) := by
    calc
      flagLen * wordBits <= m * wordBits := by
        exact Nat.mul_le_mul_right wordBits hflagLe
      _ <= m * (2 * localStride * ell2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * localStride) * ell2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * ell2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right ell2 hscaled
      _ <= 20 * (ell3 * n) := by
        have hell2Le : ell2 <= ell3 := by
          have hmul := Nat.mul_le_mul_left ell2 hellOne
          simpa [ell2, ell3, Nat.mul_left_comm,
            Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) hell2Le
        calc
          2 * (10 * n) * ell2 = 20 * n * ell2 := by
            let t := ell2 * n
            simp [Nat.mul_left_comm, Nat.mul_comm]
            change 2 * (10 * t) = 20 * t
            omega
          _ <= 20 * n * ell3 := by
            simpa using hright
          _ = 20 * (ell3 * n) := by
            simp [Nat.mul_left_comm, Nat.mul_comm]
  simpa [flagLen, wordBits, ell, ell3, n, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hmul

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
        shape).length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        40 shape.bpCode.length := by
  let flagLen :=
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
      shape).length
  let m := builtRectangularFalseSelectLocalSlotCount shape
  let wordBits := sparseDenseFalseSelectWordBits shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  let ell := sparseDenseFalseSelectEll shape
  let ell2 := ell * ell
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  have hellOne : 1 <= ell := by
    simp [ell, sparseDenseFalseSelectEll]
  have hflagLe : flagLen <= m := by
    simpa [flagLen, m,
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length]
      using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount_le_full
        shape
  have hslots :
      m * localStride <= 10 * n := by
    simpa [m, localStride, n] using
      builtRectangularFalseSelectLocalSlotCount_mul_localStride_le_const_bpCode_length
        shape
  have hwordLower :
      wordBits <= 2 * localStride * ell2 := by
    simpa [wordBits, localStride, ell, ell2,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      sparseDenseFalseSelectWordBits_le_two_mul_localStride_mul_ell_sq
        shape
  have hmul :
      flagLen * wordBits <= 20 * (ell3 * n) := by
    calc
      flagLen * wordBits <= m * wordBits := by
        exact Nat.mul_le_mul_right wordBits hflagLe
      _ <= m * (2 * localStride * ell2) := by
        exact Nat.mul_le_mul_left m hwordLower
      _ = 2 * (m * localStride) * ell2 := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      _ <= 2 * (10 * n) * ell2 := by
        have hscaled := Nat.mul_le_mul_left 2 hslots
        exact Nat.mul_le_mul_right ell2 hscaled
      _ <= 20 * (ell3 * n) := by
        have hell2Le : ell2 <= ell3 := by
          have hmul := Nat.mul_le_mul_left ell2 hellOne
          simpa [ell2, ell3, Nat.mul_left_comm,
            Nat.mul_comm] using hmul
        have hright := Nat.mul_le_mul_left (20 * n) hell2Le
        calc
          2 * (10 * n) * ell2 = 20 * n * ell2 := by
            let t := ell2 * n
            simp [Nat.mul_left_comm, Nat.mul_comm]
            change 2 * (10 * t) = 20 * t
            omega
          _ <= 20 * n * ell3 := by
            simpa using hright
          _ = 20 * (ell3 * n) := by
            simp [Nat.mul_left_comm, Nat.mul_comm]
  exact
    payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
      (shape := shape) (payload := flagLen) (scale := 20)
      (by
        simpa [flagLen, wordBits, ell, ell3, n, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hmul)

theorem builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
    (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData
        shape).auxPayload.length <=
      SuccinctSpace.logLogCubedSampledDirectoryOverhead
        192 shape.bpCode.length + 16 := by
  let flagBits :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape
  let flagLen := flagBits.length
  let rankWord :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize
      shape
  let bpWord := sparseDenseFalseSelectWordBits shape
  let ell := sparseDenseFalseSelectEll shape
  let ell3 := ell * (ell * ell)
  let n := shape.bpCode.length
  let data :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData shape
  have hrankWordPos : 0 < rankWord := by
    simpa [rankWord] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_pos
        shape
  have hrankWordLeBp : rankWord <= bpWord := by
    simpa [rankWord, bpWord, sparseDenseFalseSelectWordBits] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankWordSize_le_machine
        shape
  have hauxEq :
      data.auxPayload.length =
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
            shape := by
    have hprofile :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape
    simpa [data] using hprofile.1
  have hsuperLe :
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
          shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
    rw [SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalSuperRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalSuperRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper]
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
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
          shape <=
        2 * (flagLen + rankWord) := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
    rw [SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalBlockRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalBlockRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
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
  have hauxLe :
      data.auxPayload.length <= 4 * (flagLen + rankWord) := by
    rw [hauxEq]
    calc
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
            shape +
          builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
            shape <=
        2 * (flagLen + rankWord) + 2 * (flagLen + rankWord) :=
          Nat.add_le_add hsuperLe hblockLe
      _ = 4 * (flagLen + rankWord) := by omega
  by_cases hnZero : n = 0
  · have hflagZero : flagLen = 0 := by
      have hlen :=
        builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length
          shape
      have hcountZero :
          builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
            shape = 0 := by
        have hbp : shape.size = 0 := by
          have hbpLen : shape.bpCode.length = 2 * shape.size :=
            Cartesian.CartesianShape.bpCode_length shape
          omega
        unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
        simp [falseSelectOccurrenceCount_eq_size, hbp]
      simpa [flagBits, flagLen, hcountZero] using hlen
    have hbpWord : bpWord = 1 := by
      simp [bpWord, sparseDenseFalseSelectWordBits,
        SuccinctRankProposal.machineWordBits, n, hnZero]
    have hrankSmall : rankWord <= 1 := by
      simpa [hbpWord] using hrankWordLeBp
    have hauxSmall : data.auxPayload.length <= 4 := by
      have h := hauxLe
      rw [hflagZero] at h
      omega
    have hoverNonneg :
        0 <=
          SuccinctSpace.logLogCubedSampledDirectoryOverhead
            192 shape.bpCode.length := Nat.zero_le _
    exact Nat.le_trans hauxSmall (by omega)
  have hflagMul :
      flagLen * bpWord <= 20 * (ell3 * n) := by
    simpa [flagBits, flagLen, bpWord, ell, ell3, n,
      sparseDenseFalseSelectWordBits, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_mul_wordBits_le
        shape
  have hrankMul :
      rankWord * bpWord <= 4 * (ell3 * n) := by
    have hbpSq :
        bpWord * bpWord <= 4 * n := by
      have hnPos : 0 < n := Nat.pos_of_ne_zero hnZero
      simpa [bpWord, sparseDenseFalseSelectWordBits, n] using
        machineWordBits_sq_le_four_mul_self_of_pos hnPos
    have hrankBp :
        rankWord * bpWord <= bpWord * bpWord :=
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
      data.auxPayload.length * bpWord <= 96 * (ell3 * n) := by
    calc
      data.auxPayload.length * bpWord <=
          4 * (flagLen + rankWord) * bpWord := by
            exact Nat.mul_le_mul_right bpWord hauxLe
      _ = 4 * (flagLen * bpWord + rankWord * bpWord) := by
            simp [Nat.add_mul, Nat.mul_assoc]
      _ <= 4 * (20 * (ell3 * n) + 4 * (ell3 * n)) := by
            exact Nat.mul_le_mul_left 4
              (Nat.add_le_add hflagMul hrankMul)
      _ = 96 * (ell3 * n) := by
            let t := ell3 * n
            change 4 * (20 * t + 4 * t) = 96 * t
            omega
  exact
    Nat.le_trans
      (payload_le_logLogCubedSampledDirectoryOverhead_of_mul_wordBits_le
        (shape := shape) (payload := data.auxPayload.length) (scale := 96)
        (by
          simpa [bpWord, ell, ell3, n, sparseDenseFalseSelectWordBits,
            Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hauxMul))
      (Nat.le_add_right _ _)

def sparseExceptionDirectoryOverhead
    (flagSlots rankSuperSlots rankBlockSlots explicitSlots : Nat)
    (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead flagSlots n +
    SuccinctSpace.sampledDirectoryOverhead rankSuperSlots n +
      SuccinctSpace.sampledDirectoryOverhead rankBlockSlots n +
        SuccinctSpace.idDivLogLogOverhead explicitSlots n

theorem sparseExceptionDirectoryOverhead_littleO
    (flagSlots rankSuperSlots rankBlockSlots explicitSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (sparseExceptionDirectoryOverhead
        flagSlots rankSuperSlots rankBlockSlots explicitSlots) := by
  unfold sparseExceptionDirectoryOverhead
  simpa [Nat.add_assoc] using
    (((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO
        flagSlots).add
      (SuccinctSpace.sampledDirectoryOverhead_littleO
        rankSuperSlots)).add
      (SuccinctSpace.sampledDirectoryOverhead_littleO
        rankBlockSlots)).add
      (SuccinctSpace.idDivLogLogOverhead_littleO explicitSlots)

def canonicalSparseExceptionDirectoryOverhead (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) + 16) +
      sparseExceptionRelativeTableOverhead n

theorem canonicalSparseExceptionDirectoryOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalSparseExceptionDirectoryOverhead := by
  unfold canonicalSparseExceptionDirectoryOverhead
  have hflags :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40
            (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192
            (2 * n) + 16) :=
    ((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192)
      |>.comp_two_mul_arg).add_const 16
  exact (hflags.add hrank).add sparseExceptionRelativeTableOverhead_littleO

theorem fixedWidthNatTable_word_length_le_of_mem
    {entries : List Nat} {width n : Nat}
    (table : SuccinctSpace.FixedWidthNatTable entries width)
    (hwidth : width <= SuccinctRankProposal.machineWordBits n)
    {word : List Bool}
    (hmem : List.Mem word table.store.words.toList) :
    word.length <= SuccinctRankProposal.machineWordBits n := by
  rcases (List.mem_iff_getElem?.mp hmem) with ⟨i, hgetList⟩
  have hget : table.store.words[i]? = some word := by
    simpa [Array.getElem?_toList] using hgetList
  rw [table.read_word_length_of_some hget]
  exact hwidth

structure RelativeSplitSparseExceptionDirectory
    (shape : Cartesian.CartesianShape)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  localStride : Nat
  localStride_pos : 0 < localStride
  flagBits : List Bool
  rankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      flagBits rankSuperOverhead rankBlockOverhead 4
  relativeEntries : List Nat
  relativeWidth : Nat
  relativeTable :
    SuccinctSpace.FixedWidthNatTable relativeEntries relativeWidth
  rank_wordSize_le_machine :
    rankData.wordSize <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  rank_superWidth_le_machine :
    rankData.superWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  rank_blockWidth_le_machine :
    rankData.blockWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  relativeWidth_le_machine :
    relativeWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  payload_length_le_overhead :
    flagBits.length + rankData.auxPayload.length +
        relativeTable.payload.length <=
      canonicalSparseExceptionDirectoryOverhead shape.size

namespace RelativeSplitSparseExceptionDirectory

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  directory.flagBits ++ directory.rankData.auxPayload ++
    directory.relativeTable.payload

theorem payload_length_le_canonical
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
      canonicalSparseExceptionDirectoryOverhead shape.size := by
  simpa [payload, Nat.add_assoc] using
    directory.payload_length_le_overhead

def readWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  directory.rankData.superTables.trueTable.store.words.toList ++
    directory.rankData.superTables.falseTable.store.words.toList ++
      directory.rankData.blockTables.trueTable.store.words.toList ++
        directory.rankData.blockTables.falseTable.store.words.toList ++
          directory.rankData.bitWords.store.words.toList ++
            directory.relativeTable.store.words.toList

def readCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.rankData.rankCosted true localSlot)
    fun exceptionRank =>
      relativeOffsetReadCosted directory.relativeTable base
        (relativeSplitFalseSelectSparseCompactSlot
          exceptionRank localOccurrence directory.localStride)

theorem readCosted_cost_le_five
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).cost <= 5 := by
  unfold readCosted relativeOffsetReadCosted
  have hrank :=
    directory.rankData.rankCosted_cost_le_four true localSlot
  have hrelative :=
    directory.relativeTable.readCosted_cost_le_one
      (relativeSplitFalseSelectSparseCompactSlot
        (directory.rankData.rankCosted true localSlot).value
        localOccurrence directory.localStride)
  simp [Costed.bind, Costed.map] at *
  omega

theorem readCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    (base localSlot localOccurrence : Nat) :
    (directory.readCosted base localSlot localOccurrence).erase =
      (directory.relativeEntries[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
            localOccurrence directory.localStride]?).map
        (fun offset => base + offset) := by
  have hrank :=
    directory.rankData.rankCosted_exact true localSlot
  change (directory.rankData.rankCosted true localSlot).value =
      RMQ.Succinct.rankPrefix true directory.flagBits localSlot at hrank
  let slot :=
    relativeSplitFalseSelectSparseCompactSlot
      (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
      localOccurrence directory.localStride
  have hread :
      (directory.relativeTable.readCosted slot).value =
        directory.relativeEntries[slot]? := by
    simpa [Costed.erase] using
      directory.relativeTable.readCosted_erase slot
  unfold readCosted relativeOffsetReadCosted
  simp [Costed.bind, Costed.map, Costed.erase, hrank, slot, hread]

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word directory.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  rw [readWords] at hmem
  rcases List.mem_append.mp hmem with hprefix0 | hrelative
  · rcases List.mem_append.mp hprefix0 with hprefix1 | hflagWord
    · rcases List.mem_append.mp hprefix1 with hprefix2 | hblockFalse
      · rcases List.mem_append.mp hprefix2 with hprefix3 | hblockTrue
        · rcases List.mem_append.mp hprefix3 with hsuperTrue | hsuperFalse
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.trueTable
                directory.rank_superWidth_le_machine hsuperTrue
          · exact
              fixedWidthNatTable_word_length_le_of_mem
                directory.rankData.superTables.falseTable
                directory.rank_superWidth_le_machine hsuperFalse
        · exact
            fixedWidthNatTable_word_length_le_of_mem
              directory.rankData.blockTables.trueTable
              directory.rank_blockWidth_le_machine hblockTrue
      · exact
          fixedWidthNatTable_word_length_le_of_mem
            directory.rankData.blockTables.falseTable
            directory.rank_blockWidth_le_machine hblockFalse
    · exact Nat.le_trans
        (directory.rankData.bitWords.word_length_le hflagWord)
        directory.rank_wordSize_le_machine
  · exact
      fixedWidthNatTable_word_length_le_of_mem
        directory.relativeTable
        directory.relativeWidth_le_machine hrelative

theorem profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (directory :
      RelativeSplitSparseExceptionDirectory
        shape rankSuperOverhead rankBlockOverhead) :
    directory.payload.length <=
        canonicalSparseExceptionDirectoryOverhead shape.size /\
      (forall base localSlot localOccurrence,
        (directory.readCosted
          base localSlot localOccurrence).cost <= 5) /\
      (forall base localSlot localOccurrence,
        (directory.readCosted base localSlot localOccurrence).erase =
          (directory.relativeEntries[
              relativeSplitFalseSelectSparseCompactSlot
                (RMQ.Succinct.rankPrefix true directory.flagBits localSlot)
                localOccurrence directory.localStride]?).map
            (fun offset => base + offset)) /\
      forall {word : List Bool},
        List.Mem word directory.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨directory.payload_length_le_canonical,
      directory.readCosted_cost_le_five,
      directory.readCosted_exact,
      fun {word} hmem => directory.read_words_length_le_machine hmem⟩

end RelativeSplitSparseExceptionDirectory

def builtRelativeSplitSparseExceptionDirectory
    (shape : Cartesian.CartesianShape) :
    RelativeSplitSparseExceptionDirectory
      shape
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankSuperOverhead
        shape)
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankBlockOverhead
        shape) where
  localStride := sparseDenseFalseSelectLocalStride shape
  localStride_pos := sparseDenseFalseSelectLocalStride_pos shape
  flagBits :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits shape
  rankData :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData shape
  relativeEntries :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries shape
  relativeWidth :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth shape
  relativeTable :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeTable shape
  rank_wordSize_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.1
  rank_superWidth_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.2.1
  rank_blockWidth_le_machine := by
    exact
      (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_profile
        shape).2.2.2.1
  relativeWidth_le_machine :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeWidth_le_machine shape
  payload_length_le_overhead := by
    have hflags :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_length_le_overhead
        shape
    have hrank :=
      builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagRankData_auxPayload_le_overhead
        shape
    have hrelative :=
      builtRelativeSplitFalseSelectSparseExceptionRelativeTable_payload_le_overhead
        shape
    have hbp : shape.bpCode.length = 2 * shape.size :=
      Cartesian.CartesianShape.bpCode_length shape
    simp [canonicalSparseExceptionDirectoryOverhead,
      hbp] at hflags hrank hrelative ⊢
    omega

def canonicalRelativeSplitSparseExceptionFalseSelectOverhead
    (n : Nat) : Nat :=
  SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
    SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n) +
      (SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) + 16) +
        compactLongSuperRelativeTableOverhead n +
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 (2 * n) +
            canonicalSparseExceptionDirectoryOverhead n

theorem canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead := by
  unfold canonicalRelativeSplitSparseExceptionFalseSelectOverhead
  have hsuper :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hflags :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 40 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 40)
      |>.comp_two_mul_arg
  have hrank :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 192 (2 * n) +
            16) :=
    ((SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 192)
      |>.comp_two_mul_arg).add_const 16
  have hlocal :
      SuccinctSpace.LittleOLinear
        (fun n =>
          SuccinctSpace.logLogCubedSampledDirectoryOverhead 640 (2 * n)) :=
    (SuccinctSpace.logLogCubedSampledDirectoryOverhead_littleO 640)
      |>.comp_two_mul_arg
  exact
    (((((hsuper.add hflags).add hrank).add
      compactLongSuperRelativeTableOverhead_littleO).add hlocal).add
      canonicalSparseExceptionDirectoryOverhead_littleO)

structure RelativeSplitSparseExceptionFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (rankSuperOverhead rankBlockOverhead : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits shape.bpCode.length
  superStride : Nat
  superStride_pos : 0 < superStride
  localStride : Nat
  localStride_pos : 0 < localStride
  localSlotsPerSuper : Nat
  superEntries : List SparseDenseFalseSelectDenseLocalEntry
  longFlagBits : List Bool
  longFlagBits_eq :
    longFlagBits = relativeSplitFalseSelectLongFlagBits superEntries
  longFlagRankSuperOverhead : Nat
  longFlagRankBlockOverhead : Nat
  longFlagRankData :
    SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData
      longFlagBits longFlagRankSuperOverhead longFlagRankBlockOverhead 4
  longFlagRank_wordSize_le_machine :
    longFlagRankData.wordSize <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longFlagRank_superWidth_le_machine :
    longFlagRankData.superWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longFlagRank_blockWidth_le_machine :
    longFlagRankData.blockWidth <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length
  longSuperRelativeEntries : List Nat
  localEntries : List SparseDenseFalseSelectDenseLocalEntry
  superFieldWidth : Nat
  longSuperRelativeWidth : Nat
  localFieldWidth : Nat
  superTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      superEntries superFieldWidth
  longSuperRelativeTable :
    SuccinctSpace.FixedWidthNatTable
      longSuperRelativeEntries longSuperRelativeWidth
  localTable :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable
      localEntries localFieldWidth
  sparseDirectory :
    RelativeSplitSparseExceptionDirectory
      shape rankSuperOverhead rankBlockOverhead
  bitWords : SuccinctSpace.BoundedPayloadWordStore shape.bpCode wordSize
  super_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      superTable shape.bpCode.length
  long_read_words_length_le_machine :
    forall {i : Nat} {word : List Bool},
      longSuperRelativeTable.store.words[i]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length
  local_read_words_length_le_machine :
    FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.ReadWordsLengthLeMachine
      localTable shape.bpCode.length
  payload_length_le_overhead :
    (superTable.payload ++ longFlagBits ++
      longFlagRankData.auxPayload ++ longSuperRelativeTable.payload ++
        localTable.payload ++ sparseDirectory.payload).length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size
  super_missing_exact :
    forall q,
      superEntries[falseSelectSuperSlot q superStride]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  long_explicit_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = true ->
        (longSuperRelativeEntries[
            relativeSplitFalseSelectLongCompactSlot
              (RMQ.Succinct.rankPrefix true longFlagBits
                (falseSelectSuperSlot q superStride))
              (q - super.baseOccurrence) superStride]?).map
          (fun offset =>
            relativeSplitFalseSelectEntryBasePosition wordSize super +
              offset) =
          RMQ.Succinct.select false shape.bpCode q
  local_missing_exact :
    forall q super,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = none ->
        RMQ.Succinct.select false shape.bpCode q = none
  sparse_compact_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = true ->
        (sparseDirectory.readCosted
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super)
          (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
          RMQ.Succinct.select false shape.bpCode q
  dense_exact :
    forall q super loc,
      superEntries[falseSelectSuperSlot q superStride]? = some super ->
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length ->
      relativeSplitFalseSelectEntryIsMarked super = false ->
      localEntries[
          relativeSplitFalseSelectLocalSlot q superStride
            localSlotsPerSuper localStride super]? = some loc ->
      relativeSplitFalseSelectEntryIsMarked loc = false ->
        (denseTwoWordFalseSelectCosted bitWords
          (relativeSplitFalseSelectLocalBasePosition wordSize super loc)
          (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
          RMQ.Succinct.select false shape.bpCode q

namespace RelativeSplitSparseExceptionFalseSelectCloseData

def payload
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List Bool :=
  data.superTable.payload ++ data.longFlagBits ++
    data.longFlagRankData.auxPayload ++
      data.longSuperRelativeTable.payload ++
        data.localTable.payload ++ data.sparseDirectory.payload

def longFlagRankReadWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  (((data.longFlagRankData.superTables.trueTable.store.words.toList ++
      data.longFlagRankData.superTables.falseTable.store.words.toList) ++
    data.longFlagRankData.blockTables.trueTable.store.words.toList ++
      data.longFlagRankData.blockTables.falseTable.store.words.toList) ++
        data.longFlagRankData.bitWords.store.words.toList)

def readWords
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    List (List Bool) :=
  data.superTable.readWords ++
    data.longFlagRankReadWords ++
      data.longSuperRelativeTable.store.words.toList ++
        data.localTable.readWords ++
          data.sparseDirectory.readWords ++
            data.bitWords.store.words.toList

def queryOccurrence
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (_data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Nat :=
  idx

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  let q := data.queryOccurrence idx
  if idx < shape.size then
    Costed.bind
      (data.superTable.readCosted
        (falseSelectSuperSlot q data.superStride)) fun super? =>
      match super? with
      | none => Costed.pure none
      | some super =>
          if relativeSplitFalseSelectEntryIsMarked super then
            Costed.bind
              (data.longFlagRankData.rankCosted true
                (falseSelectSuperSlot q data.superStride))
              fun exceptionRank =>
                relativeOffsetReadCosted data.longSuperRelativeTable
                  (relativeSplitFalseSelectEntryBasePosition
                    data.wordSize super)
                  (relativeSplitFalseSelectLongCompactSlot
                    exceptionRank (q - super.baseOccurrence)
                    data.superStride)
          else
            let localSlot :=
              relativeSplitFalseSelectLocalSlot q data.superStride
                data.localSlotsPerSuper data.localStride super
            Costed.bind (data.localTable.readCosted localSlot) fun loc? =>
              match loc? with
              | none => Costed.pure none
              | some loc =>
                  if relativeSplitFalseSelectEntryIsMarked loc then
                    data.sparseDirectory.readCosted
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      localSlot
                      (q -
                        relativeSplitFalseSelectLocalBaseOccurrence
                          super loc)
                  else
                    denseTwoWordFalseSelectCosted data.bitWords
                      (relativeSplitFalseSelectLocalBasePosition
                        data.wordSize super loc)
                      (relativeSplitFalseSelectLocalBaseOccurrence
                        super loc)
                      q
  else
    Costed.pure none

theorem payload_length_le_canonical
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    data.payload.length <=
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead
        shape.size := by
  simpa [payload] using data.payload_length_le_overhead

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCloseCosted idx).cost <=
      sparseDenseFalseSelectQueryCost := by
  unfold selectCloseCosted queryOccurrence sparseDenseFalseSelectQueryCost
  by_cases hvalid : idx < shape.size
  case pos =>
    cases hsuperValue :
        (data.superTable.readCosted
          (falseSelectSuperSlot
            idx data.superStride)).value with
    | none =>
        simp [Costed.bind, Costed.pure, hvalid, hsuperValue] <;> omega
    | some super =>
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrankCost :=
            data.longFlagRankData.rankCosted_cost_le true
              (falseSelectSuperSlot
                idx data.superStride)
          have hlongCost :
              (data.longSuperRelativeTable.readCosted
                (relativeSplitFalseSelectLongCompactSlot
                  (data.longFlagRankData.rankCosted true
                    (falseSelectSuperSlot
                      idx data.superStride)).value
                  (idx - super.baseOccurrence)
                  data.superStride)).cost <= 1 := by
            exact data.longSuperRelativeTable.readCosted_cost_le_one _
          simp [relativeOffsetReadCosted, Costed.bind, Costed.map,
            Costed.pure, hvalid, hsuperValue, hlong] <;> omega
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          cases hlocalValue :
              (data.localTable.readCosted localSlot).value with
          | none =>
              simp [Costed.bind, Costed.pure, hvalid, hsuperValue, hlong,
                localSlot, hlocalValue] <;> omega
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                have hsparseCost :
                  (data.sparseDirectory.readCosted
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalSlot
                      idx data.superStride
                      data.localSlotsPerSuper data.localStride super)
                    (idx -
                      relativeSplitFalseSelectLocalBaseOccurrence super loc)).cost
                      <= 5 := by
                  simpa [localSlot] using
                    data.sparseDirectory.readCosted_cost_le_five
                      (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                      localSlot
                      (idx -
                        relativeSplitFalseSelectLocalBaseOccurrence super loc)
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
              case neg =>
                have hdenseCost :=
                  denseTwoWordFalseSelectCosted_cost_le_five
                    data.bitWords
                    (relativeSplitFalseSelectLocalBasePosition
                      data.wordSize super loc)
                    (relativeSplitFalseSelectLocalBaseOccurrence super loc)
                    idx
                simp [Costed.bind, hvalid, hsuperValue, hlong, localSlot,
                  hlocalValue, hsparse] <;> omega
  case neg =>
    simp [Costed.pure, hvalid]

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) (idx : Nat) :
    (data.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  let q := idx
  have hclamp :
      RMQ.Succinct.select false shape.bpCode q =
        SuccinctSpace.bpCloseOfInorder? shape idx := by
    simpa [q] using
      SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx
  unfold selectCloseCosted queryOccurrence
  dsimp only
  by_cases hvalid : idx < shape.size
  case pos =>
    have hvalidQ :
        q < RMQ.Succinct.rankPrefix false shape.bpCode
          shape.bpCode.length := by
      simpa [q, SuccinctSpace.bpCode_rankFalse_full] using hvalid
    cases hsuper :
        data.superEntries[
          falseSelectSuperSlot
            idx data.superStride]? with
    | none =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              none := by
          simpa [q] using hsuper
        simp [hvalid, hsuper, Costed.erase_bind,
          FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
        rw [<- hclamp]
        exact (data.super_missing_exact q hsuperQ).symm
    | some super =>
        have hsuperQ :
            data.superEntries[
                falseSelectSuperSlot q data.superStride]? =
              some super := by
          simpa [q] using hsuper
        by_cases hlong :
            relativeSplitFalseSelectEntryIsMarked super = true
        case pos =>
          have hrank :=
            data.longFlagRankData.rankCosted_exact true
              (falseSelectSuperSlot
                idx data.superStride)
          simp [hvalid, hsuper, hlong, relativeOffsetReadCosted,
            Costed.erase_bind, Costed.erase_map,
            FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase,
            SuccinctSpace.FixedWidthNatTable.readCosted_erase, hrank]
          rw [<- hclamp]
          simpa [q] using
            data.long_explicit_exact q super hsuperQ hvalidQ hlong
        case neg =>
          let localSlot :=
            relativeSplitFalseSelectLocalSlot
              idx data.superStride
              data.localSlotsPerSuper data.localStride super
          have hlongFalse :
              relativeSplitFalseSelectEntryIsMarked super = false := by
            cases hmark : relativeSplitFalseSelectEntryIsMarked super
            case false =>
              rfl
            case true =>
              exact False.elim (hlong hmark)
          cases hlocal :
              data.localEntries[localSlot]? with
          | none =>
              simp [hvalid, hsuper, hlong, localSlot, hlocal,
                Costed.erase_bind,
                FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
              have hlocal' :
                data.localEntries[
                    relativeSplitFalseSelectLocalSlot q data.superStride
                      data.localSlotsPerSuper data.localStride super]? =
                  none := by
                simpa [q, localSlot] using hlocal
              rw [<- hclamp]
              exact (data.local_missing_exact q super hsuperQ hvalidQ hlongFalse
                hlocal').symm
          | some loc =>
              by_cases hsparse :
                  relativeSplitFalseSelectEntryIsMarked loc = true
              case pos =>
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                rw [<- hclamp]
                simpa [q] using
                  data.sparse_compact_exact q super loc hsuperQ hvalidQ
                    hlongFalse hlocal' hsparse
              case neg =>
                have hsparseFalse :
                    relativeSplitFalseSelectEntryIsMarked loc = false := by
                  cases hmark : relativeSplitFalseSelectEntryIsMarked loc
                  case false =>
                    rfl
                  case true =>
                    exact False.elim (hsparse hmark)
                simp [hvalid, hsuper, hlong, localSlot, hlocal,
                  Costed.erase_bind,
                  FixedWidthSparseDenseFalseSelectDenseLocalEntryTable.readCosted_erase]
                have hlocal' :
                    data.localEntries[
                        relativeSplitFalseSelectLocalSlot q data.superStride
                        data.localSlotsPerSuper data.localStride super]? =
                      some loc := by
                  simpa [q, localSlot] using hlocal
                simp [hsparse]
                rw [<- hclamp]
                simpa [q] using
                  data.dense_exact q super loc hsuperQ hvalidQ hlongFalse
                    hlocal' hsparseFalse
  case neg =>
    have hnotQ :
        ¬ q < RMQ.Succinct.rankPrefix false shape.bpCode
          shape.bpCode.length := by
      simpa [q, SuccinctSpace.bpCode_rankFalse_full] using hvalid
    simp [hvalid, Costed.pure]
    rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]
    exact
      (select_none_of_rankPrefix_length_le
        (target := false) (bits := shape.bpCode) (occurrence := idx)
        (by
          rw [SuccinctSpace.bpCode_rankFalse_full]
          omega)).symm

theorem longFlagRank_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.longFlagRankReadWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    (hmem : List.Mem word data.readWords) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
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
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨data.payload_length_le_canonical,
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO,
      data.selectCloseCosted_cost_le,
      data.selectCloseCosted_exact,
      fun {word} hmem => data.read_word_length_le_machine hmem⟩

def toChargedSelectPositionSource
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead) :
    ChargedSelectPositionSource false shape.bpCode
      canonicalRelativeSplitSparseExceptionFalseSelectOverhead
      sparseDenseFalseSelectQueryCost where
  domainSize := shape.size
  payload := data.payload
  readWords := data.readWords
  selectPositionCosted := data.selectCloseCosted
  payload_length_le := data.payload_length_le_canonical
  overhead_littleO :=
    canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO
  selectPositionCosted_cost_le := data.selectCloseCosted_cost_le
  selectPositionCosted_exact := by
    intro idx
    rw [data.selectCloseCosted_exact idx]
    rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]
  read_word_length_le_machine := by
    intro word hmem
    exact data.read_word_length_le_machine hmem

def relativeSplitDescriptorIndexCosted
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun pos? =>
      pos?.map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos))
    (data.selectCloseCosted idx)

theorem relativeSplitDescriptorIndexCosted_eq_chargedSource
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    data.relativeSplitDescriptorIndexCosted idx =
      (data.toChargedSelectPositionSource.descriptorIndexCosted
        data.wordSize idx) := by
  rfl

theorem toChargedSelectPositionSource_descriptorIndexCosted_profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk : Nat}
    (hchunk : 0 < occurrencesPerChunk) :
    let source := data.toChargedSelectPositionSource
    source.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead
          source.domainSize /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (source.descriptorIndexCosted data.wordSize idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (source.descriptorIndexCosted data.wordSize idx).erase =
          (RMQ.Succinct.select false shape.bpCode idx).map
            (fun pos =>
              clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos)) /\
      (forall {idx descriptorIndex : Nat},
        (source.descriptorIndexCosted data.wordSize idx).erase =
          some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
            descriptorIndex occurrencesPerChunk idx) /\
      forall {word : List Bool},
        List.Mem word source.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro source
  exact
    source.descriptorIndexCosted_profile data.wordSize_pos hchunk

theorem relativeSplitDescriptorIndexCosted_table_backed_sample_exact
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {word : List Bool}
    {fieldWidth count occurrencesPerChunk idx pos descriptorIndex
      firstWordCount : Nat}
    (hfield : data.wordSize < 2 ^ fieldWidth)
    (hchunk : 0 < occurrencesPerChunk)
    (hdescriptorRead :
      (data.relativeSplitDescriptorIndexCosted idx).erase =
        some descriptorIndex)
    (hfirstRead :
      ((twoWordDescriptorFirstCountTables
          shape.bpCode data.wordSize fieldWidth count hfield).sampleCosted
          false descriptorIndex).erase = some firstWordCount)
    (hselect : RMQ.Succinct.select false shape.bpCode idx = some pos)
    (hword :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          shape.bpCode data.wordSize_pos).store.words[
            (clarkSelectTwoWordDescriptorSample false shape.bpCode
              data.wordSize descriptorIndex firstWordCount idx).wordIndex]? =
        some word) :
    SelectSampleWordExact false shape.bpCode idx
      (clarkSelectTwoWordDescriptorSample false shape.bpCode data.wordSize
        descriptorIndex firstWordCount idx) word := by
  rw [relativeSplitDescriptorIndexCosted_eq_chargedSource] at hdescriptorRead
  exact
    data.toChargedSelectPositionSource
      |>.descriptorIndexCosted_table_backed_sample_exact
        hfield data.wordSize_pos hchunk hdescriptorRead hfirstRead hselect
        hword

theorem relativeSplitDescriptorIndexCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    (data.relativeSplitDescriptorIndexCosted idx).cost <=
      sparseDenseFalseSelectQueryCost := by
  rw [relativeSplitDescriptorIndexCosted, Costed.map_cost]
  exact data.selectCloseCosted_cost_le idx

theorem relativeSplitDescriptorIndexCosted_erase
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    (idx : Nat) :
    (data.relativeSplitDescriptorIndexCosted idx).erase =
      (RMQ.Succinct.select false shape.bpCode idx).map
        (fun pos =>
          clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos) := by
  rw [relativeSplitDescriptorIndexCosted, Costed.erase_map]
  rw [data.selectCloseCosted_exact idx]
  rw [<- SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder? shape idx]

theorem relativeSplitDescriptorIndexCosted_covers
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk idx descriptorIndex : Nat}
    (hchunk : 0 < occurrencesPerChunk)
    (hread :
      (data.relativeSplitDescriptorIndexCosted idx).erase =
        some descriptorIndex) :
    ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
      descriptorIndex occurrencesPerChunk idx := by
  rw [relativeSplitDescriptorIndexCosted_erase] at hread
  cases hselect : RMQ.Succinct.select false shape.bpCode idx with
  | none =>
      simp [hselect] at hread
  | some pos =>
      simp [hselect] at hread
      exact
        clarkSelectTwoWordDescriptorIndexOfPos_covers
          (target := false) (bits := shape.bpCode)
          (wordSize := data.wordSize)
          (occurrencesPerChunk := occurrencesPerChunk)
          (occurrence := idx) (pos := pos)
          (descriptorIndex := descriptorIndex)
          data.wordSize_pos hchunk hselect hread.symm

theorem relativeSplitDescriptorIndexCosted_profile
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {occurrencesPerChunk : Nat}
    (hchunk : 0 < occurrencesPerChunk) :
    data.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (data.relativeSplitDescriptorIndexCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.relativeSplitDescriptorIndexCosted idx).erase =
          (RMQ.Succinct.select false shape.bpCode idx).map
            (fun pos =>
              clarkSelectTwoWordDescriptorIndexOfPos data.wordSize pos)) /\
      (forall {idx descriptorIndex : Nat},
        (data.relativeSplitDescriptorIndexCosted idx).erase =
          some descriptorIndex ->
          ClarkSelectTwoWordChunkCovers false shape.bpCode data.wordSize
            descriptorIndex occurrencesPerChunk idx) /\
      forall {word : List Bool},
        List.Mem word data.readWords ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hprofile := data.profile
  exact
    ⟨hprofile.1, hprofile.2.1,
      data.relativeSplitDescriptorIndexCosted_cost_le,
      data.relativeSplitDescriptorIndexCosted_erase,
      fun {idx descriptorIndex} hread =>
        data.relativeSplitDescriptorIndexCosted_covers hchunk hread,
      hprofile.2.2.2.2⟩

theorem long_explicit_slot_lt_length_of_select
    {shape : Cartesian.CartesianShape}
    {rankSuperOverhead rankBlockOverhead : Nat}
    (data :
      RelativeSplitSparseExceptionFalseSelectCloseData
        shape rankSuperOverhead rankBlockOverhead)
    {q pos : Nat} {super : SparseDenseFalseSelectDenseLocalEntry}
    (hsuper :
      data.superEntries[falseSelectSuperSlot q data.superStride]? =
        some super)
    (hlong :
      relativeSplitFalseSelectEntryIsMarked super = true)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    relativeSplitFalseSelectLongCompactSlot
        (RMQ.Succinct.rankPrefix true data.longFlagBits
          (falseSelectSuperSlot q data.superStride))
        (q - super.baseOccurrence) data.superStride <
      data.longSuperRelativeEntries.length := by
  have hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length := by
    have hpos : pos < shape.bpCode.length :=
      RMQ.Succinct.select_bounds hselect
    have hsucc :=
      rankPrefix_succ_of_select
        (target := false) (bits := shape.bpCode)
        (occurrence := q) (pos := pos) hselect
    have hmono :
        RMQ.Succinct.rankPrefix false shape.bpCode (pos + 1) <=
          RMQ.Succinct.rankPrefix false shape.bpCode shape.bpCode.length :=
      RMQ.Succinct.rankPrefix_mono_limit false shape.bpCode (by omega)
    omega
  have hexact :=
    data.long_explicit_exact q super hsuper hvalid hlong
  rw [hselect] at hexact
  cases hentry :
      data.longSuperRelativeEntries[
        relativeSplitFalseSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true data.longFlagBits
            (falseSelectSuperSlot q data.superStride))
          (q - super.baseOccurrence) data.superStride]? with
  | none =>
      simp [hentry] at hexact
  | some offset =>
      exact (List.getElem?_eq_some_iff.mp hentry).1

end RelativeSplitSparseExceptionFalseSelectCloseData

theorem builtRelativeSplitFalseSelectLongSuperFlagBits_eq_relativeSplitLongFlagBits
    (shape : Cartesian.CartesianShape) :
    builtRelativeSplitFalseSelectLongSuperFlagBits shape =
      relativeSplitFalseSelectLongFlagBits
        (builtRelativeSplitFalseSelectSuperEntries shape) := by
  simp [builtRelativeSplitFalseSelectLongSuperFlagBits,
    relativeSplitFalseSelectLongFlagBits,
    builtRelativeSplitFalseSelectSuperEntries, List.map_map,
    Function.comp, builtRelativeSplitFalseSelectSuperEntry_marked_eq_long]

theorem builtRelativeSplitFalseSelectSuperEntries_missing_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (hmissing :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? = none) :
    RMQ.Succinct.select false shape.bpCode q = none := by
  cases hselect :
      RMQ.Succinct.select false shape.bpCode q with
  | none =>
      rfl
  | some pos =>
      have hocc : q < falseSelectOccurrenceCount shape :=
        falseSelect_occurrence_lt_count_of_select shape hselect
      have hslotMul :
          (q / sparseDenseFalseSelectSuperStride shape) *
              sparseDenseFalseSelectSuperStride shape <
            falseSelectOccurrenceCount shape := by
        have hmul :=
          Nat.div_mul_le_self q
            (sparseDenseFalseSelectSuperStride shape)
        omega
      have hslot :
          falseSelectSuperSlot q
              (sparseDenseFalseSelectSuperStride shape) <
            builtRectangularFalseSelectSuperSlotCount shape := by
        unfold falseSelectSuperSlot
          builtRectangularFalseSelectSuperSlotCount
        by_cases hlt :
            q / sparseDenseFalseSelectSuperStride shape <
              falseSelectCeilDiv (falseSelectOccurrenceCount shape)
                (sparseDenseFalseSelectSuperStride shape)
        · exact hlt
        · have hceilLe :
              falseSelectCeilDiv (falseSelectOccurrenceCount shape)
                  (sparseDenseFalseSelectSuperStride shape) <=
                q / sparseDenseFalseSelectSuperStride shape :=
            Nat.le_of_not_gt hlt
          have hmulLe :=
            Nat.mul_le_mul_right
              (sparseDenseFalseSelectSuperStride shape) hceilLe
          have hceilGe :=
            falseSelectCeilDiv_mul_ge_of_pos
              (n := falseSelectOccurrenceCount shape)
              (stride := sparseDenseFalseSelectSuperStride shape)
              (sparseDenseFalseSelectSuperStride_pos shape)
          exact False.elim (by omega)
      have hget :=
        builtRelativeSplitFalseSelectSuperEntries_get?
          shape hslot
      rw [hget] at hmissing
      simp at hmissing

theorem builtRelativeSplitFalseSelectLongExplicit_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? = some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hlong :
      relativeSplitFalseSelectEntryIsMarked super = true) :
    ((builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
        relativeSplitFalseSelectLongCompactSlot
          (RMQ.Succinct.rankPrefix true
            (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
            (falseSelectSuperSlot q
              (sparseDenseFalseSelectSuperStride shape)))
          (q - super.baseOccurrence)
          (sparseDenseFalseSelectSuperStride shape)]?).map
      (fun offset =>
        relativeSplitFalseSelectEntryBasePosition
            (sparseDenseFalseSelectWordBits shape) super +
          offset) =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hslot : superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuilt :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hslot
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hlongBuilt :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = true := by
    have hmark :=
      builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
        shape superSlot
    rw [hmark] at hlong
    exact hlong
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeQ :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot,
      builtRelativeSplitFalseSelectSuperBaseOccurrence] using hmul
  have hqLtBaseStride :
      q <
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt :=
      Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      builtRelativeSplitFalseSelectSuperBaseOccurrence,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hlocalOcc :
      q - builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
        sparseDenseFalseSelectSuperStride shape := by
    omega
  have hend :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape superSlot := by
    have hqEq :
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
            (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) = q := by
      omega
    rw [hqEq]
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hqEqLocal :
      builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
          (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) = q := by
    omega
  have hselectLocal :
      RMQ.Succinct.select false shape.bpCode
          (builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot +
            (q - builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) =
        some pos := by
    simpa [hqEqLocal] using hselect
  have hlookup :=
    compactLongSuperRelativeTable_lookup_exact
      shape (superSlot := superSlot)
      (localOccurrence :=
        q - builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
      (pos := pos) hslot hlongBuilt hlocalOcc hend hselectLocal
  have hbasePos :
      relativeSplitFalseSelectEntryBasePosition
          (sparseDenseFalseSelectWordBits shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) := by
    unfold relativeSplitFalseSelectEntryBasePosition
      builtRelativeSplitFalseSelectSuperEntry
    let baseOccurrence :=
      superSlot * sparseDenseFalseSelectSuperStride shape
    let basePosition :=
      builtRelativeSplitFalseSelectPosition shape baseOccurrence
    let wordSize := sparseDenseFalseSelectWordBits shape
    have hmod :
        basePosition / wordSize * wordSize +
            (basePosition - basePosition / wordSize * wordSize) =
          basePosition := by
      have hle := Nat.div_mul_le_self basePosition wordSize
      omega
    simpa [baseOccurrence, basePosition, wordSize,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hmod
  have hbaseLePos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) <= pos := by
    have hsuperCount :
        builtRelativeSplitFalseSelectSuperBaseOccurrence shape superSlot <
          falseSelectOccurrenceCount shape := by
      omega
    rcases falseSelect_exists_of_lt_occurrence_count
        shape hsuperCount with ⟨basePos, hbaseSelect⟩
    have hmono :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := builtRelativeSplitFalseSelectSuperBaseOccurrence
          shape superSlot)
        (hi := q)
        (posLo := basePos) (posHi := pos)
        hbaseLeQ hbaseSelect hselect
    have hbaseEq :
        builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot) = basePos :=
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
    rwa [hbaseEq]
  have hposEq :
      builtRelativeSplitFalseSelectPosition shape
          (builtRelativeSplitFalseSelectSuperBaseOccurrence
            shape superSlot) +
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRelativeSplitFalseSelectSuperBaseOccurrence
              shape superSlot)) = pos := by
    omega
  have hqueryLookup :
      (builtRelativeSplitFalseSelectLongSuperRelativeEntries shape)[
          relativeSplitFalseSelectLongCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectLongSuperFlagBits shape)
              (falseSelectSuperSlot q
                (sparseDenseFalseSelectSuperStride shape)))
            (q -
              (builtRelativeSplitFalseSelectSuperEntry
                shape superSlot).baseOccurrence)
            (sparseDenseFalseSelectSuperStride shape)]? =
        some
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRelativeSplitFalseSelectSuperBaseOccurrence
                shape superSlot)) := by
    simpa [relativeSplitFalseSelectLongCompactSlot,
      builtRelativeSplitFalseSelectSuperEntry,
      builtRelativeSplitFalseSelectSuperBaseOccurrence, superSlot]
      using hlookup
  rw [hselect]
  rw [hqueryLookup]
  simp [hbasePos, hposEq]

theorem falseSelectCeilDiv_mul_ge
    {n stride : Nat} (hstride : 0 < stride) :
    n <= falseSelectCeilDiv n stride * stride := by
  unfold falseSelectCeilDiv
  cases n with
  | zero =>
      simp
  | succ n =>
      have hleStride : stride <= n + 1 + stride - 1 := by
        omega
      have hlt :
          n + 1 + stride - 1 - stride <
            (n + 1 + stride - 1) / stride * stride :=
        Nat.lt_div_mul_self hstride hleStride
      omega

theorem falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
    {superStride localStride : Nat}
    (hlocal : 0 < localStride) :
    superStride <=
      falseSelectLocalSlotsPerSuper superStride localStride *
        localStride := by
  unfold falseSelectLocalSlotsPerSuper
  cases superStride with
  | zero =>
      simp
  | succ superStride =>
      have hleStride :
          localStride <= superStride + 1 + localStride - 1 := by
        omega
      have hlt :
          superStride + 1 + localStride - 1 - localStride <
            (superStride + 1 + localStride - 1) / localStride *
              localStride :=
        Nat.lt_div_mul_self hlocal hleStride
      omega

theorem nat_add_sub_one_le_mul_of_pos
    {a b : Nat} (ha : 0 < a) (hb : 0 < b) :
    a + b - 1 <= a * b := by
  cases a with
  | zero =>
      omega
  | succ a =>
      cases b with
      | zero =>
          omega
      | succ b =>
          simp [Nat.succ_mul, Nat.mul_succ]
          omega

theorem falseSelectLocalSlotsPerSuper_le_superStride
    {superStride localStride : Nat}
    (hsuper : 0 < superStride) (hlocal : 0 < localStride) :
    falseSelectLocalSlotsPerSuper superStride localStride <=
      superStride := by
  unfold falseSelectLocalSlotsPerSuper
  have hnum :
      superStride + localStride - 1 <=
        superStride * localStride :=
    nat_add_sub_one_le_mul_of_pos hsuper hlocal
  have hlt :
      (superStride + localStride - 1) / localStride <
        superStride + 1 := by
    rw [Nat.div_lt_iff_lt_mul hlocal]
    have hone : 1 <= localStride := by omega
    calc
      superStride + localStride - 1 <=
          superStride * localStride := hnum
      _ < (superStride + 1) * localStride := by
          rw [Nat.add_mul, Nat.one_mul]
          omega
  omega

theorem builtRelativeSplitFalseSelectLocalSlot_facts
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false) :
    let localSlot :=
      relativeSplitFalseSelectLocalSlot q
        (sparseDenseFalseSelectSuperStride shape)
        (builtRectangularFalseSelectLocalSlotsPerSuper shape)
        (sparseDenseFalseSelectLocalStride shape) super
    localSlot < builtRectangularFalseSelectLocalSlotCount shape /\
      localSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape /\
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true /\
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        falseSelectSuperSlot q
          (sparseDenseFalseSelectSuperStride shape) /\
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q /\
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  let slots := builtRectangularFalseSelectLocalSlotsPerSuper shape
  let superStride := sparseDenseFalseSelectSuperStride shape
  let localStride := sparseDenseFalseSelectLocalStride shape
  have hslot : superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuilt :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hslot
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuilt] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  have hshortBuilt :
      builtRelativeSplitFalseSelectSuperIsLong shape superSlot = false := by
    have hmark :=
      builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
        shape superSlot
    rw [hmark] at hshort
    exact hshort
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeQ :
      superSlot * superStride <= q := by
    have hmul := Nat.div_mul_le_self q superStride
    simpa [superSlot, falseSelectSuperSlot, superStride] using hmul
  have hqLtBaseStride :
      q < superSlot * superStride + superStride := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot, superStride,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  let localInSuper := (q - superSlot * superStride) / localStride
  have hlocalStridePos : 0 < localStride := by
    simpa [localStride] using sparseDenseFalseSelectLocalStride_pos shape
  have hslotsPos : 0 < slots := by
    simpa [slots] using
      builtRectangularFalseSelectLocalSlotsPerSuper_pos shape
  have hlocalInSuperLt : localInSuper < slots := by
    by_cases hlt : localInSuper < slots
    case pos =>
      exact hlt
    case neg =>
      have hle : slots <= localInSuper := Nat.le_of_not_gt hlt
      have hslotsMul :
          slots * localStride <= localInSuper * localStride :=
        Nat.mul_le_mul_right localStride hle
      have hdivMul :
          localInSuper * localStride <= q - superSlot * superStride := by
        simpa [localInSuper] using
          Nat.div_mul_le_self (q - superSlot * superStride) localStride
      have hcap :
          superStride <= slots * localStride := by
        simpa [slots, superStride, localStride,
          builtRectangularFalseSelectLocalSlotsPerSuper] using
          (falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
            (superStride := sparseDenseFalseSelectSuperStride shape)
            (localStride := sparseDenseFalseSelectLocalStride shape)
            (sparseDenseFalseSelectLocalStride_pos shape))
      exact False.elim (by omega)
  let localSlot := superSlot * slots + localInSuper
  have hlocalSlotEq :
      relativeSplitFalseSelectLocalSlot q
          (sparseDenseFalseSelectSuperStride shape)
          (builtRectangularFalseSelectLocalSlotsPerSuper shape)
          (sparseDenseFalseSelectLocalStride shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot) =
        localSlot := by
    simp [relativeSplitFalseSelectLocalSlot,
      relativeSplitFalseSelectLocalSlotInSuper,
      builtRelativeSplitFalseSelectSuperEntry, superSlot, slots,
      superStride, localStride, localSlot, localInSuper,
      falseSelectSuperSlot]
  have hlocalSlotLt :
      localSlot < builtRectangularFalseSelectLocalSlotCount shape := by
    have hmul := Nat.mul_lt_mul_of_pos_right hslot hslotsPos
    have hnext :
        superSlot * slots + localInSuper <
          (superSlot + 1) * slots := by
      rw [Nat.add_mul, Nat.one_mul]
      omega
    have hle :
        (superSlot + 1) * slots <=
          builtRectangularFalseSelectSuperSlotCount shape * slots := by
      exact Nat.mul_le_mul_right slots (by omega)
    simpa [localSlot, builtRectangularFalseSelectLocalSlotCount,
      slots, Nat.mul_assoc] using Nat.lt_of_lt_of_le hnext hle
  have hsuperSlotOfLocal :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    unfold builtRelativeSplitFalseSelectLocalSuperSlot
    calc
      (localSlot /
          builtRectangularFalseSelectLocalSlotsPerSuper shape) =
          (localInSuper + slots * superSlot) / slots := by
            simp [localSlot, slots, Nat.mul_comm, Nat.add_comm]
      _ = localInSuper / slots + superSlot := by
            exact Nat.add_mul_div_left localInSuper superSlot hslotsPos
      _ = superSlot := by
            rw [Nat.div_eq_of_lt hlocalInSuperLt]
            simp
  have hlocalRemainder :
      localSlot -
          builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot *
            builtRectangularFalseSelectLocalSlotsPerSuper shape =
        localInSuper := by
    rw [hsuperSlotOfLocal]
    simp [localSlot, slots]
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsuperSlotOfLocal
  have hlocalRemainderRaw :
      localSlot -
          superSlot * builtRectangularFalseSelectLocalSlotsPerSuper shape =
        localInSuper := by
    simpa [hsuperSlotOfLocal] using hlocalRemainder
  have hbaseEq :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot =
        superSlot * superStride + localInSuper * localStride := by
    unfold builtRectangularFalseSelectLocalBaseOccurrence
      builtRectangularFalseSelectLocalSlotInSuperOfGlobal
    rw [hlocalDiv]
    rw [hlocalRemainderRaw]
  have hdivMul :
      localInSuper * localStride <= q - superSlot * superStride := by
    simpa [localInSuper] using
      Nat.div_mul_le_self (q - superSlot * superStride) localStride
  have hbaseLocalLeQ :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    rw [hbaseEq]
    omega
  have hslotsLeSuperStride :
      slots <= superStride := by
    simpa [slots, superStride, localStride,
      builtRectangularFalseSelectLocalSlotsPerSuper] using
      (falseSelectLocalSlotsPerSuper_le_superStride
        (hsuper := sparseDenseFalseSelectSuperStride_pos shape)
        (hlocal := sparseDenseFalseSelectLocalStride_pos shape))
  have hlocalSlotLeBase :
      localSlot <=
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot := by
    have hslotPart :
        superSlot * slots <= superSlot * superStride :=
      Nat.mul_le_mul_left superSlot hslotsLeSuperStride
    have hlocalStrideOne : 1 <= localStride := by omega
    have hlocalPart :
        localInSuper <= localInSuper * localStride := by
      simpa using Nat.mul_le_mul_left localInSuper hlocalStrideOne
    rw [hbaseEq]
    simp [localSlot]
    omega
  have hlocalSlotLtCount :
      localSlot < falseSelectOccurrenceCount shape := by
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hlocalSlotLeBase hbaseLocalLeQ) hoccCount
  have hlocalSlotLtEffective :
      localSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape := by
    unfold builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
    exact Nat.lt_min.mpr ⟨hlocalSlotLt, hlocalSlotLtCount⟩
  have hdeltaLtNext :
      q - superSlot * superStride <
        localInSuper * localStride + localStride := by
    simpa [localInSuper, Nat.add_comm, Nat.add_left_comm,
      Nat.add_assoc] using
      Nat.lt_div_mul_add hlocalStridePos
        (a := q - superSlot * superStride)
  have hqLtLocalEnd :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    rw [hbaseEq]
    simpa [localStride] using (by omega :
      q < superSlot * superStride + localInSuper * localStride +
        localStride)
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  have hlive :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true := by
    unfold builtRelativeSplitFalseSelectCompactLocalEntryIsLive
    simp [hsuperSlotOfLocal, hshortBuilt, hbaseCount]
  rw [hlocalSlotEq]
  exact
    ⟨hlocalSlotLt, hlocalSlotLtEffective, hlive, hsuperSlotOfLocal, hbaseLocalLeQ,
      hqLtLocalEnd⟩

theorem builtRelativeSplitFalseSelectLocalEntries_missing_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hmissing :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        none) :
    RMQ.Succinct.select false shape.bpCode q = none := by
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape) super
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q super hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, _hlive, _hsameSuper,
      _hbaseLe, _hend⟩
  have hget :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hmissingLocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        none := by
    simpa [localSlot] using hmissing
  rw [hget] at hmissingLocal
  cases hmissingLocal

theorem builtRelativeSplitSparseExceptionDirectory_readCosted_lookup_exact
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot localOccurrence pos : Nat}
    (hslot :
      globalLocalSlot < builtRectangularFalseSelectLocalSlotCount shape)
    (heff :
      globalLocalSlot <
        builtRelativeSplitFalseSelectSparseExceptionEffectiveLocalSlotCount
          shape)
    (hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape globalLocalSlot = true)
    (hocc :
      localOccurrence < sparseDenseFalseSelectLocalStride shape)
    (hend :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot + localOccurrence <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape globalLocalSlot))
    (hselect :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot + localOccurrence) =
        some pos) :
    ((builtRelativeSplitSparseExceptionDirectory shape).readCosted
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot localOccurrence).erase =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot))) := by
  have hread :=
    (builtRelativeSplitSparseExceptionDirectory shape).readCosted_exact
      (builtRelativeSplitFalseSelectPosition shape
        (builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot))
      globalLocalSlot localOccurrence
  rw [hread]
  change
    Option.map
      (fun offset =>
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          offset)
      ((builtRelativeSplitFalseSelectSparseExceptionRelativeEntries
          shape)[
          relativeSplitFalseSelectSparseCompactSlot
            (RMQ.Succinct.rankPrefix true
              (builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits
                shape)
              globalLocalSlot)
            localOccurrence
            (sparseDenseFalseSelectLocalStride shape)]?) =
      some
        (builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape globalLocalSlot) +
          (pos -
            builtRelativeSplitFalseSelectPosition shape
              (builtRectangularFalseSelectLocalBaseOccurrence
                shape globalLocalSlot)))
  have hprefix :=
    builtRelativeSplitFalseSelectSparseExceptionEffectiveFlagBits_prefix_eq
      shape (globalLocalSlot := globalLocalSlot) (Nat.le_of_lt heff)
  rw [hprefix]
  have hlookup :=
    builtRelativeSplitFalseSelectSparseExceptionRelativeEntries_lookup_exact
      shape hslot hflag hocc hend hselect
  rw [relativeSplitFalseSelectSparseCompactSlot]
  rw [hlookup]
  rfl

theorem builtRelativeSplitFalseSelectSparseCompact_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        some loc)
    (hsparse :
      relativeSplitFalseSelectEntryIsMarked loc = true) :
    ((builtRelativeSplitSparseExceptionDirectory shape).readCosted
      (relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape) super loc)
      (relativeSplitFalseSelectLocalSlot q
        (sparseDenseFalseSelectSuperStride shape)
        (builtRectangularFalseSelectLocalSlotsPerSuper shape)
        (sparseDenseFalseSelectLocalStride shape) super)
      (q - relativeSplitFalseSelectLocalBaseOccurrence super loc)).erase =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hsuperSlotLt :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuiltSuper :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = builtRelativeSplitFalseSelectLocalEntry shape localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
      shape localSlot
  rw [hmark] at hsparse
  have hflag :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape localSlot = true := by
    have hpair :
        builtRelativeSplitFalseSelectCompactLocalEntryIsLive
            shape localSlot = true /\
          builtRelativeSplitFalseSelectLocalIsSparseException
            shape localSlot = true := by
      simpa using hsparse
    exact hpair.2
  have hsameSuperSlot :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsameSuperSlot
  have hbaseOcc0 :=
    builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
      shape localSlot hlive
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    builtRelativeSplitFalseSelectLocalBasePosition_exact
      shape localSlot hlive
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape)
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    simpa [localSlot] using hqLtLocalEnd
  have hlocalOcc :
      q - builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        sparseDenseFalseSelectLocalStride shape := by
    omega
  have hqEq :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          (q - builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) =
        q := by
    omega
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeSuper :
      superSlot * sparseDenseFalseSelectSuperStride shape <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < builtRelativeSplitFalseSelectSuperEndOccurrence
        shape superSlot := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  have hend :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          (q - builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) <
        builtRelativeSplitFalseSelectSuperEndOccurrence shape
          (builtRelativeSplitFalseSelectLocalSuperSlot
            shape localSlot) := by
    rw [hqEq, hsameSuperSlot]
    exact hqLtSuperEnd
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hselectLocal :
      RMQ.Succinct.select false shape.bpCode
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot +
            (q - builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot)) =
        some pos := by
    simpa [hqEq] using hselect
  have hread :=
    builtRelativeSplitSparseExceptionDirectory_readCosted_lookup_exact
      shape hlocalSlotLt heff hflag hlocalOcc hend hselectLocal
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseLePos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) <= pos := by
    have hmono :=
      select_index_mono (target := false) (bits := shape.bpCode)
        (lo := builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot)
        (hi := q) (posLo := basePos) (posHi := pos)
        hbaseLeLocal hbaseSelect hselect
    have hbaseEqPos :
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot) = basePos :=
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
    rwa [hbaseEqPos]
  have hposEq :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) +
        (pos -
          builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot)) =
        pos := by
    omega
  rw [hselect]
  simpa [localSlot, hbaseOcc, hbasePos, hposEq] using hread

theorem builtRelativeSplitFalseSelect_selected_lt_shortLocalBase_plus_span
    (shape : Cartesian.CartesianShape)
    {globalLocalSlot q pos : Nat}
    (hbaseLe :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape globalLocalSlot <= q)
    (hqEnd :
      q <
        builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape globalLocalSlot)
    (hselect :
      RMQ.Succinct.select false shape.bpCode q = some pos) :
    pos <
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape globalLocalSlot) +
        builtRelativeSplitFalseSelectShortSuperLocalSpan
          shape globalLocalSlot := by
  let base :=
    builtRectangularFalseSelectLocalBaseOccurrence
      shape globalLocalSlot
  let endOcc :=
    builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
      shape globalLocalSlot
  let basePos := builtRelativeSplitFalseSelectPosition shape base
  let lastPos := builtRelativeSplitFalseSelectPosition shape (endOcc - 1)
  have hqCount : q < falseSelectOccurrenceCount shape :=
    falseSelect_occurrence_lt_count_of_select shape hselect
  have hbaseCount : base < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨baseWitness, hbaseSelect⟩
  have hbaseEq :
      basePos = baseWitness := by
    simpa [basePos, base] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hbaseSelect
  have hbaseLePos : baseWitness <= pos :=
    select_index_mono (target := false) (bits := shape.bpCode)
      (lo := base) (hi := q) (posLo := baseWitness)
      (posHi := pos) hbaseLe hbaseSelect hselect
  have hendCount : endOcc <= falseSelectOccurrenceCount shape := by
    simpa [endOcc] using
      builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence_le_count
        shape globalLocalSlot
  have hendPos : 0 < endOcc := by
    omega
  have hlastCount : endOcc - 1 < falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hlastCount with ⟨lastWitness, hlastSelect⟩
  have hlastEq :
      lastPos = lastWitness := by
    simpa [lastPos, endOcc] using
      builtRelativeSplitFalseSelectPosition_eq_of_select
        shape hlastSelect
  have hqLeLast : q <= endOcc - 1 := by
    omega
  have hposLeLast : pos <= lastWitness :=
    select_index_mono (target := false) (bits := shape.bpCode)
      (lo := q) (hi := endOcc - 1) (posLo := pos)
      (posHi := lastWitness) hqLeLast hselect hlastSelect
  unfold builtRelativeSplitFalseSelectShortSuperLocalSpan
  change pos < basePos + (lastPos + 1 - basePos)
  rw [hbaseEq, hlastEq]
  omega

theorem builtRelativeSplitFalseSelectDense_exact
    (shape : Cartesian.CartesianShape) (q : Nat)
    (super loc : SparseDenseFalseSelectDenseLocalEntry)
    (hsuper :
      (builtRelativeSplitFalseSelectSuperEntries shape)[
          falseSelectSuperSlot q
            (sparseDenseFalseSelectSuperStride shape)]? =
        some super)
    (hvalid :
      q < RMQ.Succinct.rankPrefix false shape.bpCode
        shape.bpCode.length)
    (hshort :
      relativeSplitFalseSelectEntryIsMarked super = false)
    (hlocal :
      (builtRelativeSplitFalseSelectLocalEntries shape)[
          relativeSplitFalseSelectLocalSlot q
            (sparseDenseFalseSelectSuperStride shape)
            (builtRectangularFalseSelectLocalSlotsPerSuper shape)
            (sparseDenseFalseSelectLocalStride shape) super]? =
        some loc)
    (hdense :
      relativeSplitFalseSelectEntryIsMarked loc = false) :
    (denseTwoWordFalseSelectCosted
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        shape.bpCode (sparseDenseFalseSelectWordBits_pos shape))
      (relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape) super loc)
      (relativeSplitFalseSelectLocalBaseOccurrence super loc) q).erase =
      RMQ.Succinct.select false shape.bpCode q := by
  let superSlot :=
    falseSelectSuperSlot q (sparseDenseFalseSelectSuperStride shape)
  have hsuperSlotLt :
      superSlot < builtRectangularFalseSelectSuperSlotCount shape := by
    have hlen := (List.getElem?_eq_some_iff.mp hsuper).1
    simpa [superSlot, builtRelativeSplitFalseSelectSuperEntries_length]
      using hlen
  have hbuiltSuper :=
    builtRelativeSplitFalseSelectSuperEntries_get?
      shape (superSlot := superSlot) hsuperSlotLt
  have hsuperEq :
      super = builtRelativeSplitFalseSelectSuperEntry shape superSlot := by
    rw [hbuiltSuper] at hsuper
    exact (Option.some.inj hsuper).symm
  subst super
  let localSlot :=
    relativeSplitFalseSelectLocalSlot q
      (sparseDenseFalseSelectSuperStride shape)
      (builtRectangularFalseSelectLocalSlotsPerSuper shape)
      (sparseDenseFalseSelectLocalStride shape)
      (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
  have hfacts :=
    builtRelativeSplitFalseSelectLocalSlot_facts
      shape q (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
      hsuper hvalid hshort
  rcases hfacts with
    ⟨hlocalSlotLt, _heff, hlive, hsameSuper,
      hbaseLe, hqLtLocalEnd⟩
  have hlocalGet :=
    builtRelativeSplitFalseSelectLocalEntries_get?
      shape (globalLocalSlot := localSlot) hlocalSlotLt
  have hlocalAtSlot :
      (builtRelativeSplitFalseSelectLocalEntries shape)[localSlot]? =
        some loc := by
    simpa [localSlot] using hlocal
  rw [hlocalGet] at hlocalAtSlot
  have hlocEq :
      loc = builtRelativeSplitFalseSelectLocalEntry shape localSlot := by
    exact (Option.some.inj hlocalAtSlot).symm
  subst loc
  have hmark :=
    builtRelativeSplitFalseSelectLocalEntry_marked_eq_flag
      shape localSlot
  rw [hmark] at hdense
  have hliveLocal :
      builtRelativeSplitFalseSelectCompactLocalEntryIsLive
        shape localSlot = true := by
    simpa [localSlot] using hlive
  have hflagFalse :
      builtRelativeSplitFalseSelectLocalIsSparseException
        shape localSlot = false := by
    cases hflag :
        builtRelativeSplitFalseSelectLocalIsSparseException
          shape localSlot
    · rfl
    · have hmarkedTrue :
          (builtRelativeSplitFalseSelectCompactLocalEntryIsLive
              shape localSlot &&
            builtRelativeSplitFalseSelectLocalIsSparseException
              shape localSlot) = true := by
        simp [hliveLocal, hflag]
      rw [hmarkedTrue] at hdense
      cases hdense
  have hsameSuperSlot :
      builtRelativeSplitFalseSelectLocalSuperSlot shape localSlot =
        superSlot := by
    simpa [superSlot] using hsameSuper
  have hlocalDiv :
      localSlot / builtRectangularFalseSelectLocalSlotsPerSuper shape =
        superSlot := by
    simpa [builtRelativeSplitFalseSelectLocalSuperSlot] using
      hsameSuperSlot
  have hbaseOcc0 :=
    builtRelativeSplitFalseSelectLocalBaseOccurrence_exact
      shape localSlot hliveLocal
  have hbaseOcc :
      relativeSplitFalseSelectLocalBaseOccurrence
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot := by
    simpa [hlocalDiv] using hbaseOcc0
  have hbasePos0 :=
    builtRelativeSplitFalseSelectLocalBasePosition_exact
      shape localSlot hliveLocal
  have hbasePos :
      relativeSplitFalseSelectLocalBasePosition
        (sparseDenseFalseSelectWordBits shape)
        (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
        (builtRelativeSplitFalseSelectLocalEntry shape localSlot) =
        builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) := by
    simpa [hlocalDiv] using hbasePos0
  have hbaseLeLocal :
      builtRectangularFalseSelectLocalBaseOccurrence shape localSlot <= q := by
    simpa [localSlot] using hbaseLe
  have hqLtLocalEndLocal :
      q <
        builtRectangularFalseSelectLocalBaseOccurrence shape localSlot +
          sparseDenseFalseSelectLocalStride shape := by
    simpa [localSlot] using hqLtLocalEnd
  have hoccCount : q < falseSelectOccurrenceCount shape := by
    simpa [falseSelectOccurrenceCount] using hvalid
  have hbaseLeSuper :
      superSlot * sparseDenseFalseSelectSuperStride shape <= q := by
    have hmul :=
      Nat.div_mul_le_self q
        (sparseDenseFalseSelectSuperStride shape)
    simpa [superSlot, falseSelectSuperSlot] using hmul
  have hqLtBaseStride :
      q <
        superSlot * sparseDenseFalseSelectSuperStride shape +
          sparseDenseFalseSelectSuperStride shape := by
    have hstride := sparseDenseFalseSelectSuperStride_pos shape
    have hlt := Nat.lt_div_mul_add hstride (a := q)
    simpa [superSlot, falseSelectSuperSlot,
      Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using hlt
  have hqLtSuperEnd :
      q < builtRelativeSplitFalseSelectSuperEndOccurrence
        shape superSlot := by
    unfold builtRelativeSplitFalseSelectSuperEndOccurrence
      builtRelativeSplitFalseSelectSuperBaseOccurrence
    exact Nat.lt_min.mpr ⟨hqLtBaseStride, hoccCount⟩
  have hqLtShortEnd :
      q <
        builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
          shape localSlot := by
    unfold builtRelativeSplitFalseSelectShortSuperLocalEndOccurrence
    exact Nat.lt_min.mpr
      ⟨hqLtLocalEndLocal, by
        simpa [hsameSuperSlot] using hqLtSuperEnd⟩
  have hlocalSpanLeWord :
      builtRelativeSplitFalseSelectShortSuperLocalSpan shape localSlot <=
        sparseDenseFalseSelectWordBits shape := by
    unfold builtRelativeSplitFalseSelectLocalIsSparseException at hflagFalse
    have hshortBuilt :
        builtRelativeSplitFalseSelectSuperIsLong shape superSlot =
          false := by
      have hsuperMark :=
        builtRelativeSplitFalseSelectSuperEntry_marked_eq_long
          shape superSlot
      rw [hsuperMark] at hshort
      exact hshort
    have hshortAtLocal :
        builtRelativeSplitFalseSelectSuperIsLong shape
            (builtRelativeSplitFalseSelectLocalSuperSlot
              shape localSlot) = false := by
      rw [hsameSuperSlot]
      exact hshortBuilt
    rw [hshortAtLocal] at hflagFalse
    simp only [Bool.not_false, Bool.true_and] at hflagFalse
    by_cases hlt :
        sparseDenseFalseSelectWordBits shape <
          builtRelativeSplitFalseSelectShortSuperLocalSpan shape
            localSlot
    · have hdec :
          decide
              (sparseDenseFalseSelectWordBits shape <
                builtRelativeSplitFalseSelectShortSuperLocalSpan
                  shape localSlot) = true := by
        simp [hlt]
      rw [hdec] at hflagFalse
      cases hflagFalse
    · exact Nat.le_of_not_gt hlt
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hoccCount with ⟨pos, hselect⟩
  have hposLtLocalSpan :=
    builtRelativeSplitFalseSelect_selected_lt_shortLocalBase_plus_span
      shape hbaseLeLocal hqLtShortEnd hselect
  have hposSpanBuilt :
      pos <
        builtRelativeSplitFalseSelectPosition shape
            (builtRectangularFalseSelectLocalBaseOccurrence
              shape localSlot) +
          sparseDenseFalseSelectWordBits shape := by
    omega
  have hbaseCount :
      builtRectangularFalseSelectLocalBaseOccurrence
          shape localSlot <
        falseSelectOccurrenceCount shape := by
    omega
  rcases falseSelect_exists_of_lt_occurrence_count
      shape hbaseCount with ⟨basePos, hbaseSelect⟩
  have hbaseEqPos :
      builtRelativeSplitFalseSelectPosition shape
          (builtRectangularFalseSelectLocalBaseOccurrence
            shape localSlot) = basePos :=
    builtRelativeSplitFalseSelectPosition_eq_of_select
      shape hbaseSelect
  have hbaseSelectEntry :
      RMQ.Succinct.select false shape.bpCode
          (relativeSplitFalseSelectLocalBaseOccurrence
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) =
        some
          (relativeSplitFalseSelectLocalBasePosition
            (sparseDenseFalseSelectWordBits shape)
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) := by
    simpa [hbaseOcc, hbasePos, hbaseEqPos] using hbaseSelect
  have hbaseLeEntry :
      relativeSplitFalseSelectLocalBaseOccurrence
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot) <= q := by
    simpa [hbaseOcc] using hbaseLeLocal
  have hposSpanEntry :
      pos <
        relativeSplitFalseSelectLocalBasePosition
            (sparseDenseFalseSelectWordBits shape)
            (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
            (builtRelativeSplitFalseSelectLocalEntry shape localSlot) +
          sparseDenseFalseSelectWordBits shape := by
    simpa [hbasePos] using hposSpanBuilt
  have hdenseFacts :
      FalseSelectDenseLocalPayloadRoutingFacts
        shape.bpCode (sparseDenseFalseSelectWordBits shape)
        (relativeSplitFalseSelectLocalBasePosition
          (sparseDenseFalseSelectWordBits shape)
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot))
        (relativeSplitFalseSelectLocalBaseOccurrence
          (builtRelativeSplitFalseSelectSuperEntry shape superSlot)
          (builtRelativeSplitFalseSelectLocalEntry shape localSlot)) q :=
    falseSelectDenseLocalPayloadRoutingFacts_of_selected_span
      (hwordSize := sparseDenseFalseSelectWordBits_pos shape)
      hbaseSelectEntry hselect hbaseLeEntry hposSpanEntry
  have haligned :
      FalseSelectAlignedBitWords shape.bpCode
        (sparseDenseFalseSelectWordBits shape)
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks
          shape.bpCode (sparseDenseFalseSelectWordBits_pos shape)) :=
    falseSelectAlignedBitWords_ofChunks shape.bpCode
      (sparseDenseFalseSelectWordBits_pos shape)
  simpa [localSlot] using
    denseTwoWordFalseSelectCosted_exact_of_payload_routing_facts
      haligned hdenseFacts

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
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
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
    rw [SuccinctRankProposal.canonicalSuperRankSampleTables_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalSuperRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
        flagLen, rankWord,
        builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalSuperRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalSuperRankEntries, flagBits,
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
    rw [SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length]
    have hentryLen :
        (SuccinctRankProposal.canonicalBlockRankEntries true flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
        flagLen, rankWord]
    have hentryLenFalse :
        (SuccinctRankProposal.canonicalBlockRankEntries false flagBits
            rankWord
            (builtRelativeSplitFalseSelectLongFlagRankBlocksPerSuper
              shape)).length =
          flagLen / rankWord + 1 := by
      simp [SuccinctRankProposal.canonicalBlockRankEntries, flagBits,
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
        SuccinctRankProposal.machineWordBits, n, hnZero]
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
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro data
  exact data.profile

theorem builtRectangularFalseSelectPaddedLocalCapacity_ge_size
    (shape : Cartesian.CartesianShape) :
    shape.size <=
      builtRectangularFalseSelectLocalSlotCount shape *
        sparseDenseFalseSelectLocalStride shape := by
  have hsuperStride :
      0 < sparseDenseFalseSelectSuperStride shape := by
    have hword :
        0 < SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      SuccinctRankProposal.machineWordBits_pos
      shape.bpCode.length
    have hmul :
        0 <
          SuccinctRankProposal.machineWordBits shape.bpCode.length *
            SuccinctRankProposal.machineWordBits shape.bpCode.length :=
      Nat.mul_pos hword hword
    simpa [sparseDenseFalseSelectSuperStride,
      sparseDenseFalseSelectWordBits] using hmul
  have hlocalStride :
      0 < sparseDenseFalseSelectLocalStride shape := by
    unfold sparseDenseFalseSelectLocalStride
    omega
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      (falseSelectCeilDiv_mul_ge
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        hsuperStride)
  have hsuperLocal :
      sparseDenseFalseSelectSuperStride shape <=
        builtRectangularFalseSelectLocalSlotsPerSuper shape *
          sparseDenseFalseSelectLocalStride shape := by
    simpa [builtRectangularFalseSelectLocalSlotsPerSuper] using
      (falseSelectLocalSlotsPerSuper_mul_localStride_ge_superStride
        (superStride := sparseDenseFalseSelectSuperStride shape)
        (localStride := sparseDenseFalseSelectLocalStride shape)
        hlocalStride)
  have hmul :=
    Nat.mul_le_mul_left
      (builtRectangularFalseSelectSuperSlotCount shape) hsuperLocal
  have hcap :
      builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape <=
        builtRectangularFalseSelectLocalSlotCount shape *
          sparseDenseFalseSelectLocalStride shape := by
    simpa [builtRectangularFalseSelectLocalSlotCount,
      Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hmul
  have hsize :
      shape.size = falseSelectOccurrenceCount shape := by
    exact (falseSelectOccurrenceCount_eq_size shape).symm
  omega

theorem builtRectangularFalseSelectPaddedSuperCapacity_ge_size
    (shape : Cartesian.CartesianShape) :
    shape.size <=
      builtRectangularFalseSelectSuperSlotCount shape *
        sparseDenseFalseSelectSuperStride shape := by
  have hocc :
      falseSelectOccurrenceCount shape <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape := by
    simpa [builtRectangularFalseSelectSuperSlotCount] using
      (falseSelectCeilDiv_mul_ge
        (n := falseSelectOccurrenceCount shape)
        (stride := sparseDenseFalseSelectSuperStride shape)
        (sparseDenseFalseSelectSuperStride_pos shape))
  have hsize :
      shape.size = falseSelectOccurrenceCount shape := by
    exact (falseSelectOccurrenceCount_eq_size shape).symm
  omega

def falseSelectRightSpine : Nat -> Cartesian.CartesianShape
  | 0 => Cartesian.CartesianShape.empty
  | n + 1 =>
      Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (falseSelectRightSpine n)

theorem falseSelectRightSpine_shapeOfSize (n : Nat) :
    Cartesian.ShapeOfSize n (falseSelectRightSpine n) := by
  induction n with
  | zero =>
      simp [falseSelectRightSpine]
      exact Cartesian.ShapeOfSize.empty
  | succ n ih =>
      simpa [falseSelectRightSpine, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using
        (Cartesian.ShapeOfSize.node
          (leftSize := 0)
          (rightSize := n)
          Cartesian.ShapeOfSize.empty ih)

theorem padded_relative_sparse_local_entries_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap :=
    builtRectangularFalseSelectPaddedLocalCapacity_ge_size shape
  have hbudget := hbound shape
  have hcombined := Nat.le_trans hcap hbudget
  simpa [hshapeSize] using hcombined

theorem padded_relative_sparse_local_payload_not_littleO
    {overhead : Nat -> Nat} {entryWidth : Nat}
    (hwidth : 0 < entryWidth)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectLocalSlotCount shape *
            sparseDenseFalseSelectLocalStride shape * entryWidth <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  let cellCount :=
    builtRectangularFalseSelectLocalSlotCount shape *
      sparseDenseFalseSelectLocalStride shape
  have hcap :
      shape.size <= cellCount := by
    simpa [cellCount] using
      builtRectangularFalseSelectPaddedLocalCapacity_ge_size shape
  have hwidthOne : 1 <= entryWidth := by
    omega
  have hcells :
      cellCount <= cellCount * entryWidth := by
    simpa using Nat.mul_le_mul_left cellCount hwidthOne
  have hbudget :
      cellCount * entryWidth <= overhead shape.size := by
    simpa [cellCount] using hbound shape
  have hcombined := Nat.le_trans hcap (Nat.le_trans hcells hbudget)
  simpa [hshapeSize] using hcombined

theorem padded_relative_long_super_entries_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap := builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hbudget := hbound shape
  have hcombined := Nat.le_trans hcap hbudget
  simpa [hshapeSize] using hcombined

theorem padded_relative_long_super_payload_not_littleO
    {overhead : Nat -> Nat} {entryWidth : Nat}
    (hwidth : 0 < entryWidth)
    (hbound :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape * entryWidth <=
          overhead shape.size) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  let cellCount :=
    builtRectangularFalseSelectSuperSlotCount shape *
      sparseDenseFalseSelectSuperStride shape
  have hcap :
      shape.size <= cellCount := by
    simpa [cellCount] using
      builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hwidthOne : 1 <= entryWidth := by
    omega
  have hcells :
      cellCount <= cellCount * entryWidth := by
    simpa using Nat.mul_le_mul_left cellCount hwidthOne
  have hbudget :
      cellCount * entryWidth <= overhead shape.size := by
    simpa [cellCount] using hbound shape
  have hcombined := Nat.le_trans hcap (Nat.le_trans hcells hbudget)
  simpa [hshapeSize] using hcombined

theorem relativeSplitSparseException_long_super_padded_payload_not_littleO
    {overhead : Nat -> Nat}
    {rankSuperOverhead rankBlockOverhead :
      Cartesian.CartesianShape -> Nat}
    (builder :
      forall shape : Cartesian.CartesianShape,
        RelativeSplitSparseExceptionFalseSelectCloseData
          shape (rankSuperOverhead shape) (rankBlockOverhead shape))
    (hpadded :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          (builder shape).longSuperRelativeEntries.length)
    (hcharged :
      forall shape : Cartesian.CartesianShape,
        (builder shape).longSuperRelativeTable.payload.length <=
          overhead shape.size)
    (hwidth :
      forall shape : Cartesian.CartesianShape,
        0 < (builder shape).longSuperRelativeWidth) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_self_le
  intro n
  let shape := falseSelectRightSpine n
  let data := builder shape
  have hshapeSize : shape.size = n := by
    exact Cartesian.ShapeOfSize.size_eq
      (falseSelectRightSpine_shapeOfSize n)
  have hcap :
      shape.size <=
        builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape :=
    builtRectangularFalseSelectPaddedSuperCapacity_ge_size shape
  have hpad :
      builtRectangularFalseSelectSuperSlotCount shape *
          sparseDenseFalseSelectSuperStride shape <=
        data.longSuperRelativeEntries.length := by
    simpa [data] using hpadded shape
  have hwidthPos : 0 < data.longSuperRelativeWidth := by
    simpa [data] using hwidth shape
  have hwidthOne : 1 <= data.longSuperRelativeWidth := by
    omega
  have hentriesPayload :
      data.longSuperRelativeEntries.length <=
        data.longSuperRelativeTable.payload.length := by
    calc
      data.longSuperRelativeEntries.length <=
          data.longSuperRelativeEntries.length *
            data.longSuperRelativeWidth := by
        simpa using
          Nat.mul_le_mul_left
            data.longSuperRelativeEntries.length hwidthOne
      _ = data.longSuperRelativeTable.payload.length := by
        exact data.longSuperRelativeTable.payload_length_eq.symm
  have hbudget :
      data.longSuperRelativeTable.payload.length <=
        overhead shape.size := by
    simpa [data] using hcharged shape
  have hcombined :
      shape.size <= overhead shape.size :=
    Nat.le_trans hcap
      (Nat.le_trans hpad (Nat.le_trans hentriesPayload hbudget))
  simpa [hshapeSize] using hcombined

theorem noRelativeSplitSparseExceptionFalseSelectCloseData_with_padded_long_super_payload
    {rankSuperOverhead rankBlockOverhead :
      Cartesian.CartesianShape -> Nat}
    (builder :
      forall shape : Cartesian.CartesianShape,
        RelativeSplitSparseExceptionFalseSelectCloseData
          shape (rankSuperOverhead shape) (rankBlockOverhead shape))
    (hpadded :
      forall shape : Cartesian.CartesianShape,
        builtRectangularFalseSelectSuperSlotCount shape *
            sparseDenseFalseSelectSuperStride shape <=
          (builder shape).longSuperRelativeEntries.length)
    (hwidth :
      forall shape : Cartesian.CartesianShape,
        0 < (builder shape).longSuperRelativeWidth) :
    False := by
  have hnot :
      Not
        (SuccinctSpace.LittleOLinear
          canonicalRelativeSplitSparseExceptionFalseSelectOverhead) := by
    exact
      relativeSplitSparseException_long_super_padded_payload_not_littleO
        (overhead := canonicalRelativeSplitSparseExceptionFalseSelectOverhead)
        (builder := builder)
        hpadded
        (by
          intro shape
          let data := builder shape
          have hlongLePayload :
              data.longSuperRelativeTable.payload.length <=
                (data.superTable.payload ++
                  data.longFlagBits ++
                    data.longFlagRankData.auxPayload ++
                      data.longSuperRelativeTable.payload ++
                        data.localTable.payload ++
                          data.sparseDirectory.payload).length := by
            simp [List.length_append]
            omega
          exact Nat.le_trans hlongLePayload
            data.payload_length_le_overhead)
        hwidth
  exact hnot canonicalRelativeSplitSparseExceptionFalseSelectOverhead_littleO

theorem noBuiltRelativeSplitSparseExceptionFalseSelectCloseData_with_current_long_slot_profile :
    Not
      (exists
        (rankSuperOverhead rankBlockOverhead :
          Cartesian.CartesianShape -> Nat),
        exists builder :
          forall shape : Cartesian.CartesianShape,
            RelativeSplitSparseExceptionFalseSelectCloseData
              shape (rankSuperOverhead shape) (rankBlockOverhead shape),
          (forall shape : Cartesian.CartesianShape,
            builtRectangularFalseSelectSuperSlotCount shape *
                sparseDenseFalseSelectSuperStride shape <=
              (builder shape).longSuperRelativeEntries.length) /\
          (forall shape : Cartesian.CartesianShape,
            0 < (builder shape).longSuperRelativeWidth)) := by
  rintro
    ⟨rankSuperOverhead, rankBlockOverhead, builder,
      hcurrentLongSlotCoverage, hpositiveLongWidth⟩
  exact
    noRelativeSplitSparseExceptionFalseSelectCloseData_with_padded_long_super_payload
      (rankSuperOverhead := rankSuperOverhead)
      (rankBlockOverhead := rankBlockOverhead)
      (builder := builder)
      hcurrentLongSlotCoverage
      hpositiveLongWidth

/-!
### Concrete charged replacement surface

The older rectangular relative-split record and generated rectangular entry
rows were pruned after the compact sparse-exception path superseded them. The
surface below remains as the checked full-width two-level
obstruction/replacement checkpoint for the finite-block-table route.
It consumes concrete two-level stored-word select tables built from
`shape.bpCode`; no close-select function or branch exactness theorem is
supplied externally.
-/

def builtRectangularChargedFalseSelectWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRankProposal.machineWordBits shape.bpCode.length

def builtRectangularChargedFalseSelectOccurrencesPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularChargedFalseSelectWordSize shape

theorem builtRectangularChargedFalseSelectWordSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRectangularChargedFalseSelectWordSize shape := by
  simp [builtRectangularChargedFalseSelectWordSize,
    SuccinctRankProposal.machineWordBits_pos]

theorem builtRectangularChargedFalseSelectOccurrencesPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < builtRectangularChargedFalseSelectOccurrencesPerSuper shape := by
  simpa [builtRectangularChargedFalseSelectOccurrencesPerSuper] using
    builtRectangularChargedFalseSelectWordSize_pos shape

theorem builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ builtRectangularChargedFalseSelectWordSize shape := by
  simpa [builtRectangularChargedFalseSelectWordSize,
    SuccinctRankProposal.machineWordBits] using
    (Nat.lt_log2_self (n := shape.bpCode.length))

def builtRectangularChargedFalseSelectSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (canonicalSelectSuperTablesFinite
      shape.bpCode
      (builtRectangularChargedFalseSelectWordSize shape)
      (builtRectangularChargedFalseSelectOccurrencesPerSuper shape)
      (builtRectangularChargedFalseSelectWordSize shape)
      (builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow
        shape)).payload.length

def builtRectangularChargedFalseSelectBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  (canonicalSelectBlockTablesFinite
      shape.bpCode
      (builtRectangularChargedFalseSelectWordSize shape)
      (builtRectangularChargedFalseSelectOccurrencesPerSuper shape)
      (builtRectangularChargedFalseSelectWordSize shape)
      (builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow
        shape)).payload.length

theorem builtRectangularChargedFalseSelectBlockOverhead_ge_bpCode_length_succ
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length + 1 <=
      builtRectangularChargedFalseSelectBlockOverhead shape := by
  exact
    canonicalSelectBlockTablesFinite_payload_length_ge_succ
      (bits := shape.bpCode)
      (wordSize := builtRectangularChargedFalseSelectWordSize shape)
      (occurrencesPerSuper :=
        builtRectangularChargedFalseSelectOccurrencesPerSuper shape)
      (fieldWidth := builtRectangularChargedFalseSelectWordSize shape)
      (builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow shape)

def builtRectangularChargedFalseSelectSelectData
    (shape : Cartesian.CartesianShape) :
    TwoLevelPayloadLiveStoredWordSelectData shape.bpCode
      (builtRectangularChargedFalseSelectSuperOverhead shape)
      (builtRectangularChargedFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost :=
  canonicalTwoLevelSelectDataOfChunksExact
    shape.bpCode
    (builtRectangularChargedFalseSelectWordSize_pos shape)
    (by
      simp [builtRectangularChargedFalseSelectWordSize])
    (builtRectangularChargedFalseSelectOccurrencesPerSuper_pos shape)
    (builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow shape)
    (builtRectangularChargedFalseSelect_bpCode_length_lt_word_pow shape)
    (by
      unfold sparseDenseFalseSelectQueryCost
      omega)

/--
Historical compatibility name for the generic two-level stored-word
false-select close accessor below.

Despite the old `RectangularCharged` prefix, this construction is not the
rectangular sparse/dense local-table scheme.  It uses the canonical two-level
select tables over `shape.bpCode`; new code and reports should use the
`TwoLevelFalseSelect...` aliases below when referring to this route.
-/
structure RectangularChargedFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (superOverhead blockOverhead queryCost : Nat) where
  selectData :
    TwoLevelPayloadLiveStoredWordSelectData
      shape.bpCode superOverhead blockOverhead queryCost

namespace RectangularChargedFalseSelectCloseData

def payload
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List Bool :=
  data.selectData.auxPayload

def locatorReadWords
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List (List Bool) :=
  (((data.selectData.superTables.trueTable.store.words.toList ++
      data.selectData.superTables.falseTable.store.words.toList) ++
    data.selectData.blockTables.trueTable.store.words.toList) ++
      data.selectData.blockTables.falseTable.store.words.toList)

def readWords
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) : List (List Bool) :=
  data.locatorReadWords ++ data.selectData.bitWords.store.words.toList

def selectCloseCosted
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) : Costed (Option Nat) :=
  data.selectData.selectCosted false idx

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) :
    data.payload.length = superOverhead + blockOverhead := by
  exact data.selectData.auxPayload_length

theorem selectCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) :
    (data.selectCloseCosted idx).cost <= queryCost := by
  exact data.selectData.selectCosted_cost_le false idx

theorem selectCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    (idx : Nat) :
    (data.selectCloseCosted idx).erase =
      SuccinctSpace.bpCloseOfInorder? shape idx := by
  calc
    (data.selectCloseCosted idx).erase =
        RMQ.Succinct.select false shape.bpCode idx := by
      exact data.selectData.selectCosted_exact false idx
    _ = SuccinctSpace.bpCloseOfInorder? shape idx := by
      exact SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?
        shape idx

theorem payload_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost)
    {word : List Bool}
    (hmem :
      List.Mem word data.selectData.bitWords.store.words.toList) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact data.selectData.payload_word_length_le_machine hmem

theorem profile
    {shape : Cartesian.CartesianShape}
    {superOverhead blockOverhead queryCost : Nat}
    (data :
      RectangularChargedFalseSelectCloseData
        shape superOverhead blockOverhead queryCost) :
    data.payload.length = superOverhead + blockOverhead /\
      (forall idx, (data.selectCloseCosted idx).cost <= queryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word data.selectData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    ⟨data.payload_length, data.selectCloseCosted_cost_le,
      data.selectCloseCosted_exact,
      fun {word} hmem => data.payload_word_length_le_machine hmem⟩

end RectangularChargedFalseSelectCloseData

def builtRectangularChargedFalseSelectCloseData
    (shape : Cartesian.CartesianShape) :
    RectangularChargedFalseSelectCloseData shape
      (builtRectangularChargedFalseSelectSuperOverhead shape)
      (builtRectangularChargedFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost where
  selectData := builtRectangularChargedFalseSelectSelectData shape

theorem builtRectangularChargedFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRectangularChargedFalseSelectCloseData shape
    data.payload.length =
        builtRectangularChargedFalseSelectSuperOverhead shape +
          builtRectangularChargedFalseSelectBlockOverhead shape /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word
            data.selectData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact (builtRectangularChargedFalseSelectCloseData shape).profile

abbrev TwoLevelFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (superOverhead blockOverhead queryCost : Nat) :=
  RectangularChargedFalseSelectCloseData
    shape superOverhead blockOverhead queryCost

def builtTwoLevelFalseSelectWordSize
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularChargedFalseSelectWordSize shape

def builtTwoLevelFalseSelectOccurrencesPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularChargedFalseSelectOccurrencesPerSuper shape

def builtTwoLevelFalseSelectSuperOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularChargedFalseSelectSuperOverhead shape

def builtTwoLevelFalseSelectBlockOverhead
    (shape : Cartesian.CartesianShape) : Nat :=
  builtRectangularChargedFalseSelectBlockOverhead shape

def builtTwoLevelFalseSelectSelectData
    (shape : Cartesian.CartesianShape) :
    TwoLevelPayloadLiveStoredWordSelectData shape.bpCode
      (builtTwoLevelFalseSelectSuperOverhead shape)
      (builtTwoLevelFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost :=
  builtRectangularChargedFalseSelectSelectData shape

def builtTwoLevelFalseSelectCloseData
    (shape : Cartesian.CartesianShape) :
    TwoLevelFalseSelectCloseData shape
      (builtTwoLevelFalseSelectSuperOverhead shape)
      (builtTwoLevelFalseSelectBlockOverhead shape)
      sparseDenseFalseSelectQueryCost :=
  builtRectangularChargedFalseSelectCloseData shape

theorem builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length + 1 <=
      builtTwoLevelFalseSelectBlockOverhead shape := by
  exact
    builtRectangularChargedFalseSelectBlockOverhead_ge_bpCode_length_succ
      shape

def builtTwoLevelFalseSelectRightSpineBlockOverhead (n : Nat) : Nat :=
  builtTwoLevelFalseSelectBlockOverhead (falseSelectRightSpine n)

theorem builtTwoLevelFalseSelectRightSpineBlockOverhead_ge_two_n_plus_one
    (n : Nat) :
    2 * n + 1 <=
      builtTwoLevelFalseSelectRightSpineBlockOverhead n := by
  let shape := falseSelectRightSpine n
  have hshape : Cartesian.ShapeOfSize n shape :=
    falseSelectRightSpine_shapeOfSize n
  have hbp : shape.bpCode.length = 2 * n :=
    Cartesian.CartesianShape.bpCode_length_of_shapeOfSize hshape
  have hblock := builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ
    shape
  simpa [builtTwoLevelFalseSelectRightSpineBlockOverhead, shape, hbp] using
    hblock

theorem builtTwoLevelFalseSelect_current_finite_block_tables_not_littleO :
    Not
      (SuccinctSpace.LittleOLinear
        builtTwoLevelFalseSelectRightSpineBlockOverhead) := by
  apply not_littleOLinear_of_self_le
  intro n
  have hlinear :
      n <= 2 * n + 1 := by
    omega
  exact Nat.le_trans hlinear
    (builtTwoLevelFalseSelectRightSpineBlockOverhead_ge_two_n_plus_one n)

theorem builtTwoLevelFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtTwoLevelFalseSelectCloseData shape
    data.payload.length =
        builtTwoLevelFalseSelectSuperOverhead shape +
          builtTwoLevelFalseSelectBlockOverhead shape /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      forall {word : List Bool},
        List.Mem word
            data.selectData.bitWords.store.words.toList ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact builtRectangularChargedFalseSelectCloseData_profile shape

end SuccinctSelectProposal
end RMQ
