import RMQ.Core.SuccinctRankProposal

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

end SuccinctSelectProposal
end RMQ
