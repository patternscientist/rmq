import RMQ.Core.RankSelectSpec
import RMQ.Core.SuccinctRank
import RMQ.Core.GenericSelect.SelectSource

/-!
# Two-level select samples

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
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

end SuccinctSelectProposal
end RMQ

