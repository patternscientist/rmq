import RMQ.Core.SuccinctSelect.TwoLevel.SelectSamples

/-!
# Select word exactness and descriptor obstructions

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal
open SuccinctSpace

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


end SuccinctSelectProposal
end RMQ

