import RMQ.Core.SuccinctSelect.TwoLevel.WordExact

/-!
# Clark select-position source

Split implementation layer for two-level select and rank/select helpers.
Public declarations stay in the historical `RMQ.SuccinctSelectProposal`
namespace until the namespace-alignment cleanup pass.
-/

namespace RMQ
namespace SuccinctSelectProposal
open SuccinctSpace

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
          word.length <= SuccinctRank.machineWordBits bits.length := by
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


end SuccinctSelectProposal
end RMQ

