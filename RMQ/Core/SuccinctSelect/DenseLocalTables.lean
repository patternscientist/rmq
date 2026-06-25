import RMQ.Core.SuccinctSelect.Obstructions
import RMQ.Core.GenericSelect.DenseEntryTable

/-!
# Dense-local false-select tables

This module contains the split multiword dense-local table codec and sampled
select wrapper profiles used by the later sparse/dense false-select close
construction. It keeps the historical `RMQ.SuccinctSelectProposal` namespace.
-/

namespace RMQ
namespace SuccinctSelectProposal

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
    ⟨RMQ.GenericSelect.fixedWidthNatTable_entry_lt_two_pow
        table.baseOccurrenceTable hbase,
      RMQ.GenericSelect.fixedWidthNatTable_entry_lt_two_pow
        table.baseWordIndexTable hword,
      RMQ.GenericSelect.fixedWidthNatTable_entry_lt_two_pow
        table.rankBeforeTable hrank,
      RMQ.GenericSelect.fixedWidthNatTable_entry_lt_two_pow
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
