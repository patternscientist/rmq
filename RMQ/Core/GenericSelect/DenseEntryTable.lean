import RMQ.Core.GenericSelect.Arithmetic

/-!
# Generic select dense-entry tables

Fixed-width dense-local entry tables and entry-based slot arithmetic.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRankProposal

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


structure SparseDenseSelectDenseLocalEntry where
  baseOccurrence : Nat
  baseWordIndex : Nat
  rankBefore : Nat
  firstOffset : Nat

namespace SparseDenseSelectDenseLocalEntry

def baseOccurrences
    (entries : List SparseDenseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.baseOccurrence)

def baseWordIndices
    (entries : List SparseDenseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.baseWordIndex)

def ranksBefore
    (entries : List SparseDenseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.rankBefore)

def firstOffsets
    (entries : List SparseDenseSelectDenseLocalEntry) : List Nat :=
  entries.map (fun entry => entry.firstOffset)

end SparseDenseSelectDenseLocalEntry

def sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget
    (entries : List SparseDenseSelectDenseLocalEntry)
    (fieldWidth : Nat) : Nat :=
  entries.length * fieldWidth +
    entries.length * fieldWidth +
      entries.length * fieldWidth +
        entries.length * fieldWidth

/--
Multiword fixed-width payload table for dense-local select entries.

Each field is stored in its own fixed-width Nat table. Thus every payload word
is bounded by `fieldWidth`, and `fieldWidth <= machineWordBits n` is sufficient
for machine-word reads; no `4 * fieldWidth <= machineWordBits n` obligation is
introduced.
-/
structure FixedWidthSparseDenseSelectDenseLocalEntryTable
    (entries : List SparseDenseSelectDenseLocalEntry)
    (fieldWidth : Nat) where
  baseOccurrenceTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseSelectDenseLocalEntry.baseOccurrences entries)
      fieldWidth
  baseWordIndexTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseSelectDenseLocalEntry.baseWordIndices entries)
      fieldWidth
  rankBeforeTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseSelectDenseLocalEntry.ranksBefore entries)
      fieldWidth
  firstOffsetTable :
    SuccinctSpace.FixedWidthNatTable
      (SparseDenseSelectDenseLocalEntry.firstOffsets entries)
      fieldWidth

namespace FixedWidthSparseDenseSelectDenseLocalEntryTable

def entryOfFields
    (baseOccurrence baseWordIndex rankBefore firstOffset : Option Nat) :
    Option SparseDenseSelectDenseLocalEntry :=
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
    (entries : List SparseDenseSelectDenseLocalEntry)
    (i : Nat) :
    entryOfFields
        ((SparseDenseSelectDenseLocalEntry.baseOccurrences entries)[i]?)
        ((SparseDenseSelectDenseLocalEntry.baseWordIndices entries)[i]?)
        ((SparseDenseSelectDenseLocalEntry.ranksBefore entries)[i]?)
        ((SparseDenseSelectDenseLocalEntry.firstOffsets entries)[i]?) =
      entries[i]? := by
  induction entries generalizing i with
  | nil =>
      simp [entryOfFields,
        SparseDenseSelectDenseLocalEntry.baseOccurrences,
        SparseDenseSelectDenseLocalEntry.baseWordIndices,
        SparseDenseSelectDenseLocalEntry.ranksBefore,
        SparseDenseSelectDenseLocalEntry.firstOffsets]
  | cons entry rest ih =>
      cases i with
      | zero =>
          rcases entry with
            ⟨baseOccurrence, baseWordIndex, rankBefore, firstOffset⟩
          simp [entryOfFields,
            SparseDenseSelectDenseLocalEntry.baseOccurrences,
            SparseDenseSelectDenseLocalEntry.baseWordIndices,
            SparseDenseSelectDenseLocalEntry.ranksBefore,
            SparseDenseSelectDenseLocalEntry.firstOffsets]
      | succ i =>
          simpa [SparseDenseSelectDenseLocalEntry.baseOccurrences,
            SparseDenseSelectDenseLocalEntry.baseWordIndices,
            SparseDenseSelectDenseLocalEntry.ranksBefore,
            SparseDenseSelectDenseLocalEntry.firstOffsets]
            using ih i

def payload
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth) : List Bool :=
  table.baseOccurrenceTable.payload ++
    table.baseWordIndexTable.payload ++
      table.rankBeforeTable.payload ++
        table.firstOffsetTable.payload

def readWords
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth) : List (List Bool) :=
  table.baseOccurrenceTable.store.words.toList ++
    table.baseWordIndexTable.store.words.toList ++
      table.rankBeforeTable.store.words.toList ++
        table.firstOffsetTable.store.words.toList

def ofEntries
    (entries : List SparseDenseSelectDenseLocalEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseSelectDenseLocalEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.baseWordIndex < 2 ^ fieldWidth /\
              entry.rankBefore < 2 ^ fieldWidth /\
                entry.firstOffset < 2 ^ fieldWidth) :
    FixedWidthSparseDenseSelectDenseLocalEntryTable
      entries fieldWidth where
  baseOccurrenceTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseSelectDenseLocalEntry.baseOccurrences entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).1)
  baseWordIndexTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseSelectDenseLocalEntry.baseWordIndices entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.1)
  rankBeforeTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseSelectDenseLocalEntry.ranksBefore entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.2.1)
  firstOffsetTable :=
    SuccinctSpace.FixedWidthNatTable.ofEntries
      (SparseDenseSelectDenseLocalEntry.firstOffsets entries)
      fieldWidth (by
        intro value hmem
        rcases List.mem_map.mp hmem with ⟨entry, hentry, rfl⟩
        exact (hbound hentry).2.2.2)

def readCosted
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    Costed (Option SparseDenseSelectDenseLocalEntry) :=
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost = 4 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_four
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).cost <= 4 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simpa [readCosted, Costed.erase_bind, Costed.erase_map,
    SuccinctSpace.FixedWidthNatTable.readCosted_erase]
    using entryOfFields_get? entries i

theorem entry_fields_lt
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth)
    {i : Nat} {entry : SparseDenseSelectDenseLocalEntry}
    (hget : entries[i]? = some entry) :
    entry.baseOccurrence < 2 ^ fieldWidth /\
      entry.baseWordIndex < 2 ^ fieldWidth /\
        entry.rankBefore < 2 ^ fieldWidth /\
          entry.firstOffset < 2 ^ fieldWidth := by
  have hbase :
      (SparseDenseSelectDenseLocalEntry.baseOccurrences entries)[i]? =
        some entry.baseOccurrence := by
    simpa [SparseDenseSelectDenseLocalEntry.baseOccurrences,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseSelectDenseLocalEntry =>
          entry.baseOccurrence)) hget
  have hword :
      (SparseDenseSelectDenseLocalEntry.baseWordIndices entries)[i]? =
        some entry.baseWordIndex := by
    simpa [SparseDenseSelectDenseLocalEntry.baseWordIndices,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseSelectDenseLocalEntry =>
          entry.baseWordIndex)) hget
  have hrank :
      (SparseDenseSelectDenseLocalEntry.ranksBefore entries)[i]? =
        some entry.rankBefore := by
    simpa [SparseDenseSelectDenseLocalEntry.ranksBefore,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseSelectDenseLocalEntry =>
          entry.rankBefore)) hget
  have hoffset :
      (SparseDenseSelectDenseLocalEntry.firstOffsets entries)[i]? =
        some entry.firstOffset := by
    simpa [SparseDenseSelectDenseLocalEntry.firstOffsets,
      List.getElem?_map] using congrArg (Option.map
        (fun entry : SparseDenseSelectDenseLocalEntry =>
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth) :
    table.payload.length =
      sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget
        entries fieldWidth := by
  simp [payload,
    sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget,
    SparseDenseSelectDenseLocalEntry.baseOccurrences,
    SparseDenseSelectDenseLocalEntry.baseWordIndices,
    SparseDenseSelectDenseLocalEntry.ranksBefore,
    SparseDenseSelectDenseLocalEntry.firstOffsets,
    SuccinctSpace.FixedWidthNatTable.payload_length, Nat.add_assoc]

def ReadProfile
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth) : Prop :=
  (forall i, (table.baseOccurrenceTable.readCosted i).cost <= 1 /\
    (table.baseOccurrenceTable.readCosted i).erase =
      (SparseDenseSelectDenseLocalEntry.baseOccurrences entries)[i]?) /\
  (forall i, (table.baseWordIndexTable.readCosted i).cost <= 1 /\
    (table.baseWordIndexTable.readCosted i).erase =
      (SparseDenseSelectDenseLocalEntry.baseWordIndices entries)[i]?) /\
  (forall i, (table.rankBeforeTable.readCosted i).cost <= 1 /\
    (table.rankBeforeTable.readCosted i).erase =
      (SparseDenseSelectDenseLocalEntry.ranksBefore entries)[i]?) /\
  (forall i, (table.firstOffsetTable.readCosted i).cost <= 1 /\
    (table.firstOffsetTable.readCosted i).erase =
      (SparseDenseSelectDenseLocalEntry.firstOffsets entries)[i]?) /\
  (forall i, (table.readCosted i).cost <= 4 /\
    (table.readCosted i).erase = entries[i]?)

theorem readProfile
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth n : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth n : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
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
    {entries : List SparseDenseSelectDenseLocalEntry}
    {fieldWidth : Nat}
    (table :
      FixedWidthSparseDenseSelectDenseLocalEntryTable
        entries fieldWidth) :
    table.payload.length =
        sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget
          entries fieldWidth /\
      table.ReadProfile := by
  exact ⟨table.payload_length, table.readProfile⟩

theorem ofEntries_profile
    (entries : List SparseDenseSelectDenseLocalEntry)
    (fieldWidth : Nat)
    (hbound :
      forall {entry : SparseDenseSelectDenseLocalEntry},
        List.Mem entry entries ->
          entry.baseOccurrence < 2 ^ fieldWidth /\
            entry.baseWordIndex < 2 ^ fieldWidth /\
              entry.rankBefore < 2 ^ fieldWidth /\
                entry.firstOffset < 2 ^ fieldWidth) :
    (ofEntries entries fieldWidth hbound).payload.length =
        sparseDenseSelectDenseLocalEntryMultiwordPayloadBudget
          entries fieldWidth /\
      (ofEntries entries fieldWidth hbound).ReadProfile := by
  exact (ofEntries entries fieldWidth hbound).profile

end FixedWidthSparseDenseSelectDenseLocalEntryTable
/-- Local slot within one super interval, measured from the super base
occurrence. -/
def selectLocalSlotInSuper
    (entry : SparseDenseSelectDenseLocalEntry)
    (q localStride : Nat) : Nat :=
  (q - entry.baseOccurrence) / localStride

/-- Rectangular local-table slot for occurrence `q`. -/
def selectLocalSlot
    (q superStride localSlotsPerSuper localStride : Nat)
    (entry : SparseDenseSelectDenseLocalEntry) : Nat :=
  selectSuperSlot q superStride * localSlotsPerSuper +
    selectLocalSlotInSuper entry q localStride

/-- Padded sparse-local explicit slot derived from the rectangular local slot. -/
def selectSparseLocalExplicitSlot
    (localSlot q localStride : Nat)
    (entry : SparseDenseSelectDenseLocalEntry) : Nat :=
  localSlot * localStride + (q - entry.baseOccurrence)
theorem selectCeilDiv_mul_le_add
    (n stride : Nat) :
    selectCeilDiv n stride * stride <= n + stride := by
  unfold selectCeilDiv
  have hdiv :
      ((n + stride - 1) / stride) * stride <=
        n + stride - 1 := Nat.div_mul_le_self _ _
  omega

theorem selectLocalSlotsPerSuper_mul_localStride_le_add
    (superStride localStride : Nat) :
    selectLocalSlotsPerSuper superStride localStride *
        localStride <=
      superStride + localStride := by
  unfold selectLocalSlotsPerSuper
  have hdiv :
      ((superStride + localStride - 1) / localStride) *
          localStride <=
        superStride + localStride - 1 := Nat.div_mul_le_self _ _
  omega


theorem selectCeilDiv_mul_ge_of_pos
    {n stride : Nat} (hstride : 0 < stride) :
    n <= selectCeilDiv n stride * stride := by
  unfold selectCeilDiv
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


theorem selectCeilDiv_slot_mul_lt
    {n stride slot : Nat} (hstride : 0 < stride)
    (hslot : slot < selectCeilDiv n stride) :
    slot * stride < n := by
  unfold selectCeilDiv at hslot
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

theorem selectCeilDiv_le_self_of_pos
    {n stride : Nat} (hn : 0 < n) (hstride : 0 < stride) :
    selectCeilDiv n stride <= n := by
  unfold selectCeilDiv
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


theorem selectCeilDiv_mul_ge
    {n stride : Nat} (hstride : 0 < stride) :
    n <= selectCeilDiv n stride * stride := by
  unfold selectCeilDiv
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

theorem selectLocalSlotsPerSuper_mul_localStride_ge_superStride
    {superStride localStride : Nat}
    (hlocal : 0 < localStride) :
    superStride <=
      selectLocalSlotsPerSuper superStride localStride *
        localStride := by
  unfold selectLocalSlotsPerSuper
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

theorem selectLocalSlotsPerSuper_le_superStride
    {superStride localStride : Nat}
    (hsuper : 0 < superStride) (hlocal : 0 < localStride) :
    selectLocalSlotsPerSuper superStride localStride <=
      superStride := by
  unfold selectLocalSlotsPerSuper
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

end RMQ.GenericSelect
