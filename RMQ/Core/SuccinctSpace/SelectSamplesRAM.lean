import RMQ.Core.SuccinctSpace.SelectSamples
import RMQ.Core.SuccinctSpace.WordStoreRAM

/-!
# Word-RAM interpretation for select-locator sample tables

Select locator tables decode a domain-specific record, so the generic
`WordRAM` core stays independent of them.  This module still makes the payload
read explicit: the decoded table read is a zero-cost map over an interpreted
word read from counted payload memory.
-/

namespace RMQ

namespace SuccinctSpace

namespace FixedWidthSelectSampleTable

/-- A one-segment Word-RAM store for this fixed-width select-sample table. -/
def wordRAMStore
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    RMQ.WordRAM.Store :=
  table.store.wordRAMStore

/--
Interpreted select-sample table read.

The interpreter reads the encoded payload word; the surrounding zero-cost map
performs the table codec.  This keeps the table value tied to payload memory
without making `WordRAM` depend on succinct-select record types.
-/
def readInterpretedCosted
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  Costed.map
    (fun word? => word?.map (bitsToStoredWordSelectSample fieldWidth))
    ((table.store.readProgram i).eval table.wordRAMStore).toCosted

@[simp] theorem readInterpretedCosted_cost
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readInterpretedCosted i).cost = 1 := by
  unfold readInterpretedCosted wordRAMStore
  simp [PayloadWordStore.readProgram, PayloadWordStore.wordRAMStore]

theorem readInterpretedCosted_exact
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readInterpretedCosted i).erase = entries[i]? := by
  unfold readInterpretedCosted wordRAMStore
  change (table.store.words[i]?).map
      (bitsToStoredWordSelectSample fieldWidth) = entries[i]?
  exact table.read_exact i

/-- Interpreted select-sample reads refine the existing costed table read. -/
theorem readInterpretedCosted_refines_readCosted
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    table.readInterpretedCosted i = table.readCosted i := by
  apply Costed.ext
  · simpa [Costed.erase] using
      (table.readInterpretedCosted_exact i).trans
        (table.readCosted_erase i).symm
  · simp

theorem readInterpretedCosted_profile
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    table.payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      forall i,
        (table.readInterpretedCosted i).cost <= 1 /\
          (table.readInterpretedCosted i).erase = entries[i]? := by
  constructor
  · exact table.payload_length
  · intro i
    exact ⟨by
      rw [readInterpretedCosted_cost]
      exact Nat.le_refl 1,
      table.readInterpretedCosted_exact i⟩

theorem wordRAMStore_wordsBounded_of_width_le
    {entries : List (Option StoredWordSelectSample)} {fieldWidth bound : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth)
    (hwidth : selectSampleWordWidth fieldWidth <= bound) :
    table.wordRAMStore.WordsBounded bound := by
  intro segment index word hread
  unfold wordRAMStore PayloadWordStore.wordRAMStore
    RMQ.WordRAM.Store.readWord? at hread
  cases segment with
  | zero =>
      simp at hread
      have hlen : word.length = selectSampleWordWidth fieldWidth :=
        table.word_length_of_get? hread
      omega
  | succ segment =>
      simp at hread

end FixedWidthSelectSampleTable

namespace FixedWidthSelectSampleTables

/-- Interpreted read from the true/false selected sample table. -/
def sampleInterpretedCosted
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  match target with
  | true => tables.trueTable.readInterpretedCosted i
  | false => tables.falseTable.readInterpretedCosted i

@[simp] theorem sampleInterpretedCosted_cost
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleInterpretedCosted target i).cost = 1 := by
  cases target <;> simp [sampleInterpretedCosted]

theorem sampleInterpretedCosted_exact
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleInterpretedCosted target i).erase =
      (tables.entries target)[i]? := by
  cases target <;>
    simp [sampleInterpretedCosted, entries,
      FixedWidthSelectSampleTable.readInterpretedCosted_exact]

theorem sampleInterpretedCosted_refines_sampleCosted
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    tables.sampleInterpretedCosted target i =
      tables.sampleCosted target i := by
  cases target <;>
    simp [sampleInterpretedCosted, sampleCosted,
      FixedWidthSelectSampleTable.readInterpretedCosted_refines_readCosted]

theorem sampleInterpretedCosted_profile
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    tables.payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        (tables.sampleInterpretedCosted target i).cost <= 1 /\
          (tables.sampleInterpretedCosted target i).erase =
            (tables.entries target)[i]? := by
  constructor
  · exact tables.payload_length
  · intro target i
    exact ⟨by
      rw [sampleInterpretedCosted_cost]
      exact Nat.le_refl 1,
      tables.sampleInterpretedCosted_exact target i⟩

end FixedWidthSelectSampleTables

end SuccinctSpace

end RMQ
