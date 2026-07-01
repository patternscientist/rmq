import RMQ.Core.SuccinctSpace.Tables
import RMQ.Core.SuccinctSpace.WordStoreRAM

/-!
# Word-RAM interpretation for fixed-width payload tables

The existing tables already read counted payload words and decode them.  This
module makes that execution path explicit by routing reads through the
first-order `WordRAM` interpreter.
-/

namespace RMQ

namespace SuccinctSpace

namespace WordRAMBridge

theorem bitsToNatLE_eq (word : List Bool) :
    RMQ.WordRAM.bitsToNatLE word = bitsToNatLE word := by
  induction word with
  | nil =>
      rfl
  | cons bit rest ih =>
      simp [RMQ.WordRAM.bitsToNatLE, bitsToNatLE, RMQ.WordRAM.bitToNat,
        bitToNat, ih]

theorem bitsToOptionNatLE_eq (width : Nat) (word : List Bool) :
    RMQ.WordRAM.bitsToOptionNatLE width word =
      bitsToOptionNatLE width word := by
  cases word with
  | nil =>
      rfl
  | cons present rest =>
      by_cases hpresent : present = true
      · simp [RMQ.WordRAM.bitsToOptionNatLE, bitsToOptionNatLE,
          hpresent, bitsToNatLE_eq]
      · have hfalse : present = false := by
          cases present <;> simp at hpresent ⊢
        simp [RMQ.WordRAM.bitsToOptionNatLE, bitsToOptionNatLE, hfalse]

end WordRAMBridge

namespace FixedWidthNatTable

/-- A one-segment Word-RAM store for this fixed-width natural table. -/
def wordRAMStore
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    RMQ.WordRAM.Store :=
  table.store.wordRAMStore

/-- First-order program for reading and decoding one table cell. -/
def readProgram
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    RMQ.WordRAM.Program .optNat :=
  RMQ.WordRAM.Program.mapOptWordNat (table.store.readProgram i)

@[simp] theorem readProgram_eval_value
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).value =
      (table.store.words[i]?).map RMQ.WordRAM.bitsToNatLE := by
  rfl

theorem readProgram_exact
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted.erase =
      entries[i]? := by
  have hdecode :
      (table.store.words[i]?).map RMQ.WordRAM.bitsToNatLE =
        (table.store.words[i]?).map bitsToNatLE := by
    cases table.store.words[i]? with
    | none =>
        rfl
    | some word =>
        simp [WordRAMBridge.bitsToNatLE_eq word]
  change (table.store.words[i]?).map RMQ.WordRAM.bitsToNatLE = entries[i]?
  rw [hdecode]
  exact table.read_exact i

theorem readProgram_cost
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted.cost = 1 := by
  rfl

/-- Interpreted table reads refine the existing costed table read. -/
theorem readProgram_refines_readCosted
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted =
      table.readCosted i := by
  apply Costed.ext
  · simpa [Costed.erase] using
      (table.readProgram_exact i).trans (table.readCosted_erase i).symm
  · exact (table.readProgram_cost i).trans (table.readCosted_cost i).symm

theorem readProgram_profile
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload.length = entries.length * width /\
      forall i,
        ((table.readProgram i).eval table.wordRAMStore).toCosted.cost <= 1 /\
          ((table.readProgram i).eval table.wordRAMStore).toCosted.erase =
            entries[i]? := by
  constructor
  · exact table.payload_length
  · intro i
    exact ⟨by
      rw [readProgram_cost]
      exact Nat.le_refl 1,
      table.readProgram_exact i⟩

theorem wordRAMStore_wordsBounded_of_width_le
    {entries : List Nat} {width bound : Nat}
    (table : FixedWidthNatTable entries width)
    (hwidth : width <= bound) :
    table.wordRAMStore.WordsBounded bound := by
  intro segment index word hread
  unfold wordRAMStore PayloadWordStore.wordRAMStore
    RMQ.WordRAM.Store.readWord? at hread
  cases segment with
  | zero =>
      simp at hread
      have hlen : word.length = width :=
        table.word_length_of_get? hread
      omega
  | succ segment =>
      simp at hread

end FixedWidthNatTable

namespace FixedWidthOptionNatTable

/-- A one-segment Word-RAM store for this fixed-width optional-natural table. -/
def wordRAMStore
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    RMQ.WordRAM.Store :=
  table.store.wordRAMStore

/-- First-order program for reading and decoding one optional table cell. -/
def readProgram
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    RMQ.WordRAM.Program .optOptNat :=
  RMQ.WordRAM.Program.mapOptWordOptionNat width (table.store.readProgram i)

@[simp] theorem readProgram_eval_value
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).value =
      (table.store.words[i]?).map
        (RMQ.WordRAM.bitsToOptionNatLE width) := by
  rfl

theorem readProgram_exact
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted.erase =
      entries[i]? := by
  have hdecode :
      (table.store.words[i]?).map
          (RMQ.WordRAM.bitsToOptionNatLE width) =
        (table.store.words[i]?).map (bitsToOptionNatLE width) := by
    cases table.store.words[i]? with
    | none =>
        rfl
    | some word =>
        simp [WordRAMBridge.bitsToOptionNatLE_eq width word]
  change (table.store.words[i]?).map
      (RMQ.WordRAM.bitsToOptionNatLE width) = entries[i]?
  rw [hdecode]
  exact table.read_exact i

theorem readProgram_cost
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted.cost = 1 := by
  rfl

/-- Interpreted optional-table reads refine the existing costed table read. -/
theorem readProgram_refines_readCosted
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    ((table.readProgram i).eval table.wordRAMStore).toCosted =
      table.readCosted i := by
  apply Costed.ext
  · simpa [Costed.erase] using
      (table.readProgram_exact i).trans (table.readCosted_erase i).symm
  · exact (table.readProgram_cost i).trans (table.readCosted_cost i).symm

theorem readProgram_profile
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    table.payload.length = entries.length * optionNatWordWidth width /\
      forall i,
        ((table.readProgram i).eval table.wordRAMStore).toCosted.cost <= 1 /\
          ((table.readProgram i).eval table.wordRAMStore).toCosted.erase =
            entries[i]? := by
  constructor
  · exact table.payload_length
  · intro i
    exact ⟨by
      rw [readProgram_cost]
      exact Nat.le_refl 1,
      table.readProgram_exact i⟩

theorem wordRAMStore_wordsBounded_of_width_le
    {entries : List (Option Nat)} {width bound : Nat}
    (table : FixedWidthOptionNatTable entries width)
    (hwidth : optionNatWordWidth width <= bound) :
    table.wordRAMStore.WordsBounded bound := by
  intro segment index word hread
  unfold wordRAMStore PayloadWordStore.wordRAMStore
    RMQ.WordRAM.Store.readWord? at hread
  cases segment with
  | zero =>
      simp at hread
      have hlen : word.length = optionNatWordWidth width :=
        table.word_length_of_get? hread
      omega
  | succ segment =>
      simp at hread

end FixedWidthOptionNatTable

namespace FixedWidthRankSampleTables

/-- First-order program for reading a true/false rank sample. -/
def sampleProgram
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    RMQ.WordRAM.Program .optNat :=
  match target with
  | true => tables.trueTable.readProgram i
  | false => tables.falseTable.readProgram i

/-- The Word-RAM store used by the selected sample table. -/
def sampleWordRAMStore
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) : RMQ.WordRAM.Store :=
  match target with
  | true => tables.trueTable.wordRAMStore
  | false => tables.falseTable.wordRAMStore

theorem sampleProgram_exact
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    ((tables.sampleProgram target i).eval
        (tables.sampleWordRAMStore target)).toCosted.erase =
      (tables.entries target)[i]? := by
  cases target <;> simp [sampleProgram, sampleWordRAMStore, entries,
    FixedWidthNatTable.readProgram_exact]

theorem sampleProgram_cost
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    ((tables.sampleProgram target i).eval
        (tables.sampleWordRAMStore target)).toCosted.cost = 1 := by
  cases target <;> rfl

theorem sampleProgram_refines_sampleCosted
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    ((tables.sampleProgram target i).eval
        (tables.sampleWordRAMStore target)).toCosted =
      tables.sampleCosted target i := by
  cases target <;>
    simp [sampleProgram, sampleWordRAMStore, sampleCosted,
      FixedWidthNatTable.readProgram_refines_readCosted]

theorem sampleProgram_profile
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    tables.payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        ((tables.sampleProgram target i).eval
            (tables.sampleWordRAMStore target)).toCosted.cost <= 1 /\
          ((tables.sampleProgram target i).eval
              (tables.sampleWordRAMStore target)).toCosted.erase =
            (tables.entries target)[i]? := by
  constructor
  · exact tables.payload_length
  · intro target i
    exact ⟨by
      rw [sampleProgram_cost]
      exact Nat.le_refl 1,
      tables.sampleProgram_exact target i⟩

end FixedWidthRankSampleTables

end SuccinctSpace

end RMQ
