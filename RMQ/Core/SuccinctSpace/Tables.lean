import RMQ.Core.SuccinctSpace.WordStore

/-!
# Fixed-width payload tables

Payload-live fixed-width natural, optional-natural, and rank-sample tables.
These tables are generic storage/refinement components reused by the succinct
rank/select and BP-navigation layers.
-/

namespace RMQ

namespace SuccinctSpace

/--
Fixed-width natural-number table stored inside counted payload words.

`read_exact` is the semantic codec obligation: decoding the stored word at slot
`i` gives the reference entry `entries[i]?`.  Unlike the older
payload-backed wrappers, the query path below reads the payload word itself,
not an arbitrary decoded `IndexedSeq Nat` supplied beside the payload.
-/
structure FixedWidthNatTable (entries : List Nat) (width : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq : payload.length = entries.length * width
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits -> bits.length = width
  read_exact :
    forall i : Nat, (store.words[i]?).map bitsToNatLE = entries[i]?

namespace FixedWidthNatTable

def ofEncodedWords
    (entries : List Nat) (width : Nat) (words : List (List Bool))
    (hentries : words.map bitsToNatLE = entries)
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    FixedWidthNatTable entries width where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length = words.length * width :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * width := by
        rw [<- hentries]
        simp
  word_length_of_get? := by
    intro i bits hget
    have hlist : words[i]? = some bits := by
      simpa [Array.getElem?_toList] using hget
    exact hwidth (List.mem_of_getElem? hlist)
  read_exact := by
    intro i
    have hmap : (words.map bitsToNatLE)[i]? = entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    FixedWidthNatTable entries width :=
  ofEncodedWords entries width (entries.map (natToBitsLE width)) (by
    induction entries with
    | nil =>
        simp
    | cons entry rest ih =>
        have hentry : entry < 2 ^ width :=
          hbound List.mem_cons_self
        have hrest :
            forall {tailEntry : Nat},
              List.Mem tailEntry rest -> tailEntry < 2 ^ width := by
          intro tailEntry hmem
          exact hbound (List.mem_cons_of_mem entry hmem)
        simp [bitsToNatLE_natToBitsLE_of_lt hentry, ih hrest])
    (by
      intro word hmem
      rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
      exact natToBitsLE_length width entry)

def readCosted
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun word? => word?.map bitsToNatLE)
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted]

theorem readCosted_cost_le_one
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, table.read_exact i]

theorem payload_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload.length = entries.length * width :=
  table.payload_length_eq

theorem read_word_length_of_some
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width)
    {i : Nat} {word : List Bool}
    (hword : table.store.words[i]? = some word) :
    word.length = width :=
  table.word_length_of_get? hword

theorem profile
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.payload.length = entries.length * width /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      flattenPayloadWords table.store.words.toList = table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List Nat) (width : Nat) (words : List (List Bool))
    (hentries : words.map bitsToNatLE = entries)
    (hwidth :
      forall {word : List Bool}, List.Mem word words -> word.length = width) :
    (ofEncodedWords entries width words hentries hwidth).payload.length =
        entries.length * width /\
      (forall i,
        ((ofEncodedWords entries width words hentries hwidth).readCosted i).cost <=
            1 /\
          ((ofEncodedWords entries width words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries width words hentries hwidth).store.words.toList =
        (ofEncodedWords entries width words hentries hwidth).payload := by
  exact (ofEncodedWords entries width words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List Nat) (width : Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries -> entry < 2 ^ width) :
    (ofEntries entries width hbound).payload.length =
        entries.length * width /\
      (forall i,
        ((ofEntries entries width hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries width hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries width hbound).store.words.toList =
        (ofEntries entries width hbound).payload := by
  exact (ofEntries entries width hbound).profile

end FixedWidthNatTable

/-- Decode a fixed-width optional natural number from one payload word. -/
def bitsToOptionNatLE (width : Nat) (bits : List Bool) : Option Nat :=
  match bits with
  | [] => none
  | present :: rest =>
      if present then
        some (bitsToNatLE (rest.take width))
      else
        none

def optionNatWordWidth (width : Nat) : Nat :=
  1 + width

def optionNatToBitsLE (width : Nat) : Option Nat -> List Bool
  | none => false :: List.replicate width false
  | some n => true :: natToBitsLE width n

theorem optionNatToBitsLE_length
    (width : Nat) (entry : Option Nat) :
    (optionNatToBitsLE width entry).length =
      optionNatWordWidth width := by
  cases entry <;>
    simp [optionNatToBitsLE, optionNatWordWidth, natToBitsLE_length,
      Nat.add_comm]

theorem bitsToOptionNatLE_optionNatToBitsLE_of_bound
    {width : Nat} {entry : Option Nat}
    (hbound : forall n : Nat, entry = some n -> n < 2 ^ width) :
    bitsToOptionNatLE width (optionNatToBitsLE width entry) = entry := by
  cases entry with
  | none =>
      simp [optionNatToBitsLE, bitsToOptionNatLE]
  | some n =>
      have hn : n < 2 ^ width := hbound n rfl
      have htake :
          (natToBitsLE width n).take width = natToBitsLE width n := by
        rw [List.take_of_length_le]
        rw [natToBitsLE_length]
        exact Nat.le_refl width
      simp [optionNatToBitsLE, bitsToOptionNatLE,
        htake, bitsToNatLE_natToBitsLE_of_lt hn]

/--
Fixed-width optional natural-number table stored inside counted payload words.

The outer option of `readCosted` is the indexed read; the inner option is the
stored payload value.
-/
structure FixedWidthOptionNatTable
    (entries : List (Option Nat)) (width : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq :
    payload.length = entries.length * optionNatWordWidth width
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits -> bits.length = optionNatWordWidth width
  read_exact :
    forall i : Nat,
      (store.words[i]?).map (bitsToOptionNatLE width) = entries[i]?

namespace FixedWidthOptionNatTable

def ofEncodedWords
    (entries : List (Option Nat)) (width : Nat)
    (words : List (List Bool))
    (hentries : words.map (bitsToOptionNatLE width) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words -> word.length = optionNatWordWidth width) :
    FixedWidthOptionNatTable entries width where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length =
          words.length * optionNatWordWidth width :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * optionNatWordWidth width := by
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
        (words.map (bitsToOptionNatLE width))[i]? = entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List (Option Nat)) (width : Nat)
    (hbound :
      forall {entry : Option Nat} {n : Nat},
        List.Mem entry entries -> entry = some n -> n < 2 ^ width) :
    FixedWidthOptionNatTable entries width :=
  ofEncodedWords entries width (entries.map (optionNatToBitsLE width)) (by
    induction entries with
    | nil =>
        simp
    | cons entry rest ih =>
        have hentry :
            bitsToOptionNatLE width (optionNatToBitsLE width entry) =
              entry := by
          exact bitsToOptionNatLE_optionNatToBitsLE_of_bound
            (entry := entry)
            (fun n hsome => hbound List.mem_cons_self hsome)
        have hrest :
            forall {tailEntry : Option Nat} {n : Nat},
              List.Mem tailEntry rest ->
                tailEntry = some n -> n < 2 ^ width := by
          intro tailEntry n hmem hsome
          exact hbound (List.mem_cons_of_mem entry hmem) hsome
        simp [hentry, ih hrest])
    (by
      intro word hmem
      rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
      exact optionNatToBitsLE_length width entry)

def readCosted
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    Costed (Option (Option Nat)) :=
  Costed.map (fun word? => word?.map (bitsToOptionNatLE width))
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted]

theorem readCosted_cost_le_one
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, table.read_exact i]

theorem payload_length
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    table.payload.length = entries.length * optionNatWordWidth width :=
  table.payload_length_eq

theorem profile
    {entries : List (Option Nat)} {width : Nat}
    (table : FixedWidthOptionNatTable entries width) :
    table.payload.length = entries.length * optionNatWordWidth width /\
      (forall i, (table.readCosted i).cost <= 1 /\
        (table.readCosted i).erase = entries[i]?) /\
      flattenPayloadWords table.store.words.toList = table.payload := by
  constructor
  · exact table.payload_length
  · constructor
    · intro i
      exact ⟨table.readCosted_cost_le_one i,
        table.readCosted_erase i⟩
    · exact table.store.payload_eq_words_join

theorem ofEncodedWords_profile
    (entries : List (Option Nat)) (width : Nat)
    (words : List (List Bool))
    (hentries : words.map (bitsToOptionNatLE width) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words -> word.length = optionNatWordWidth width) :
    (ofEncodedWords entries width words hentries hwidth).payload.length =
        entries.length * optionNatWordWidth width /\
      (forall i,
        ((ofEncodedWords entries width words hentries hwidth).readCosted i).cost <=
            1 /\
          ((ofEncodedWords entries width words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries width words hentries hwidth).store.words.toList =
        (ofEncodedWords entries width words hentries hwidth).payload := by
  exact (ofEncodedWords entries width words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List (Option Nat)) (width : Nat)
    (hbound :
      forall {entry : Option Nat} {n : Nat},
        List.Mem entry entries -> entry = some n -> n < 2 ^ width) :
    (ofEntries entries width hbound).payload.length =
        entries.length * optionNatWordWidth width /\
      (forall i,
        ((ofEntries entries width hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries width hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries width hbound).store.words.toList =
        (ofEntries entries width hbound).payload := by
  exact (ofEntries entries width hbound).profile

end FixedWidthOptionNatTable

/--
Payload-live true/false rank-sample tables.

This is the small codec layer that the final succinct rank directory should
consume: each sample query reads one fixed-width word from the counted payload
for the requested bit value.  It deliberately does not claim that these tables
are `o(n)`; full-precision sample arrays are a fidelity layer, not the final
succinct directory.
-/
structure FixedWidthRankSampleTables
    (trueEntries falseEntries : List Nat) (width : Nat) where
  trueTable : FixedWidthNatTable trueEntries width
  falseTable : FixedWidthNatTable falseEntries width

namespace FixedWidthRankSampleTables

def ofEncodedWords
    (trueEntries falseEntries : List Nat) (width : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue : trueWords.map bitsToNatLE = trueEntries)
    (hfalse : falseWords.map bitsToNatLE = falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords -> word.length = width)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords -> word.length = width) :
    FixedWidthRankSampleTables trueEntries falseEntries width where
  trueTable :=
    FixedWidthNatTable.ofEncodedWords
      trueEntries width trueWords htrue htrueWidth
  falseTable :=
    FixedWidthNatTable.ofEncodedWords
      falseEntries width falseWords hfalse hfalseWidth

def ofEntries
    (trueEntries falseEntries : List Nat) (width : Nat)
    (htrue :
      forall {entry : Nat}, List.Mem entry trueEntries -> entry < 2 ^ width)
    (hfalse :
      forall {entry : Nat}, List.Mem entry falseEntries -> entry < 2 ^ width) :
    FixedWidthRankSampleTables trueEntries falseEntries width where
  trueTable := FixedWidthNatTable.ofEntries trueEntries width htrue
  falseTable := FixedWidthNatTable.ofEntries falseEntries width hfalse

def payload
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    List Bool :=
  tables.trueTable.payload ++ tables.falseTable.payload

def entries
    {trueEntries falseEntries : List Nat} {width : Nat}
    (_tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) : List Nat :=
  match target with
  | true => trueEntries
  | false => falseEntries

def sampleCosted
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) : Costed (Option Nat) :=
  match target with
  | true => tables.trueTable.readCosted i
  | false => tables.falseTable.readCosted i

@[simp] theorem sampleCosted_cost
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost = 1 := by
  cases target <;> simp [sampleCosted]

theorem sampleCosted_cost_le_one
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost <= 1 := by
  simp

@[simp] theorem sampleCosted_erase
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).erase =
      (tables.entries target)[i]? := by
  cases target <;> simp [sampleCosted, entries]

theorem payload_length
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    tables.payload.length =
      trueEntries.length * width + falseEntries.length * width := by
  simp [payload, tables.trueTable.payload_length,
    tables.falseTable.payload_length]

theorem profile
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables : FixedWidthRankSampleTables trueEntries falseEntries width) :
    tables.payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        (tables.sampleCosted target i).cost <= 1 /\
          (tables.sampleCosted target i).erase =
            (tables.entries target)[i]? := by
  constructor
  · exact tables.payload_length
  · intro target i
    exact ⟨tables.sampleCosted_cost_le_one target i,
      tables.sampleCosted_erase target i⟩

theorem ofEncodedWords_profile
    (trueEntries falseEntries : List Nat) (width : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue : trueWords.map bitsToNatLE = trueEntries)
    (hfalse : falseWords.map bitsToNatLE = falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords -> word.length = width)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords -> word.length = width) :
    (ofEncodedWords trueEntries falseEntries width trueWords falseWords
        htrue hfalse htrueWidth hfalseWidth).payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted target i).cost <=
            1 /\
          ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).erase =
            ((ofEncodedWords trueEntries falseEntries width trueWords falseWords
              htrue hfalse htrueWidth hfalseWidth).entries target)[i]? := by
  exact
    (ofEncodedWords trueEntries falseEntries width trueWords falseWords
      htrue hfalse htrueWidth hfalseWidth).profile

theorem ofEntries_profile
    (trueEntries falseEntries : List Nat) (width : Nat)
    (htrue :
      forall {entry : Nat}, List.Mem entry trueEntries -> entry < 2 ^ width)
    (hfalse :
      forall {entry : Nat}, List.Mem entry falseEntries -> entry < 2 ^ width) :
    (ofEntries trueEntries falseEntries width htrue hfalse).payload.length =
        trueEntries.length * width + falseEntries.length * width /\
      forall target i,
        ((ofEntries trueEntries falseEntries width htrue hfalse).sampleCosted
            target i).cost <= 1 /\
          ((ofEntries trueEntries falseEntries width htrue hfalse).sampleCosted
              target i).erase =
            ((ofEntries trueEntries falseEntries width htrue hfalse).entries
              target)[i]? := by
  exact (ofEntries trueEntries falseEntries width htrue hfalse).profile

end FixedWidthRankSampleTables

end SuccinctSpace

end RMQ
