import RMQ.Core.SuccinctSpace.Tables

/-!
# Select locator sample tables

Payload-live codecs and fixed-width tables for select locator samples.
-/

namespace RMQ

namespace SuccinctSpace


/-- Stored locator for a word-level select query. -/
structure StoredWordSelectSample where
  wordIndex : Nat
  wordStart : Nat
  rankBefore : Nat

def selectSampleSeqOf
    (target : Bool)
    (trueSamples falseSamples :
      TableModel.IndexedSeq (Option StoredWordSelectSample)) :
    TableModel.IndexedSeq (Option StoredWordSelectSample) :=
  match target with
  | true => trueSamples
  | false => falseSamples

/--
Decode one fixed-width select locator word.

The first bit is a presence bit.  When present, the remaining payload is split
into three little-endian fields of width `fieldWidth`: `wordIndex`,
`wordStart`, and `rankBefore`.
-/
def bitsToStoredWordSelectSample
    (fieldWidth : Nat) (bits : List Bool) :
    Option StoredWordSelectSample :=
  match bits with
  | [] => none
  | present :: rest =>
      if present then
        some
          { wordIndex := bitsToNatLE (rest.take fieldWidth)
            wordStart := bitsToNatLE ((rest.drop fieldWidth).take fieldWidth)
            rankBefore :=
              bitsToNatLE ((rest.drop (2 * fieldWidth)).take fieldWidth) }
      else
        none

def selectSampleWordWidth (fieldWidth : Nat) : Nat :=
  1 + 3 * fieldWidth

def storedWordSelectSampleToBitsLE
    (fieldWidth : Nat) (sample : StoredWordSelectSample) :
    List Bool :=
  natToBitsLE fieldWidth sample.wordIndex ++
    natToBitsLE fieldWidth sample.wordStart ++
      natToBitsLE fieldWidth sample.rankBefore

theorem storedWordSelectSampleToBitsLE_length
    (fieldWidth : Nat) (sample : StoredWordSelectSample) :
    (storedWordSelectSampleToBitsLE fieldWidth sample).length =
      3 * fieldWidth := by
  simp [storedWordSelectSampleToBitsLE, natToBitsLE_length]
  omega

def optionStoredWordSelectSampleToBitsLE
    (fieldWidth : Nat) : Option StoredWordSelectSample -> List Bool
  | none => false :: List.replicate (3 * fieldWidth) false
  | some sample => true :: storedWordSelectSampleToBitsLE fieldWidth sample

theorem optionStoredWordSelectSampleToBitsLE_length
    (fieldWidth : Nat) (entry : Option StoredWordSelectSample) :
    (optionStoredWordSelectSampleToBitsLE fieldWidth entry).length =
      selectSampleWordWidth fieldWidth := by
  cases entry with
  | none =>
      simp [optionStoredWordSelectSampleToBitsLE, selectSampleWordWidth]
      omega
  | some sample =>
      simp [optionStoredWordSelectSampleToBitsLE, selectSampleWordWidth,
        storedWordSelectSampleToBitsLE_length]
      omega

theorem bitsToStoredWordSelectSample_optionToBits_of_bound
    {fieldWidth : Nat} {entry : Option StoredWordSelectSample}
    (hbound :
      forall sample : StoredWordSelectSample,
        entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    bitsToStoredWordSelectSample fieldWidth
        (optionStoredWordSelectSampleToBitsLE fieldWidth entry) =
      entry := by
  cases entry with
  | none =>
      simp [optionStoredWordSelectSampleToBitsLE,
        bitsToStoredWordSelectSample]
  | some sample =>
      rcases hbound sample rfl with ⟨hwordIndex, hwordStart, hrankBefore⟩
      let wordIndexBits := natToBitsLE fieldWidth sample.wordIndex
      let wordStartBits := natToBitsLE fieldWidth sample.wordStart
      let rankBeforeBits := natToBitsLE fieldWidth sample.rankBefore
      have hwordIndexLen : wordIndexBits.length = fieldWidth := by
        simp [wordIndexBits, natToBitsLE_length]
      have hwordStartLen : wordStartBits.length = fieldWidth := by
        simp [wordStartBits, natToBitsLE_length]
      have hrankBeforeLen : rankBeforeBits.length = fieldWidth := by
        simp [rankBeforeBits, natToBitsLE_length]
      have htakeWordIndex :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).take
              fieldWidth =
            wordIndexBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).take
              fieldWidth =
              (wordIndexBits ++ (wordStartBits ++ rankBeforeBits)).take
                wordIndexBits.length := by
            rw [hwordIndexLen]
            simp [List.append_assoc]
          _ = wordIndexBits := by
            rw [List.take_append_of_le_length (Nat.le_refl _)]
            rw [List.take_of_length_le (Nat.le_refl _)]
      have hdropWordIndex :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth =
            wordStartBits ++ rankBeforeBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth =
              (wordIndexBits ++ (wordStartBits ++ rankBeforeBits)).drop
                wordIndexBits.length := by
            rw [hwordIndexLen]
            simp [List.append_assoc]
          _ = wordStartBits ++ rankBeforeBits := by
            rw [List.drop_append_of_le_length (Nat.le_refl _)]
            rw [List.drop_of_length_le (Nat.le_refl _)]
            simp
      have htakeWordStart :
          ((wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              fieldWidth).take fieldWidth =
            wordStartBits := by
        rw [hdropWordIndex]
        calc
          (wordStartBits ++ rankBeforeBits).take fieldWidth =
              (wordStartBits ++ rankBeforeBits).take wordStartBits.length := by
            rw [hwordStartLen]
          _ = wordStartBits := by
            rw [List.take_append_of_le_length (Nat.le_refl _)]
            rw [List.take_of_length_le (Nat.le_refl _)]
      have hdropTwo :
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth) =
            rankBeforeBits := by
        calc
          (wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth) =
              ((wordIndexBits ++ wordStartBits) ++ rankBeforeBits).drop
                (wordIndexBits ++ wordStartBits).length := by
            have hlen :
                (wordIndexBits ++ wordStartBits).length =
                  2 * fieldWidth := by
              simp [hwordIndexLen, hwordStartLen]
              omega
            rw [hlen]
          _ = rankBeforeBits := by
            rw [List.drop_append_of_le_length (Nat.le_refl _)]
            rw [List.drop_of_length_le (Nat.le_refl _)]
            simp
      have htakeRankBefore :
          ((wordIndexBits ++ wordStartBits ++ rankBeforeBits).drop
              (2 * fieldWidth)).take fieldWidth =
            rankBeforeBits := by
        rw [hdropTwo]
        rw [List.take_of_length_le]
        rw [hrankBeforeLen]
        exact Nat.le_refl fieldWidth
      have htakeWordIndexRaw :
          (natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).take
              fieldWidth =
            natToBitsLE fieldWidth sample.wordIndex := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeWordIndex
      have htakeWordStartRaw :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).drop
              fieldWidth).take fieldWidth =
            natToBitsLE fieldWidth sample.wordStart := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeWordStart
      have htakeRankBeforeRaw :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore).drop
              (2 * fieldWidth)).take fieldWidth =
            natToBitsLE fieldWidth sample.rankBefore := by
        simpa [wordIndexBits, wordStartBits, rankBeforeBits]
          using htakeRankBefore
      have htakeWordIndexRight :
          (natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).take
              fieldWidth =
            natToBitsLE fieldWidth sample.wordIndex := by
        simpa [List.append_assoc] using htakeWordIndexRaw
      have htakeWordStartRight :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).drop
              fieldWidth).take fieldWidth =
            natToBitsLE fieldWidth sample.wordStart := by
        simpa [List.append_assoc] using htakeWordStartRaw
      have htakeRankBeforeRight :
          ((natToBitsLE fieldWidth sample.wordIndex ++
              (natToBitsLE fieldWidth sample.wordStart ++
                natToBitsLE fieldWidth sample.rankBefore)).drop
              (2 * fieldWidth)).take fieldWidth =
            natToBitsLE fieldWidth sample.rankBefore := by
        simpa [List.append_assoc] using htakeRankBeforeRaw
      simp [optionStoredWordSelectSampleToBitsLE,
        storedWordSelectSampleToBitsLE, bitsToStoredWordSelectSample]
      rw [htakeWordIndexRight, htakeWordStartRight, htakeRankBeforeRight]
      simp [bitsToNatLE_natToBitsLE_of_lt hwordIndex,
        bitsToNatLE_natToBitsLE_of_lt hwordStart,
        bitsToNatLE_natToBitsLE_of_lt hrankBefore]

/--
Payload-live fixed-width table of optional select locators.

Outer `none` is an out-of-table read; `some none` is a stored certificate that
the requested occurrence is absent.
-/
structure FixedWidthSelectSampleTable
    (entries : List (Option StoredWordSelectSample)) (fieldWidth : Nat) where
  payload : List Bool
  store : PayloadWordStore payload
  payload_length_eq :
    payload.length = entries.length * selectSampleWordWidth fieldWidth
  word_length_of_get? :
    forall {i : Nat} {bits : List Bool},
      store.words[i]? = some bits ->
        bits.length = selectSampleWordWidth fieldWidth
  read_exact :
    forall i : Nat,
      (store.words[i]?).map (bitsToStoredWordSelectSample fieldWidth) =
        entries[i]?

namespace FixedWidthSelectSampleTable

def ofEncodedWords
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToStoredWordSelectSample fieldWidth) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length = selectSampleWordWidth fieldWidth) :
    FixedWidthSelectSampleTable entries fieldWidth where
  payload := flattenPayloadWords words
  store :=
    { words := words.toArray
      erases := by simp }
  payload_length_eq := by
    calc
      (flattenPayloadWords words).length =
          words.length * selectSampleWordWidth fieldWidth :=
        flattenPayloadWords_length_of_forall_length hwidth
      _ = entries.length * selectSampleWordWidth fieldWidth := by
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
        (words.map (bitsToStoredWordSelectSample fieldWidth))[i]? =
          entries[i]? := by
      rw [hentries]
    simpa [Array.getElem?_toList] using hmap

def ofEntries
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (hbound :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry entries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    FixedWidthSelectSampleTable entries fieldWidth :=
  ofEncodedWords entries fieldWidth
    (entries.map (optionStoredWordSelectSampleToBitsLE fieldWidth)) (by
      induction entries with
      | nil =>
          simp
      | cons entry rest ih =>
          have hentry :
              bitsToStoredWordSelectSample fieldWidth
                  (optionStoredWordSelectSampleToBitsLE fieldWidth entry) =
                entry := by
            exact bitsToStoredWordSelectSample_optionToBits_of_bound
              (entry := entry)
              (fun sample hsome => hbound List.mem_cons_self hsome)
          have hrest :
              forall {tailEntry : Option StoredWordSelectSample}
                  {sample : StoredWordSelectSample},
                List.Mem tailEntry rest ->
                  tailEntry = some sample ->
                    sample.wordIndex < 2 ^ fieldWidth /\
                      sample.wordStart < 2 ^ fieldWidth /\
                        sample.rankBefore < 2 ^ fieldWidth := by
            intro tailEntry sample hmem hsome
            exact hbound (List.mem_cons_of_mem entry hmem) hsome
          simp [hentry, ih hrest])
      (by
        intro word hmem
        rcases List.mem_map.mp hmem with ⟨entry, _hentry, rfl⟩
        exact optionStoredWordSelectSampleToBitsLE_length fieldWidth entry)

def readCosted
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  Costed.map
    (fun word? => word?.map (bitsToStoredWordSelectSample fieldWidth))
    (table.store.readWordCosted i)

@[simp] theorem readCosted_cost
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).cost = 1 := by
  simp [readCosted, Costed.map_cost]

theorem readCosted_cost_le_one
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).cost <= 1 := by
  simp

@[simp] theorem readCosted_erase
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) (i : Nat) :
    (table.readCosted i).erase = entries[i]? := by
  simp [readCosted, Costed.erase_map, table.read_exact i]

theorem payload_length
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    table.payload.length =
      entries.length * selectSampleWordWidth fieldWidth :=
  table.payload_length_eq

theorem profile
    {entries : List (Option StoredWordSelectSample)} {fieldWidth : Nat}
    (table : FixedWidthSelectSampleTable entries fieldWidth) :
    table.payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
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
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) (words : List (List Bool))
    (hentries :
      words.map (bitsToStoredWordSelectSample fieldWidth) = entries)
    (hwidth :
      forall {word : List Bool},
        List.Mem word words ->
          word.length = selectSampleWordWidth fieldWidth) :
    (ofEncodedWords entries fieldWidth words hentries hwidth).payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      (forall i,
        ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
            i).cost <= 1 /\
          ((ofEncodedWords entries fieldWidth words hentries hwidth).readCosted
              i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEncodedWords entries fieldWidth words hentries hwidth).store.words.toList =
        (ofEncodedWords entries fieldWidth words hentries hwidth).payload := by
  exact (ofEncodedWords entries fieldWidth words hentries hwidth).profile

theorem ofEntries_profile
    (entries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (hbound :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry entries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    (ofEntries entries fieldWidth hbound).payload.length =
        entries.length * selectSampleWordWidth fieldWidth /\
      (forall i,
        ((ofEntries entries fieldWidth hbound).readCosted i).cost <= 1 /\
          ((ofEntries entries fieldWidth hbound).readCosted i).erase =
            entries[i]?) /\
      flattenPayloadWords
          (ofEntries entries fieldWidth hbound).store.words.toList =
        (ofEntries entries fieldWidth hbound).payload := by
  exact (ofEntries entries fieldWidth hbound).profile

end FixedWidthSelectSampleTable

/-- Payload-live true/false select-locator tables. -/
structure FixedWidthSelectSampleTables
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat) where
  trueTable : FixedWidthSelectSampleTable trueEntries fieldWidth
  falseTable : FixedWidthSelectSampleTable falseEntries fieldWidth

namespace FixedWidthSelectSampleTables

def ofEncodedWords
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue :
      trueWords.map (bitsToStoredWordSelectSample fieldWidth) = trueEntries)
    (hfalse :
      falseWords.map (bitsToStoredWordSelectSample fieldWidth) =
        falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords ->
          word.length = selectSampleWordWidth fieldWidth)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords ->
          word.length = selectSampleWordWidth fieldWidth) :
    FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth where
  trueTable :=
    FixedWidthSelectSampleTable.ofEncodedWords
      trueEntries fieldWidth trueWords htrue htrueWidth
  falseTable :=
    FixedWidthSelectSampleTable.ofEncodedWords
      falseEntries fieldWidth falseWords hfalse hfalseWidth

def ofEntries
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (htrue :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry trueEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth)
    (hfalse :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry falseEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth where
  trueTable :=
    FixedWidthSelectSampleTable.ofEntries
      trueEntries fieldWidth htrue
  falseTable :=
    FixedWidthSelectSampleTable.ofEntries
      falseEntries fieldWidth hfalse

def payload
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    List Bool :=
  tables.trueTable.payload ++ tables.falseTable.payload

def entries
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (_tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) : List (Option StoredWordSelectSample) :=
  match target with
  | true => trueEntries
  | false => falseEntries

def sampleCosted
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    Costed (Option (Option StoredWordSelectSample)) :=
  match target with
  | true => tables.trueTable.readCosted i
  | false => tables.falseTable.readCosted i

@[simp] theorem sampleCosted_cost
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost = 1 := by
  cases target <;> simp [sampleCosted]

theorem sampleCosted_cost_le_one
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).cost <= 1 := by
  simp

@[simp] theorem sampleCosted_erase
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth)
    (target : Bool) (i : Nat) :
    (tables.sampleCosted target i).erase =
      (tables.entries target)[i]? := by
  cases target <;> simp [sampleCosted, entries]

theorem payload_length
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    tables.payload.length =
      trueEntries.length * selectSampleWordWidth fieldWidth +
        falseEntries.length * selectSampleWordWidth fieldWidth := by
  simp [payload, tables.trueTable.payload_length,
    tables.falseTable.payload_length]

theorem profile
    {trueEntries falseEntries : List (Option StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      FixedWidthSelectSampleTables trueEntries falseEntries fieldWidth) :
    tables.payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
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
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (trueWords falseWords : List (List Bool))
    (htrue :
      trueWords.map (bitsToStoredWordSelectSample fieldWidth) = trueEntries)
    (hfalse :
      falseWords.map (bitsToStoredWordSelectSample fieldWidth) =
        falseEntries)
    (htrueWidth :
      forall {word : List Bool},
        List.Mem word trueWords ->
          word.length = selectSampleWordWidth fieldWidth)
    (hfalseWidth :
      forall {word : List Bool},
        List.Mem word falseWords ->
          word.length = selectSampleWordWidth fieldWidth) :
    (ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
        htrue hfalse htrueWidth hfalseWidth).payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).cost <= 1 /\
          ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
            htrue hfalse htrueWidth hfalseWidth).sampleCosted
              target i).erase =
            ((ofEncodedWords trueEntries falseEntries fieldWidth trueWords
              falseWords htrue hfalse htrueWidth hfalseWidth).entries
                target)[i]? := by
  exact
    (ofEncodedWords trueEntries falseEntries fieldWidth trueWords falseWords
      htrue hfalse htrueWidth hfalseWidth).profile

theorem ofEntries_profile
    (trueEntries falseEntries : List (Option StoredWordSelectSample))
    (fieldWidth : Nat)
    (htrue :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry trueEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth)
    (hfalse :
      forall {entry : Option StoredWordSelectSample}
          {sample : StoredWordSelectSample},
        List.Mem entry falseEntries -> entry = some sample ->
          sample.wordIndex < 2 ^ fieldWidth /\
            sample.wordStart < 2 ^ fieldWidth /\
              sample.rankBefore < 2 ^ fieldWidth) :
    (ofEntries trueEntries falseEntries fieldWidth htrue hfalse).payload.length =
        trueEntries.length * selectSampleWordWidth fieldWidth +
          falseEntries.length * selectSampleWordWidth fieldWidth /\
      forall target i,
        ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).sampleCosted
            target i).cost <= 1 /\
          ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).sampleCosted
              target i).erase =
            ((ofEntries trueEntries falseEntries fieldWidth htrue hfalse).entries
              target)[i]? := by
  exact (ofEntries trueEntries falseEntries fieldWidth htrue hfalse).profile

end FixedWidthSelectSampleTables

end SuccinctSpace

end RMQ
