import RMQ.Core.SuccinctSpace.Tables

namespace RMQ

namespace SuccinctSpace

/--
A machine-word view of a fixed-width table.  The store contains the chunks of
all logical cells, in logical-cell order; flattening it is exactly the original
counted table payload.
-/
def fixedWidthNatTableMachineChunkCount (width wordSize : Nat) : Nat :=
  width / wordSize + (if width % wordSize = 0 then 0 else 1)

def fixedWidthNatTableMachineWords
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (wordSize : Nat) :
    List (List Bool) :=
  table.store.words.toList.flatMap (chunkPayloadWords wordSize)

theorem flattenPayloadWords_flatMap_chunkPayloadWords
    {wordSize : Nat} (hwordSize : 0 < wordSize)
    (words : List (List Bool)) :
    flattenPayloadWords
        (words.flatMap (chunkPayloadWords wordSize)) =
      flattenPayloadWords words := by
  induction words with
  | nil => simp [flattenPayloadWords]
  | cons head tail ih =>
      rw [List.flatMap_cons, flattenPayloadWords_append,
        flattenPayloadWords_chunkPayloadWords hwordSize, ih]
      rfl

def FixedWidthNatTable.machineStore
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    BoundedPayloadWordStore table.payload wordSize where
  store :=
    { words := (fixedWidthNatTableMachineWords table wordSize).toArray
      erases := by
        unfold fixedWidthNatTableMachineWords
        rw [List.toList_toArray]
        rw [flattenPayloadWords_flatMap_chunkPayloadWords hwordSize]
        exact table.store.erases }
  word_length_le := by
    intro word hmem
    unfold fixedWidthNatTableMachineWords at hmem
    rcases List.mem_flatMap.mp hmem with ⟨logical, _, hchunk⟩
    exact chunkPayloadWords_word_length_le wordSize hchunk

@[simp] theorem FixedWidthNatTable.machineStore_erases
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize) :
    flattenPayloadWords
        (table.machineStore hwordSize).store.words.toList =
      table.payload :=
  (table.machineStore hwordSize).erases


theorem List.drop_append_length_add
    {α : Type} (xs ys : List α) (n : Nat) :
    (xs ++ ys).drop (xs.length + n) = ys.drop n := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [Nat.succ_add, ih]

theorem List.flatMap_drop_mul_take_of_constant_length
    {α β : Type} (xs : List α) (f : α -> List β) (count : Nat)
    (hlen : forall x, x ∈ xs -> (f x).length = count)
    {i : Nat} {x : α} (hget : xs[i]? = some x) :
    ((xs.flatMap f).drop (i * count)).take count = f x := by
  induction xs generalizing i with
  | nil => simp at hget
  | cons head tail ih =>
      cases i with
      | zero =>
          simp at hget
          subst x
          have hhead : (f head).length = count :=
            hlen head (by simp)
          simp [hhead]
      | succ i =>
          have htail : tail[i]? = some x := by
            simpa using hget
          have hhead : (f head).length = count :=
            hlen head (by simp)
          have htailLen : forall y, y ∈ tail -> (f y).length = count := by
            intro y hy
            exact hlen y (by simp [hy])
          rw [List.flatMap_cons, Nat.succ_mul]
          have hsum :
              i * count + count = (f head).length + i * count := by
            rw [hhead]
            omega
          rw [hsum, List.drop_append_length_add]
          exact ih htailLen htail

theorem List.mul_add_le_flatMap_length_of_constant_length
    {α β : Type} (xs : List α) (f : α -> List β) (count : Nat)
    (hlen : forall x, x ∈ xs -> (f x).length = count)
    {i : Nat} {x : α} (hget : xs[i]? = some x) :
    i * count + count <= (xs.flatMap f).length := by
  induction xs generalizing i with
  | nil => simp at hget
  | cons head tail ih =>
      cases i with
      | zero =>
          have hhead : (f head).length = count := hlen head (by simp)
          simp [hhead]
      | succ i =>
          have htail : tail[i]? = some x := by simpa using hget
          have hhead : (f head).length = count := hlen head (by simp)
          have htailLen : forall y, y ∈ tail -> (f y).length = count := by
            intro y hy
            exact hlen y (by simp [hy])
          have hrec := ih htailLen htail
          rw [List.flatMap_cons, List.length_append, hhead]
          rw [Nat.succ_mul]
          omega

theorem FixedWidthNatTable.machineWords_cell_slice
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    {i : Nat} {word : List Bool}
    (hget : table.store.words.toList[i]? = some word) :
    let count := fixedWidthNatTableMachineChunkCount width wordSize
    ((fixedWidthNatTableMachineWords table wordSize).drop (i * count)).take
        count =
      chunkPayloadWords wordSize word := by
  let count := fixedWidthNatTableMachineChunkCount width wordSize
  apply List.flatMap_drop_mul_take_of_constant_length
  · intro logical hmem
    have hlen : logical.length = width := by
      rcases List.mem_iff_getElem?.mp hmem with ⟨j, hlogical⟩
      exact table.word_length_of_get? (by
        simpa [Array.getElem?_toList] using hlogical)
    simpa [count, fixedWidthNatTableMachineChunkCount, hlen] using
      chunkPayloadWords_length_eq_div_add_indicator hwordSize logical
  · exact hget


def consecutiveWordIndices (start : Nat) : Nat -> List Nat
  | 0 => []
  | count + 1 => start :: consecutiveWordIndices (start + 1) count

@[simp] theorem consecutiveWordIndices_length (start count : Nat) :
    (consecutiveWordIndices start count).length = count := by
  induction count generalizing start with
  | zero => simp [consecutiveWordIndices]
  | succ count ih => simp [consecutiveWordIndices, ih]

theorem List.drop_take_succ_of_lt
    {α : Type} (xs : List α) (start count : Nat)
    (hstart : start < xs.length) :
    (xs.drop start).take (count + 1) =
      xs.get ⟨start, hstart⟩ :: (xs.drop (start + 1)).take count := by
  induction xs generalizing start with
  | nil => simp at hstart
  | cons head tail ih =>
      cases start with
      | zero => simp
      | succ start =>
          have htail : start < tail.length := by simpa using hstart
          simpa [Nat.add_assoc] using ih start htail

theorem boundedPayloadWordReadValues_consecutive
    {payload : List Bool} {wordSize start count : Nat}
    (store : BoundedPayloadWordStore payload wordSize)
    (hbound : start + count <= store.store.words.size) :
    boundedPayloadWordReadValues store
        (consecutiveWordIndices start count) =
      ((store.store.words.toList.drop start).take count).map some := by
  induction count generalizing start with
  | zero => simp [consecutiveWordIndices, boundedPayloadWordReadValues]
  | succ count ih =>
      have hstart : start < store.store.words.size := by omega
      have htail : start + 1 + count <= store.store.words.size := by omega
      have hget :
          store.store.words[start]? =
            some (store.store.words.toList.get ⟨start, by simpa using hstart⟩) := by
        simp [hstart]
      rw [show consecutiveWordIndices start (count + 1) =
        start :: consecutiveWordIndices (start + 1) count by
          rfl]
      rw [show boundedPayloadWordReadValues store
          (start :: consecutiveWordIndices (start + 1) count) =
        store.store.words[start]? ::
          boundedPayloadWordReadValues store
            (consecutiveWordIndices (start + 1) count) by
          rfl]
      rw [hget, ih (start := start + 1) htail]
      rw [List.drop_take_succ_of_lt store.store.words.toList start count
        (by simpa using hstart)]
      rfl

def fixedWidthNatTableMachineFootprint
    (width wordSize i : Nat) : List Nat :=
  let count := fixedWidthNatTableMachineChunkCount width wordSize
  consecutiveWordIndices (i * count) count

def collectPayloadWords : List (Option (List Bool)) -> Option (List Bool)
  | [] => some []
  | none :: _ => none
  | some word :: rest =>
      (collectPayloadWords rest).map fun tail => word ++ tail

@[simp] theorem collectPayloadWords_map_some
    (words : List (List Bool)) :
    collectPayloadWords (words.map some) = some (flattenPayloadWords words) := by
  induction words with
  | nil => simp [collectPayloadWords, flattenPayloadWords]
  | cons head tail ih =>
      simp [collectPayloadWords, flattenPayloadWords, ih]

def fixedWidthNatTableMachineDecode
    (words : List (Option (List Bool))) : Option Nat :=
  (collectPayloadWords words).map bitsToNatLE

def FixedWidthNatTable.machineReadCostedWithStore
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (canonicalWordCount : Nat)
    (store : BoundedPayloadWordStore table.payload wordSize)
    (i : Nat) : Costed (Option Nat) :=
  if i < entries.length then
    Costed.map fixedWidthNatTableMachineDecode
      (boundedPayloadWordReadsCosted store
        (fixedWidthNatTableMachineFootprint width wordSize i))
  else
    Costed.map (fun _ => none)
      (boundedPayloadWordReadsCosted store [canonicalWordCount])

def FixedWidthNatTable.machineReadCosted
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize) (i : Nat) : Costed (Option Nat) :=
  let store := table.machineStore hwordSize
  table.machineReadCostedWithStore store.store.words.size store i

@[simp] theorem FixedWidthNatTable.machineReadCostedWithStore_cost
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (canonicalWordCount : Nat)
    (store : BoundedPayloadWordStore table.payload wordSize)
    (i : Nat) :
    (table.machineReadCostedWithStore canonicalWordCount store i).cost =
      if i < entries.length then
        (fixedWidthNatTableMachineFootprint width wordSize i).length
      else 1 := by
  unfold FixedWidthNatTable.machineReadCostedWithStore
  by_cases hvalid : i < entries.length <;> simp [hvalid]

theorem FixedWidthNatTable.machineReadCostedWithStore_eq_of_agree
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (canonicalWordCount : Nat)
    (storeA storeB : BoundedPayloadWordStore table.payload wordSize)
    (i : Nat)
    (hagrees : forall address,
      address ∈
        (if i < entries.length then
          fixedWidthNatTableMachineFootprint width wordSize i
        else [canonicalWordCount]) ->
      storeA.store.words[address]? = storeB.store.words[address]?) :
    table.machineReadCostedWithStore canonicalWordCount storeA i =
      table.machineReadCostedWithStore canonicalWordCount storeB i := by
  unfold FixedWidthNatTable.machineReadCostedWithStore
  by_cases hvalid : i < entries.length
  · simp only [hvalid, if_true]
    rw [boundedPayloadWordReadsCosted_eq_of_agree storeA storeB]
    intro address hmem
    exact hagrees address (by simpa [hvalid] using hmem)
  · simp only [hvalid, if_false]
    rw [boundedPayloadWordReadsCosted_eq_of_agree storeA storeB]
    intro address hmem
    exact hagrees address (by simpa [hvalid] using hmem)



theorem consecutiveWordIndices_mem_bounds
    {start count address : Nat}
    (hmem : address ∈ consecutiveWordIndices start count) :
    And (start <= address) (address < start + count) := by
  induction count generalizing start with
  | zero => simp [consecutiveWordIndices] at hmem
  | succ count ih =>
      simp only [consecutiveWordIndices, List.mem_cons] at hmem
      cases hmem with
      | inl heq =>
          subst address
          omega
      | inr htail =>
          have hbounds := ih (start := start + 1) htail
          omega

theorem FixedWidthNatTable.machineFootprint_address_lt
    {entries : List Nat} {width wordSize i address : Nat}
    (table : FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize) (hvalid : i < entries.length)
    (hmem :
      address ∈ fixedWidthNatTableMachineFootprint width wordSize i) :
    address < (table.machineStore hwordSize).store.words.size := by
  have hentry : exists entry, entries[i]? = some entry :=
    ⟨entries[i], List.getElem?_eq_some_iff.mpr ⟨hvalid, rfl⟩⟩
  rcases hentry with ⟨entry, hentry⟩
  have hexact := table.read_exact i
  cases hword : table.store.words[i]? with
  | none => simp [hword, hentry] at hexact
  | some word =>
      have hwordList : table.store.words.toList[i]? = some word := by
        simpa [Array.getElem?_toList] using hword
      let count := fixedWidthNatTableMachineChunkCount width wordSize
      have hconst :
          forall logical,
            logical ∈ table.store.words.toList ->
              (chunkPayloadWords wordSize logical).length = count := by
        intro logical hlogical
        have hlen : logical.length = width := by
          rcases List.mem_iff_getElem?.mp hlogical with ⟨j, hget⟩
          exact table.word_length_of_get? (by
            simpa [Array.getElem?_toList] using hget)
        simpa [count, fixedWidthNatTableMachineChunkCount, hlen] using
          chunkPayloadWords_length_eq_div_add_indicator hwordSize logical
      have hphysical :=
        List.mul_add_le_flatMap_length_of_constant_length
          table.store.words.toList (chunkPayloadWords wordSize) count
          hconst hwordList
      have hbounds := consecutiveWordIndices_mem_bounds
        (by simpa [fixedWidthNatTableMachineFootprint, count] using hmem)
      dsimp [count] at hphysical
      change address <
        (fixedWidthNatTableMachineWords table wordSize).toArray.size
      rw [List.size_toArray]
      unfold fixedWidthNatTableMachineWords
      omega

theorem FixedWidthNatTable.machineFootprint_successful_read_backed
    {entries : List Nat} {width wordSize i address : Nat}
    (table : FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize) (hvalid : i < entries.length)
    (hmem :
      address ∈ fixedWidthNatTableMachineFootprint width wordSize i) :
    exists word,
      And
        (((table.machineStore hwordSize).store.readWordCosted address).erase =
          some word)
        (And
          (word ∈ (table.machineStore hwordSize).store.words.toList)
          (flattenPayloadWords
              (table.machineStore hwordSize).store.words.toList =
            table.payload)) := by
  have hlt := table.machineFootprint_address_lt hwordSize hvalid hmem
  cases hword :
      (table.machineStore hwordSize).store.words[address]? with
  | none =>
      rw [Array.getElem?_eq_none_iff] at hword
      omega
  | some word =>
      have hlist :
          (table.machineStore hwordSize).store.words.toList[address]? =
            some word := by
        simpa [Array.getElem?_toList] using hword
      refine ⟨word, ?_, List.mem_of_getElem? hlist,
        (table.machineStore hwordSize).erases⟩
      simp [hword]

@[simp] theorem FixedWidthNatTable.machineReadCosted_erase
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width)
    (hwordSize : 0 < wordSize) (i : Nat) :
    (table.machineReadCosted hwordSize i).erase =
      (table.readCosted i).erase := by
  rw [table.readCosted_erase]
  unfold FixedWidthNatTable.machineReadCosted
  unfold FixedWidthNatTable.machineReadCostedWithStore
  by_cases hvalid : i < entries.length
  · simp only [hvalid, if_true, Costed.erase_map]
    have hentry : exists entry, entries[i]? = some entry := by
      exact ⟨entries[i], List.getElem?_eq_some_iff.mpr ⟨hvalid, rfl⟩⟩
    rcases hentry with ⟨entry, hentry⟩
    have hexact := table.read_exact i
    cases hword : table.store.words[i]? with
    | none =>
        simp [hword, hentry] at hexact
    | some word =>
        have hwordList : table.store.words.toList[i]? = some word := by
          simpa [Array.getElem?_toList] using hword
        let count := fixedWidthNatTableMachineChunkCount width wordSize
        let start := i * count
        have hwordLen : word.length = width :=
          table.word_length_of_get? hword
        have hchunkLen :
            (chunkPayloadWords wordSize word).length = count := by
          simpa [count, fixedWidthNatTableMachineChunkCount, hwordLen] using
            chunkPayloadWords_length_eq_div_add_indicator hwordSize word
        have hslice :
            ((fixedWidthNatTableMachineWords table wordSize).drop start).take
                count =
              chunkPayloadWords wordSize word := by
          simpa [start, count] using
            table.machineWords_cell_slice hwordSize hwordList
        have hconst :
            forall logical,
              logical ∈ table.store.words.toList ->
                (chunkPayloadWords wordSize logical).length = count := by
          intro logical hmem
          have hlen : logical.length = width := by
            rcases List.mem_iff_getElem?.mp hmem with ⟨j, hlogical⟩
            exact table.word_length_of_get? (by
              simpa [Array.getElem?_toList] using hlogical)
          simpa [count, fixedWidthNatTableMachineChunkCount, hlen] using
            chunkPayloadWords_length_eq_div_add_indicator hwordSize logical
        have hbound :
            start + count <=
              (table.machineStore hwordSize).store.words.size := by
          have hphysical :=
            List.mul_add_le_flatMap_length_of_constant_length
              table.store.words.toList (chunkPayloadWords wordSize) count
              hconst hwordList
          simpa [start, FixedWidthNatTable.machineStore,
            fixedWidthNatTableMachineWords] using hphysical
        have hreads :=
          boundedPayloadWordReadValues_consecutive
            (table.machineStore hwordSize) hbound
        have hreads' :
            boundedPayloadWordReadValues (table.machineStore hwordSize)
                (fixedWidthNatTableMachineFootprint width wordSize i) =
              (((fixedWidthNatTableMachineWords table wordSize).drop start).take
                count).map some := by
          simpa only [fixedWidthNatTableMachineFootprint, start, count,
            FixedWidthNatTable.machineStore, List.toList_toArray] using hreads
        have hvalues :
            boundedPayloadWordReadValues (table.machineStore hwordSize)
                (fixedWidthNatTableMachineFootprint width wordSize i) =
              (chunkPayloadWords wordSize word).map some := by
          rw [hreads', hslice]
        rw [boundedPayloadWordReadsCosted_erase, hvalues]
        simp [fixedWidthNatTableMachineDecode,
          flattenPayloadWords_chunkPayloadWords hwordSize]
        simpa [hword, hentry] using hexact
  · have hentryNone : entries[i]? = none := by
      rw [List.getElem?_eq_none_iff]
      omega
    simp [hvalid, FixedWidthNatTable.machineStore]

theorem FixedWidthNatTable.machineStore_word_length_le
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    {word : List Bool}
    (hmem : word ∈ (table.machineStore hwordSize).store.words.toList) :
    word.length <= wordSize :=
  (table.machineStore hwordSize).word_length_le hmem

end SuccinctSpace

end RMQ
