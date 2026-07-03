import RMQ.Core.RankSelectCompressed.Base.LogChunks

namespace RMQ

namespace RankSelectSpec

/--
Canonical global block length/class table for ambient computed-RRR blocks.

The two metadata tables are stored as fixed-width payload words indexed by
block number: the first segment stores block lengths, and the second segment
stores block classes (`trueCount`).  This is the charged metadata substrate
needed by the class/length local RRR kernel.
-/
structure FixedWeightAmbientComputedRRRClassLengthTableData
    (bits : List Bool) (blocks : List (List Bool))
    (wordSize fieldWidth : Nat) where
  wordSize_pos : 0 < wordSize
  wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits
  block_code_width_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightPayloadBudget block <= wordSize
  block_length_lt_fieldWidthPow :
    forall {block : List Bool}, List.Mem block blocks ->
      block.length < 2 ^ fieldWidth

namespace FixedWeightAmbientComputedRRRClassLengthTableData

def lengthWords
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (_data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords fieldWidth
    (fixedWeightBlockLengthEntries blocks)

def classWords
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (_data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords fieldWidth
    (fixedWeightBlockClassEntries blocks)

def classLengthStore
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockClassLengthTablePayload fieldWidth blocks)
      wordSize :=
  fixedWeightBlockClassLengthBoundedStore blocks
    data.fieldWidth_le_wordSize

def lengthSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (_data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    (blockIndex : Nat) : Nat :=
  blockIndex

def classSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (_data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    (blockIndex : Nat) : Nat :=
  blocks.length + blockIndex

theorem classLengthStore_words_toList
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    data.classLengthStore.store.words.toList =
      fixedWeightBlockClassLengthTableWords fieldWidth blocks := by
  exact
    fixedWeightBlockClassLengthBoundedStore_words_toList
      blocks data.fieldWidth_le_wordSize

theorem length_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.classLengthStore.store.words[data.lengthSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE fieldWidth block.length) := by
  have hlocal :
      (data.lengthWords)[blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth block.length) :=
    fixedWeightRouteFieldTableWords_get?
      (fieldWidth := fieldWidth)
      (hget := fixedWeightBlockLengthEntries_get? hblock)
  have hlist :
      (fixedWeightBlockClassLengthTableWords fieldWidth blocks)[
          blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth block.length) := by
    have hmiddle :
        ([] ++ data.lengthWords ++ data.classWords)[0 + blockIndex]? =
          some (SuccinctSpace.natToBitsLE fieldWidth block.length) :=
      list_getElem?_append_middle_of_get?
        [] data.lengthWords data.classWords hlocal
    simpa [fixedWeightBlockClassLengthTableWords, lengthWords, classWords]
      using hmiddle
  have hstore :
      data.classLengthStore.store.words.toList[blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth block.length) := by
    rw [data.classLengthStore_words_toList]
    exact hlist
  simpa [lengthSlot, Array.getElem?_toList] using hstore

theorem class_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.classLengthStore.store.words[data.classSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) := by
  have hlocal :
      (data.classWords)[blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) :=
    fixedWeightRouteFieldTableWords_get?
      (fieldWidth := fieldWidth)
      (hget := fixedWeightBlockClassEntries_get? hblock)
  have hmiddle :
      (data.lengthWords ++ data.classWords ++ [])[data.lengthWords.length +
          blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) :=
    list_getElem?_append_middle_of_get?
      data.lengthWords data.classWords [] hlocal
  have hlist :
      (fixedWeightBlockClassLengthTableWords fieldWidth blocks)[
          blocks.length + blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) := by
    simpa [fixedWeightBlockClassLengthTableWords, lengthWords, classWords,
      fixedWeightRouteFieldTableWords, fixedWeightBlockLengthEntries,
      Nat.add_assoc] using hmiddle
  have hstore :
      data.classLengthStore.store.words.toList[
          blocks.length + blockIndex]? =
        some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block)) := by
    rw [data.classLengthStore_words_toList]
    exact hlist
  simpa [classSlot, Array.getElem?_toList] using hstore

theorem classLength_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.classLengthStore
        [data.lengthSlot blockIndex, data.classSlot blockIndex] =
      [some (SuccinctSpace.natToBitsLE fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))] := by
  simp [boundedPayloadWordReadValues,
    data.length_word_eq hblock, data.class_word_eq hblock]

def classLengthReadsCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    (blockIndex : Nat) : Costed (List (Option (List Bool))) :=
  boundedPayloadWordReadsCosted data.classLengthStore
    [data.lengthSlot blockIndex, data.classSlot blockIndex]

@[simp] theorem classLengthReadsCosted_cost
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    (blockIndex : Nat) :
    (data.classLengthReadsCosted blockIndex).cost = 2 := by
  simp [classLengthReadsCosted]

theorem classLengthReadsCosted_erase
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (data.classLengthReadsCosted blockIndex).erase =
      [some (SuccinctSpace.natToBitsLE fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))] := by
  simp [classLengthReadsCosted, data.classLength_read_values_eq hblock]

def localClassLengthBlockData
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    FixedWeightComputedRRRClassLengthBlockData
      bits.length block wordSize fieldWidth where
  wordSize_pos := data.wordSize_pos
  wordSize_le_ambient := data.wordSize_le_ambient
  fieldWidth_le_wordSize := data.fieldWidth_le_wordSize
  codeWidth_le_wordSize :=
    data.block_code_width_le (List.mem_of_getElem? hblock)
  blockLength_lt_fieldWidthPow :=
    data.block_length_lt_fieldWidthPow (List.mem_of_getElem? hblock)
  blockClass_lt_fieldWidthPow :=
    trueCount_lt_of_length_lt
      (data.block_length_lt_fieldWidthPow (List.mem_of_getElem? hblock))

def ClassLengthTableProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    Prop :=
  data.classLengthStore.store.words.toList =
      fixedWeightBlockClassLengthTableWords fieldWidth blocks /\
    SuccinctSpace.flattenPayloadWords
        data.classLengthStore.store.words.toList =
      fixedWeightBlockClassLengthTablePayload fieldWidth blocks /\
    (forall {word : List Bool},
      List.Mem word data.classLengthStore.store.words.toList ->
        word.length <= wordSize) /\
    (forall {blockIndex : Nat} {block : List Bool},
      blocks[blockIndex]? = some block ->
        boundedPayloadWordReadValues data.classLengthStore
          [data.lengthSlot blockIndex, data.classSlot blockIndex] =
        [some (SuccinctSpace.natToBitsLE fieldWidth block.length),
         some (SuccinctSpace.natToBitsLE fieldWidth (trueCount block))]) /\
    (forall {blockIndex : Nat} {block : List Bool},
      (hblock : blocks[blockIndex]? = some block) ->
        ((data.localClassLengthBlockData hblock).toDependentAuxiliaryData).DirectoryProfile)

theorem class_length_table_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {wordSize fieldWidth : Nat}
    (data :
      FixedWeightAmbientComputedRRRClassLengthTableData
        bits blocks wordSize fieldWidth) :
    data.ClassLengthTableProfile := by
  refine
    ⟨data.classLengthStore_words_toList,
      data.classLengthStore.erases,
      (fun hmem => data.classLengthStore.word_length_le_of_mem hmem),
      ?_,
      ?_⟩
  · intro blockIndex block hblock
    exact data.classLength_read_values_eq hblock
  · intro blockIndex block hblock
    exact
      FixedWeightComputedRRRClassLengthBlockData.dependent_auxiliary_data_profile
        (data.localClassLengthBlockData hblock)

end FixedWeightAmbientComputedRRRClassLengthTableData

def fixedWeightRouteFieldTableLayoutWords
    (fieldWidth : Nat)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat) : List (List Bool) :=
  fixedWeightRouteFieldTableWords fieldWidth accessBlockEntries ++
    fixedWeightRouteFieldTableWords fieldWidth accessOffsetEntries ++
      fixedWeightRouteFieldTableWords fieldWidth rankBlockEntries ++
        fixedWeightRouteFieldTableWords fieldWidth rankLocalLimitEntries ++
          fixedWeightRouteFieldTableWords fieldWidth rankBaseRankEntries ++
            fixedWeightRouteFieldTableWords fieldWidth selectBlockEntries ++
              fixedWeightRouteFieldTableWords fieldWidth
                selectLocalOccurrenceEntries ++
                fixedWeightRouteFieldTableWords fieldWidth
                  selectBlockStartEntries

def fixedWeightRouteFieldTableLayoutPayload
    (fieldWidth : Nat)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat) : List Bool :=
  SuccinctSpace.flattenPayloadWords
    (fixedWeightRouteFieldTableLayoutWords fieldWidth
      accessBlockEntries accessOffsetEntries rankBlockEntries
      rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
      selectLocalOccurrenceEntries selectBlockStartEntries)

theorem fixedWeightRouteFieldTableWords_word_length
    {fieldWidth : Nat} {entries : List Nat} {word : List Bool}
    (hmem :
      List.Mem word (fixedWeightRouteFieldTableWords fieldWidth entries)) :
    word.length = fieldWidth := by
  have hmap :
      List.Mem word
        (entries.map (SuccinctSpace.natToBitsLE fieldWidth)) := by
    simpa [fixedWeightRouteFieldTableWords] using hmem
  rcases List.mem_map.mp hmap with ⟨entry, _hentry, hword⟩
  rw [<- hword]
  exact SuccinctSpace.natToBitsLE_length fieldWidth entry

theorem fixedWeightRouteFieldTableLayoutWords_word_length
    {fieldWidth : Nat}
    {accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat}
    {word : List Bool}
    (hmem :
      List.Mem word
        (fixedWeightRouteFieldTableLayoutWords fieldWidth
          accessBlockEntries accessOffsetEntries rankBlockEntries
          rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
          selectLocalOccurrenceEntries selectBlockStartEntries)) :
    word.length = fieldWidth := by
  rw [fixedWeightRouteFieldTableLayoutWords] at hmem
  rcases List.mem_append.mp hmem with hpre | hlast
  · rcases List.mem_append.mp hpre with hpre | hselectLocal
    · rcases List.mem_append.mp hpre with hpre | hselectBlock
      · rcases List.mem_append.mp hpre with hpre | hrankBase
        · rcases List.mem_append.mp hpre with hpre | hrankLimit
          · rcases List.mem_append.mp hpre with hpre | hrankBlock
            · rcases List.mem_append.mp hpre with haccessBlock | haccessOffset
              · exact fixedWeightRouteFieldTableWords_word_length haccessBlock
              · exact fixedWeightRouteFieldTableWords_word_length haccessOffset
            · exact fixedWeightRouteFieldTableWords_word_length hrankBlock
          · exact fixedWeightRouteFieldTableWords_word_length hrankLimit
        · exact fixedWeightRouteFieldTableWords_word_length hrankBase
      · exact fixedWeightRouteFieldTableWords_word_length hselectBlock
    · exact fixedWeightRouteFieldTableWords_word_length hselectLocal
  · exact fixedWeightRouteFieldTableWords_word_length hlast

theorem fixedWeightRouteFieldTableLayoutPayload_length
    (fieldWidth : Nat)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat) :
    (fixedWeightRouteFieldTableLayoutPayload fieldWidth
        accessBlockEntries accessOffsetEntries rankBlockEntries
        rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
        selectLocalOccurrenceEntries selectBlockStartEntries).length =
      (accessBlockEntries.length + accessOffsetEntries.length +
        rankBlockEntries.length + rankLocalLimitEntries.length +
        rankBaseRankEntries.length + selectBlockEntries.length +
        selectLocalOccurrenceEntries.length +
        selectBlockStartEntries.length) * fieldWidth := by
  simp [fixedWeightRouteFieldTableLayoutPayload,
    fixedWeightRouteFieldTableLayoutWords,
    SuccinctSpace.flattenPayloadWords_append,
    fixedWeightRouteFieldTablePayload_length,
    Nat.add_mul, Nat.add_assoc]

def fixedWeightRouteFieldTableLayoutBoundedStore
    (fieldWidth : Nat)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat)
    {wordSize : Nat} (hfield : fieldWidth <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightRouteFieldTableLayoutPayload fieldWidth
        accessBlockEntries accessOffsetEntries rankBlockEntries
        rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
        selectLocalOccurrenceEntries selectBlockStartEntries)
      wordSize where
  store :=
    { words :=
        (fixedWeightRouteFieldTableLayoutWords fieldWidth
          accessBlockEntries accessOffsetEntries rankBlockEntries
          rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
          selectLocalOccurrenceEntries selectBlockStartEntries).toArray
      erases := by
        simp [fixedWeightRouteFieldTableLayoutPayload] }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (fixedWeightRouteFieldTableLayoutWords fieldWidth
            accessBlockEntries accessOffsetEntries rankBlockEntries
            rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
            selectLocalOccurrenceEntries selectBlockStartEntries) := by
      simpa using hmem
    have hlen :=
      fixedWeightRouteFieldTableLayoutWords_word_length hlist
    omega

theorem fixedWeightRouteFieldTableLayoutBoundedStore_words_toList
    (fieldWidth : Nat)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat)
    {wordSize : Nat} (hfield : fieldWidth <= wordSize) :
    (fixedWeightRouteFieldTableLayoutBoundedStore fieldWidth
        accessBlockEntries accessOffsetEntries rankBlockEntries
        rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
        selectLocalOccurrenceEntries selectBlockStartEntries hfield).store.words.toList =
      fixedWeightRouteFieldTableLayoutWords fieldWidth
        accessBlockEntries accessOffsetEntries rankBlockEntries
        rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
        selectLocalOccurrenceEntries selectBlockStartEntries := by
  rfl

/--
Eight-table fixed-width route-field layout for ambient computed-RRR metadata.

Each route field is stored in its own canonical fixed-width word table, and
the route store is aligned to the concatenation of those table words.  This is
the concrete layout layer that derives packed route metadata words from local
table slots.
-/
structure FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  routeData :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost
  fieldWidth : Nat
  fieldWidth_le_wordSize : fieldWidth <= wordSize
  accessBlockEntries : List Nat
  accessOffsetEntries : List Nat
  rankBlockEntries : List Nat
  rankLocalLimitEntries : List Nat
  rankBaseRankEntries : List Nat
  selectBlockEntries : List Nat
  selectLocalOccurrenceEntries : List Nat
  selectBlockStartEntries : List Nat
  accessBlockEntries_bound :
    forall {entry : Nat}, List.Mem entry accessBlockEntries ->
      entry < 2 ^ fieldWidth
  accessOffsetEntries_bound :
    forall {entry : Nat}, List.Mem entry accessOffsetEntries ->
      entry < 2 ^ fieldWidth
  rankBlockEntries_bound :
    forall {entry : Nat}, List.Mem entry rankBlockEntries ->
      entry < 2 ^ fieldWidth
  rankLocalLimitEntries_bound :
    forall {entry : Nat}, List.Mem entry rankLocalLimitEntries ->
      entry < 2 ^ fieldWidth
  rankBaseRankEntries_bound :
    forall {entry : Nat}, List.Mem entry rankBaseRankEntries ->
      entry < 2 ^ fieldWidth
  selectBlockEntries_bound :
    forall {entry : Nat}, List.Mem entry selectBlockEntries ->
      entry < 2 ^ fieldWidth
  selectLocalOccurrenceEntries_bound :
    forall {entry : Nat}, List.Mem entry selectLocalOccurrenceEntries ->
      entry < 2 ^ fieldWidth
  selectBlockStartEntries_bound :
    forall {entry : Nat}, List.Mem entry selectBlockStartEntries ->
      entry < 2 ^ fieldWidth
  routeStore_words_eq :
    routeData.routeStore.store.words.toList =
      fixedWeightRouteFieldTableLayoutWords fieldWidth
        accessBlockEntries accessOffsetEntries
        rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
        selectBlockEntries selectLocalOccurrenceEntries
        selectBlockStartEntries
  accessBlockLocalSlot : Nat -> Nat
  accessOffsetLocalSlot : Nat -> Nat
  rankBlockLocalSlot : Bool -> Nat -> Nat
  rankLocalLimitLocalSlot : Bool -> Nat -> Nat
  rankBaseRankLocalSlot : Bool -> Nat -> Nat
  selectBlockLocalSlot : Bool -> Nat -> Nat
  selectLocalOccurrenceLocalSlot : Bool -> Nat -> Nat
  selectBlockStartLocalSlot : Bool -> Nat -> Nat
  access_metadata_reads_eq :
    forall i,
      (routeData.accessRoute i).metadataReads =
        [accessBlockLocalSlot i,
          accessBlockEntries.length + accessOffsetLocalSlot i]
  rank_metadata_reads_eq :
    forall target pos,
      (routeData.rankRoute target pos).metadataReads =
        [accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockLocalSlot target pos,
          accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockEntries.length + rankLocalLimitLocalSlot target pos,
          accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockEntries.length + rankLocalLimitEntries.length +
            rankBaseRankLocalSlot target pos]
  select_metadata_reads_eq :
    forall target occurrence,
      (routeData.selectRoute target occurrence).metadataReads =
        [accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockEntries.length + rankLocalLimitEntries.length +
            rankBaseRankEntries.length + selectBlockLocalSlot target occurrence,
          accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockEntries.length + rankLocalLimitEntries.length +
            rankBaseRankEntries.length + selectBlockEntries.length +
            selectLocalOccurrenceLocalSlot target occurrence,
          accessBlockEntries.length + accessOffsetEntries.length +
            rankBlockEntries.length + rankLocalLimitEntries.length +
            rankBaseRankEntries.length + selectBlockEntries.length +
            selectLocalOccurrenceEntries.length +
            selectBlockStartLocalSlot target occurrence]
  access_block_entry_eq :
    forall i,
      accessBlockEntries[accessBlockLocalSlot i]? =
        some (routeData.accessRoute i).blockIndex
  access_offset_entry_eq :
    forall i,
      accessOffsetEntries[accessOffsetLocalSlot i]? =
        some (routeData.accessRoute i).offset
  rank_block_entry_eq :
    forall target pos,
      rankBlockEntries[rankBlockLocalSlot target pos]? =
        some (routeData.rankRoute target pos).blockIndex
  rank_localLimit_entry_eq :
    forall target pos,
      rankLocalLimitEntries[rankLocalLimitLocalSlot target pos]? =
        some (routeData.rankRoute target pos).localLimit
  rank_baseRank_entry_eq :
    forall target pos,
      rankBaseRankEntries[rankBaseRankLocalSlot target pos]? =
        some (routeData.rankRoute target pos).baseRank
  select_block_entry_eq :
    forall target occurrence,
      selectBlockEntries[selectBlockLocalSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).blockIndex
  select_localOccurrence_entry_eq :
    forall target occurrence,
      selectLocalOccurrenceEntries[
          selectLocalOccurrenceLocalSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).localOccurrence
  select_blockStart_entry_eq :
    forall target occurrence,
      selectBlockStartEntries[
          selectBlockStartLocalSlot target occurrence]? =
        some (routeData.selectRoute target occurrence).blockStart

namespace FixedWeightAmbientComputedRRRRouteFieldTableLayoutData

def ofCanonicalFixedWidthTables
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    {blockSize fieldWidth : Nat}
    (wordSize_pos : 0 < wordSize)
    (wordSize_le_ambient : wordSize <= Nat.log2 bits.length + 1)
    (blockSize_pos : 0 < blockSize)
    (blocks_flatten : SuccinctSpace.flattenPayloadWords blocks = bits)
    (block_length_le :
      forall {block : List Bool}, List.Mem block blocks ->
        block.length <= blockSize)
    (blockSize_le_wordSize : blockSize <= wordSize)
    (block_code_width_le :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightPayloadBudget block <= wordSize)
    (codeStore :
      SuccinctSpace.BoundedPayloadWordStore
        (fixedWeightBlockCodePayload blocks) wordSize)
    (codeStore_aligned :
      codeStore.store.words.toList = fixedWeightBlockCodeWords blocks)
    (fieldWidth_le_wordSize : fieldWidth <= wordSize)
    (accessBlockEntries accessOffsetEntries
      rankBlockEntries rankLocalLimitEntries rankBaseRankEntries
      selectBlockEntries selectLocalOccurrenceEntries
      selectBlockStartEntries : List Nat)
    (accessBlockEntries_bound :
      forall {entry : Nat}, List.Mem entry accessBlockEntries ->
        entry < 2 ^ fieldWidth)
    (accessOffsetEntries_bound :
      forall {entry : Nat}, List.Mem entry accessOffsetEntries ->
        entry < 2 ^ fieldWidth)
    (rankBlockEntries_bound :
      forall {entry : Nat}, List.Mem entry rankBlockEntries ->
        entry < 2 ^ fieldWidth)
    (rankLocalLimitEntries_bound :
      forall {entry : Nat}, List.Mem entry rankLocalLimitEntries ->
        entry < 2 ^ fieldWidth)
    (rankBaseRankEntries_bound :
      forall {entry : Nat}, List.Mem entry rankBaseRankEntries ->
        entry < 2 ^ fieldWidth)
    (selectBlockEntries_bound :
      forall {entry : Nat}, List.Mem entry selectBlockEntries ->
        entry < 2 ^ fieldWidth)
    (selectLocalOccurrenceEntries_bound :
      forall {entry : Nat}, List.Mem entry selectLocalOccurrenceEntries ->
        entry < 2 ^ fieldWidth)
    (selectBlockStartEntries_bound :
      forall {entry : Nat}, List.Mem entry selectBlockStartEntries ->
        entry < 2 ^ fieldWidth)
    (routePayload_length_eq :
      (fixedWeightRouteFieldTableLayoutPayload fieldWidth
          accessBlockEntries accessOffsetEntries rankBlockEntries
          rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
          selectLocalOccurrenceEntries selectBlockStartEntries).length =
        overhead)
    (accessRoute :
      forall i,
        FixedWeightAmbientComputedRRRAccessRoute bits blocks i)
    (rankRoute :
      forall target pos,
        FixedWeightAmbientComputedRRRRankRoute bits blocks target pos)
    (selectRoute :
      forall target occurrence,
        FixedWeightAmbientComputedRRRSelectRoute
          bits blocks target occurrence)
    (access_metadata_reads_le :
      forall i, (accessRoute i).metadataReads.length <= routeCost)
    (rank_metadata_reads_le :
      forall target pos,
        (rankRoute target pos).metadataReads.length <= routeCost)
    (select_metadata_reads_le :
      forall target occurrence,
        (selectRoute target occurrence).metadataReads.length <= routeCost)
    (local_query_cost_le :
      forall {block : List Bool}, List.Mem block blocks ->
        fixedWeightComputedRRRQueryCost block <= localQueryCost)
    (route_plus_local_le : routeCost + localQueryCost <= queryCost)
    (accessBlockLocalSlot : Nat -> Nat)
    (accessOffsetLocalSlot : Nat -> Nat)
    (rankBlockLocalSlot : Bool -> Nat -> Nat)
    (rankLocalLimitLocalSlot : Bool -> Nat -> Nat)
    (rankBaseRankLocalSlot : Bool -> Nat -> Nat)
    (selectBlockLocalSlot : Bool -> Nat -> Nat)
    (selectLocalOccurrenceLocalSlot : Bool -> Nat -> Nat)
    (selectBlockStartLocalSlot : Bool -> Nat -> Nat)
    (access_metadata_reads_eq :
      forall i,
        (accessRoute i).metadataReads =
          [accessBlockLocalSlot i,
            accessBlockEntries.length + accessOffsetLocalSlot i])
    (rank_metadata_reads_eq :
      forall target pos,
        (rankRoute target pos).metadataReads =
          [accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockLocalSlot target pos,
            accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockEntries.length + rankLocalLimitLocalSlot target pos,
            accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockEntries.length + rankLocalLimitEntries.length +
              rankBaseRankLocalSlot target pos])
    (select_metadata_reads_eq :
      forall target occurrence,
        (selectRoute target occurrence).metadataReads =
          [accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockEntries.length + rankLocalLimitEntries.length +
              rankBaseRankEntries.length +
              selectBlockLocalSlot target occurrence,
            accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockEntries.length + rankLocalLimitEntries.length +
              rankBaseRankEntries.length + selectBlockEntries.length +
              selectLocalOccurrenceLocalSlot target occurrence,
            accessBlockEntries.length + accessOffsetEntries.length +
              rankBlockEntries.length + rankLocalLimitEntries.length +
              rankBaseRankEntries.length + selectBlockEntries.length +
              selectLocalOccurrenceEntries.length +
              selectBlockStartLocalSlot target occurrence])
    (access_block_entry_eq :
      forall i,
        accessBlockEntries[accessBlockLocalSlot i]? =
          some (accessRoute i).blockIndex)
    (access_offset_entry_eq :
      forall i,
        accessOffsetEntries[accessOffsetLocalSlot i]? =
          some (accessRoute i).offset)
    (rank_block_entry_eq :
      forall target pos,
        rankBlockEntries[rankBlockLocalSlot target pos]? =
          some (rankRoute target pos).blockIndex)
    (rank_localLimit_entry_eq :
      forall target pos,
        rankLocalLimitEntries[rankLocalLimitLocalSlot target pos]? =
          some (rankRoute target pos).localLimit)
    (rank_baseRank_entry_eq :
      forall target pos,
        rankBaseRankEntries[rankBaseRankLocalSlot target pos]? =
          some (rankRoute target pos).baseRank)
    (select_block_entry_eq :
      forall target occurrence,
        selectBlockEntries[selectBlockLocalSlot target occurrence]? =
          some (selectRoute target occurrence).blockIndex)
    (select_localOccurrence_entry_eq :
      forall target occurrence,
        selectLocalOccurrenceEntries[
            selectLocalOccurrenceLocalSlot target occurrence]? =
          some (selectRoute target occurrence).localOccurrence)
    (select_blockStart_entry_eq :
      forall target occurrence,
        selectBlockStartEntries[
            selectBlockStartLocalSlot target occurrence]? =
          some (selectRoute target occurrence).blockStart) :
    FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  routeData :=
    { wordSize_pos := wordSize_pos
      wordSize_le_ambient := wordSize_le_ambient
      blockSize := blockSize
      blockSize_pos := blockSize_pos
      blocks_flatten := blocks_flatten
      block_length_le := block_length_le
      blockSize_le_wordSize := blockSize_le_wordSize
      block_code_width_le := block_code_width_le
      codeStore := codeStore
      codeStore_aligned := codeStore_aligned
      routePayload :=
        fixedWeightRouteFieldTableLayoutPayload fieldWidth
          accessBlockEntries accessOffsetEntries rankBlockEntries
          rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
          selectLocalOccurrenceEntries selectBlockStartEntries
      routeStore :=
        fixedWeightRouteFieldTableLayoutBoundedStore fieldWidth
          accessBlockEntries accessOffsetEntries rankBlockEntries
          rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
          selectLocalOccurrenceEntries selectBlockStartEntries
          fieldWidth_le_wordSize
      routePayload_length_eq := routePayload_length_eq
      accessRoute := accessRoute
      rankRoute := rankRoute
      selectRoute := selectRoute
      access_metadata_reads_le := access_metadata_reads_le
      rank_metadata_reads_le := rank_metadata_reads_le
      select_metadata_reads_le := select_metadata_reads_le
      local_query_cost_le := local_query_cost_le
      route_plus_local_le := route_plus_local_le }
  fieldWidth := fieldWidth
  fieldWidth_le_wordSize := fieldWidth_le_wordSize
  accessBlockEntries := accessBlockEntries
  accessOffsetEntries := accessOffsetEntries
  rankBlockEntries := rankBlockEntries
  rankLocalLimitEntries := rankLocalLimitEntries
  rankBaseRankEntries := rankBaseRankEntries
  selectBlockEntries := selectBlockEntries
  selectLocalOccurrenceEntries := selectLocalOccurrenceEntries
  selectBlockStartEntries := selectBlockStartEntries
  accessBlockEntries_bound := accessBlockEntries_bound
  accessOffsetEntries_bound := accessOffsetEntries_bound
  rankBlockEntries_bound := rankBlockEntries_bound
  rankLocalLimitEntries_bound := rankLocalLimitEntries_bound
  rankBaseRankEntries_bound := rankBaseRankEntries_bound
  selectBlockEntries_bound := selectBlockEntries_bound
  selectLocalOccurrenceEntries_bound :=
    selectLocalOccurrenceEntries_bound
  selectBlockStartEntries_bound := selectBlockStartEntries_bound
  routeStore_words_eq := by
    exact
      fixedWeightRouteFieldTableLayoutBoundedStore_words_toList
        fieldWidth accessBlockEntries accessOffsetEntries rankBlockEntries
        rankLocalLimitEntries rankBaseRankEntries selectBlockEntries
        selectLocalOccurrenceEntries selectBlockStartEntries
        fieldWidth_le_wordSize
  accessBlockLocalSlot := accessBlockLocalSlot
  accessOffsetLocalSlot := accessOffsetLocalSlot
  rankBlockLocalSlot := rankBlockLocalSlot
  rankLocalLimitLocalSlot := rankLocalLimitLocalSlot
  rankBaseRankLocalSlot := rankBaseRankLocalSlot
  selectBlockLocalSlot := selectBlockLocalSlot
  selectLocalOccurrenceLocalSlot := selectLocalOccurrenceLocalSlot
  selectBlockStartLocalSlot := selectBlockStartLocalSlot
  access_metadata_reads_eq := access_metadata_reads_eq
  rank_metadata_reads_eq := rank_metadata_reads_eq
  select_metadata_reads_eq := select_metadata_reads_eq
  access_block_entry_eq := access_block_entry_eq
  access_offset_entry_eq := access_offset_entry_eq
  rank_block_entry_eq := rank_block_entry_eq
  rank_localLimit_entry_eq := rank_localLimit_entry_eq
  rank_baseRank_entry_eq := rank_baseRank_entry_eq
  select_block_entry_eq := select_block_entry_eq
  select_localOccurrence_entry_eq := select_localOccurrence_entry_eq
  select_blockStart_entry_eq := select_blockStart_entry_eq

def accessBlockWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.accessBlockEntries

def accessOffsetWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.accessOffsetEntries

def rankBlockWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.rankBlockEntries

def rankLocalLimitWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.rankLocalLimitEntries

def rankBaseRankWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.rankBaseRankEntries

def selectBlockWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords data.fieldWidth data.selectBlockEntries

def selectLocalOccurrenceWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords
    data.fieldWidth data.selectLocalOccurrenceEntries

def selectBlockStartWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords
    data.fieldWidth data.selectBlockStartEntries

def layoutWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List (List Bool) :=
  fixedWeightRouteFieldTableLayoutWords data.fieldWidth
    data.accessBlockEntries data.accessOffsetEntries
    data.rankBlockEntries data.rankLocalLimitEntries
    data.rankBaseRankEntries data.selectBlockEntries
    data.selectLocalOccurrenceEntries data.selectBlockStartEntries

theorem routeStore_words_eq_layoutWords
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.routeData.routeStore.store.words.toList =
      data.layoutWords := data.routeStore_words_eq

theorem routeFieldEntry_lt
    {entries : List Nat} {fieldWidth : Nat}
    (hbound :
      forall {entry : Nat}, List.Mem entry entries ->
        entry < 2 ^ fieldWidth)
    {slot value : Nat}
    (hget : entries[slot]? = some value) :
    value < 2 ^ fieldWidth :=
  hbound (List.mem_of_getElem? hget)

theorem localWord_get?
    {fieldWidth : Nat} {entries : List Nat} {slot value : Nat}
    (hget : entries[slot]? = some value) :
    (fixedWeightRouteFieldTableWords fieldWidth entries)[slot]? =
      some (SuccinctSpace.natToBitsLE fieldWidth value) := by
  simp [fixedWeightRouteFieldTableWords, List.getElem?_map, hget]

theorem access_block_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    data.routeData.routeStore.store.words[data.accessBlockLocalSlot i]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.accessRoute i).blockIndex) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.access_block_entry_eq i)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := [])
      (mid := data.accessBlockWords)
      (post := data.accessOffsetWords ++ data.rankBlockWords ++
        data.rankLocalLimitWords ++ data.rankBaseRankWords ++
        data.selectBlockWords ++ data.selectLocalOccurrenceWords ++
        data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords] using hword

theorem access_offset_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetLocalSlot i]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.accessRoute i).offset) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.access_offset_entry_eq i)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords)
      (mid := data.accessOffsetWords)
      (post := data.rankBlockWords ++ data.rankLocalLimitWords ++
        data.rankBaseRankWords ++ data.selectBlockWords ++
        data.selectLocalOccurrenceWords ++ data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords,
    fixedWeightRouteFieldTableWords] using hword

theorem rank_block_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockLocalSlot target pos]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.rankRoute target pos).blockIndex) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.rank_block_entry_eq target pos)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords)
      (mid := data.rankBlockWords)
      (post := data.rankLocalLimitWords ++ data.rankBaseRankWords ++
        data.selectBlockWords ++ data.selectLocalOccurrenceWords ++
        data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    fixedWeightRouteFieldTableWords, Nat.add_assoc] using hword

theorem rank_localLimit_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockEntries.length +
          data.rankLocalLimitLocalSlot target pos]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.rankRoute target pos).localLimit) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.rank_localLimit_entry_eq target pos)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords ++
        data.rankBlockWords)
      (mid := data.rankLocalLimitWords)
      (post := data.rankBaseRankWords ++ data.selectBlockWords ++
        data.selectLocalOccurrenceWords ++ data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    rankLocalLimitWords, fixedWeightRouteFieldTableWords,
    Nat.add_assoc] using hword

theorem rank_baseRank_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
          data.rankBaseRankLocalSlot target pos]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.rankRoute target pos).baseRank) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.rank_baseRank_entry_eq target pos)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords ++
        data.rankBlockWords ++ data.rankLocalLimitWords)
      (mid := data.rankBaseRankWords)
      (post := data.selectBlockWords ++ data.selectLocalOccurrenceWords ++
        data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    rankLocalLimitWords, rankBaseRankWords,
    fixedWeightRouteFieldTableWords, Nat.add_assoc] using hword

theorem select_block_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
          data.rankBaseRankEntries.length +
          data.selectBlockLocalSlot target occurrence]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.selectRoute target occurrence).blockIndex) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.select_block_entry_eq target occurrence)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords ++
        data.rankBlockWords ++ data.rankLocalLimitWords ++
        data.rankBaseRankWords)
      (mid := data.selectBlockWords)
      (post := data.selectLocalOccurrenceWords ++
        data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    rankLocalLimitWords, rankBaseRankWords, selectBlockWords,
    fixedWeightRouteFieldTableWords, Nat.add_assoc] using hword

theorem select_localOccurrence_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
          data.rankBaseRankEntries.length + data.selectBlockEntries.length +
          data.selectLocalOccurrenceLocalSlot target occurrence]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.selectRoute target occurrence).localOccurrence) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.select_localOccurrence_entry_eq target occurrence)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords ++
        data.rankBlockWords ++ data.rankLocalLimitWords ++
        data.rankBaseRankWords ++ data.selectBlockWords)
      (mid := data.selectLocalOccurrenceWords)
      (post := data.selectBlockStartWords)
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    rankLocalLimitWords, rankBaseRankWords, selectBlockWords,
    selectLocalOccurrenceWords, fixedWeightRouteFieldTableWords,
    Nat.add_assoc] using hword

theorem select_blockStart_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat) :
    data.routeData.routeStore.store.words[
        data.accessBlockEntries.length + data.accessOffsetEntries.length +
          data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
          data.rankBaseRankEntries.length + data.selectBlockEntries.length +
          data.selectLocalOccurrenceEntries.length +
          data.selectBlockStartLocalSlot target occurrence]? =
      some (SuccinctSpace.natToBitsLE data.fieldWidth
        (data.routeData.selectRoute target occurrence).blockStart) := by
  have hlocal := localWord_get?
    (fieldWidth := data.fieldWidth)
    (hget := data.select_blockStart_entry_eq target occurrence)
  have hword :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.routeData.routeStore
      (pre := data.accessBlockWords ++ data.accessOffsetWords ++
        data.rankBlockWords ++ data.rankLocalLimitWords ++
        data.rankBaseRankWords ++ data.selectBlockWords ++
        data.selectLocalOccurrenceWords)
      (mid := data.selectBlockStartWords)
      (post := [])
      (by
        simpa [layoutWords, accessBlockWords, accessOffsetWords,
          rankBlockWords, rankLocalLimitWords, rankBaseRankWords,
          selectBlockWords, selectLocalOccurrenceWords,
          selectBlockStartWords, fixedWeightRouteFieldTableLayoutWords,
          List.append_assoc] using data.routeStore_words_eq_layoutWords)
      hlocal
  simpa [accessBlockWords, accessOffsetWords, rankBlockWords,
    rankLocalLimitWords, rankBaseRankWords, selectBlockWords,
    selectLocalOccurrenceWords, selectBlockStartWords,
    fixedWeightRouteFieldTableWords, Nat.add_assoc] using hword

def toPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  routeData := data.routeData
  fieldWidth := data.fieldWidth
  fieldWidth_le_wordSize := data.fieldWidth_le_wordSize
  accessBlockSlot := data.accessBlockLocalSlot
  accessOffsetSlot := fun i =>
    data.accessBlockEntries.length + data.accessOffsetLocalSlot i
  rankBlockSlot := fun target pos =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockLocalSlot target pos
  rankLocalLimitSlot := fun target pos =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length +
      data.rankLocalLimitLocalSlot target pos
  rankBaseRankSlot := fun target pos =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
      data.rankBaseRankLocalSlot target pos
  selectBlockSlot := fun target occurrence =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
      data.rankBaseRankEntries.length +
      data.selectBlockLocalSlot target occurrence
  selectLocalOccurrenceSlot := fun target occurrence =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
      data.rankBaseRankEntries.length + data.selectBlockEntries.length +
      data.selectLocalOccurrenceLocalSlot target occurrence
  selectBlockStartSlot := fun target occurrence =>
    data.accessBlockEntries.length + data.accessOffsetEntries.length +
      data.rankBlockEntries.length + data.rankLocalLimitEntries.length +
      data.rankBaseRankEntries.length + data.selectBlockEntries.length +
      data.selectLocalOccurrenceEntries.length +
      data.selectBlockStartLocalSlot target occurrence
  access_metadata_reads_eq := data.access_metadata_reads_eq
  rank_metadata_reads_eq := data.rank_metadata_reads_eq
  select_metadata_reads_eq := data.select_metadata_reads_eq
  access_block_lt := fun i =>
    routeFieldEntry_lt data.accessBlockEntries_bound
      (data.access_block_entry_eq i)
  access_offset_lt := fun i =>
    routeFieldEntry_lt data.accessOffsetEntries_bound
      (data.access_offset_entry_eq i)
  rank_block_lt := fun target pos =>
    routeFieldEntry_lt data.rankBlockEntries_bound
      (data.rank_block_entry_eq target pos)
  rank_localLimit_lt := fun target pos =>
    routeFieldEntry_lt data.rankLocalLimitEntries_bound
      (data.rank_localLimit_entry_eq target pos)
  rank_baseRank_lt := fun target pos =>
    routeFieldEntry_lt data.rankBaseRankEntries_bound
      (data.rank_baseRank_entry_eq target pos)
  select_block_lt := fun target occurrence =>
    routeFieldEntry_lt data.selectBlockEntries_bound
      (data.select_block_entry_eq target occurrence)
  select_localOccurrence_lt := fun target occurrence =>
    routeFieldEntry_lt data.selectLocalOccurrenceEntries_bound
      (data.select_localOccurrence_entry_eq target occurrence)
  select_blockStart_lt := fun target occurrence =>
    routeFieldEntry_lt data.selectBlockStartEntries_bound
      (data.select_blockStart_entry_eq target occurrence)
  access_block_word_eq := data.access_block_word_eq
  access_offset_word_eq := data.access_offset_word_eq
  rank_block_word_eq := data.rank_block_word_eq
  rank_localLimit_word_eq := data.rank_localLimit_word_eq
  rank_baseRank_word_eq := data.rank_baseRank_word_eq
  select_block_word_eq := data.select_block_word_eq
  select_localOccurrence_word_eq := data.select_localOccurrence_word_eq
  select_blockStart_word_eq := data.select_blockStart_word_eq

def LayoutPackedProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.toPackedRouteTableData.PackedRouteTableProfile /\
    data.routeData.routeStore.store.words.toList =
      data.layoutWords /\
    SuccinctSpace.flattenPayloadWords data.layoutWords =
      data.routeData.routePayload

theorem route_field_table_layout_packed_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.LayoutPackedProfile := by
  refine
    ⟨data.toPackedRouteTableData.packed_route_table_profile,
      data.routeStore_words_eq_layoutWords,
      ?_⟩
  rw [<- data.routeStore_words_eq_layoutWords]
  exact data.routeData.routeStore.erases

end FixedWeightAmbientComputedRRRRouteFieldTableLayoutData

def boundedPayloadWordStoreAppend
    {payload1 payload2 : List Bool} {wordSize : Nat}
    (left : SuccinctSpace.BoundedPayloadWordStore payload1 wordSize)
    (right : SuccinctSpace.BoundedPayloadWordStore payload2 wordSize) :
    SuccinctSpace.BoundedPayloadWordStore (payload1 ++ payload2) wordSize where
  store :=
    { words := (left.store.words.toList ++ right.store.words.toList).toArray
      erases := by
        rw [SuccinctSpace.flattenPayloadWords_append,
          left.store.erases, right.store.erases] }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (left.store.words.toList ++ right.store.words.toList) := by
      simpa using hmem
    rcases List.mem_append.mp hlist with hleft | hright
    · exact left.word_length_le hleft
    · exact right.word_length_le hright

@[simp] theorem boundedPayloadWordStoreAppend_words_toList
    {payload1 payload2 : List Bool} {wordSize : Nat}
    (left : SuccinctSpace.BoundedPayloadWordStore payload1 wordSize)
    (right : SuccinctSpace.BoundedPayloadWordStore payload2 wordSize) :
    (boundedPayloadWordStoreAppend left right).store.words.toList =
      left.store.words.toList ++ right.store.words.toList := by
  rfl

/--
Envelope combining the concrete eight-field route layout with the concrete
per-block length/class tables.

The route and class/length words are concatenated into one charged ambient
auxiliary store.  The profile below keeps the route-field readback, the
class/length readback, and the class/length-consuming ambient evaluator visible
as separate obligations.
-/
structure FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
    (bits : List Bool) (blocks : List (List Bool))
    (overhead wordSize routeCost localQueryCost queryCost : Nat) where
  routeLayout :
    FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
      bits blocks overhead wordSize routeCost localQueryCost queryCost
  classLengthTable :
    FixedWeightAmbientComputedRRRClassLengthTableData
      bits blocks wordSize routeLayout.fieldWidth
  class_length_local_query_cost_le :
    forall {block : List Bool}, List.Mem block blocks ->
      fixedWeightComputedRRRClassLengthQueryCost block <= localQueryCost

namespace FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData

def classLengthOverhead
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Nat :=
  fixedWeightBlockClassLengthTableOverhead
    data.routeLayout.fieldWidth blocks

def totalMetadataOverhead
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Nat :=
  overhead + data.classLengthOverhead

def combinedAuxPayload
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    List Bool :=
  data.routeLayout.routeData.routePayload ++
    fixedWeightBlockClassLengthTablePayload
      data.routeLayout.fieldWidth blocks

def combinedAuxStore
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    SuccinctSpace.BoundedPayloadWordStore data.combinedAuxPayload wordSize :=
  boundedPayloadWordStoreAppend data.routeLayout.routeData.routeStore
    data.classLengthTable.classLengthStore

def routeWordCount
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Nat :=
  data.routeLayout.routeData.routeStore.store.words.toList.length

def combinedLengthSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (blockIndex : Nat) : Nat :=
  data.routeWordCount + data.classLengthTable.lengthSlot blockIndex

def combinedClassSlot
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (blockIndex : Nat) : Nat :=
  data.routeWordCount + data.classLengthTable.classSlot blockIndex

theorem combinedAuxStore_words_toList
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.combinedAuxStore.store.words.toList =
      data.routeLayout.routeData.routeStore.store.words.toList ++
        data.classLengthTable.classLengthStore.store.words.toList := by
  rfl

theorem combined_route_word_eq_of
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {slot : Nat} {word : List Bool}
    (hword :
      data.routeLayout.routeData.routeStore.store.words[slot]? =
        some word) :
    data.combinedAuxStore.store.words[slot]? = some word := by
  have hlocal :
      data.routeLayout.routeData.routeStore.store.words.toList[slot]? =
        some word := by
    simpa [Array.getElem?_toList] using hword
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := [])
      (mid := data.routeLayout.routeData.routeStore.store.words.toList)
      (post := data.classLengthTable.classLengthStore.store.words.toList)
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend])
      hlocal
  simpa using hcombined

theorem combined_length_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.combinedAuxStore.store.words[data.combinedLengthSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE
        data.routeLayout.fieldWidth block.length) := by
  have hlocal :
      data.classLengthTable.classLengthStore.store.words[
          data.classLengthTable.lengthSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth block.length) :=
    data.classLengthTable.length_word_eq hblock
  have hlocalList :
      data.classLengthTable.classLengthStore.store.words.toList[
          data.classLengthTable.lengthSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth block.length) := by
    simpa [Array.getElem?_toList] using hlocal
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := data.routeLayout.routeData.routeStore.store.words.toList)
      (mid := data.classLengthTable.classLengthStore.store.words.toList)
      (post := [])
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend])
      hlocalList
  simpa [combinedLengthSlot, routeWordCount] using hcombined

theorem combined_class_word_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    data.combinedAuxStore.store.words[data.combinedClassSlot blockIndex]? =
      some (SuccinctSpace.natToBitsLE
        data.routeLayout.fieldWidth (trueCount block)) := by
  have hlocal :
      data.classLengthTable.classLengthStore.store.words[
          data.classLengthTable.classSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth (trueCount block)) :=
    data.classLengthTable.class_word_eq hblock
  have hlocalList :
      data.classLengthTable.classLengthStore.store.words.toList[
          data.classLengthTable.classSlot blockIndex]? =
        some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth (trueCount block)) := by
    simpa [Array.getElem?_toList] using hlocal
  have hcombined :=
    boundedPayloadWordStore_get?_of_words_append_middle
      data.combinedAuxStore
      (pre := data.routeLayout.routeData.routeStore.store.words.toList)
      (mid := data.classLengthTable.classLengthStore.store.words.toList)
      (post := [])
      (by simp [combinedAuxStore, boundedPayloadWordStoreAppend])
      hlocalList
  simpa [combinedClassSlot, routeWordCount] using hcombined

theorem combined_classLength_read_values_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.combinedAuxStore
        [data.combinedLengthSlot blockIndex,
         data.combinedClassSlot blockIndex] =
      [some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth (trueCount block))] := by
  simp [boundedPayloadWordReadValues,
    data.combined_length_word_eq hblock,
    data.combined_class_word_eq hblock]

def classLengthMetadataReads
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (_hblock : blocks[blockIndex]? = some block) : List Nat :=
  [data.combinedLengthSlot blockIndex, data.combinedClassSlot blockIndex]

@[simp] theorem classLengthMetadataReads_length
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    (data.classLengthMetadataReads hblock).length = 2 := by
  simp [classLengthMetadataReads]

theorem classLengthMetadataReadValues_eq
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.combinedAuxStore
        (data.classLengthMetadataReads hblock) =
      [some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth (trueCount block))] := by
  simpa [classLengthMetadataReads] using
    data.combined_classLength_read_values_eq hblock

theorem classLengthMetadataReadValues_append
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block)
    (routeReads : List Nat) :
    boundedPayloadWordReadValues data.combinedAuxStore
        (data.classLengthMetadataReads hblock ++ routeReads) =
      [some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth block.length),
       some (SuccinctSpace.natToBitsLE
          data.routeLayout.fieldWidth (trueCount block))] ++
        boundedPayloadWordReadValues data.combinedAuxStore routeReads := by
  simp [data.classLengthMetadataReadValues_eq hblock]

theorem code_read_values_singleton
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    {blockIndex : Nat} {block : List Bool}
    (hblock : blocks[blockIndex]? = some block) :
    boundedPayloadWordReadValues data.routeLayout.routeData.codeStore
        [blockIndex] =
      [some (fixedWeightPackedPayload block)] := by
  have hget :
      data.routeLayout.routeData.codeStore.store.words[blockIndex]? =
        some (fixedWeightPackedPayload block) :=
    fixedWeightAmbientBlockCodeStore_get?_of_aligned
      data.routeLayout.routeData.codeStore_aligned hblock
  simp [boundedPayloadWordReadValues, hget]

def accessAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) (_codeWords : List (Option (List Bool))) : List Nat :=
  let route := data.routeLayout.routeData.accessRoute i
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def rankAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat)
    (_codeWords : List (Option (List Bool))) : List Nat :=
  let route := data.routeLayout.routeData.rankRoute target pos
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def selectAuxReads
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat)
    (_codeWords : List (Option (List Bool))) : List Nat :=
  let route := data.routeLayout.routeData.selectRoute target occurrence
  data.classLengthMetadataReads route.block_get ++ route.metadataReads

def accessEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (i : Nat) (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Bool) :=
  let route := data.routeLayout.routeData.accessRoute i
  Costed.map (fun word => word[route.offset]?)
    (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
      auxWords codeWords)

def rankEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (pos : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed Nat :=
  let route := data.routeLayout.routeData.rankRoute target pos
  Costed.map (fun localRank => route.baseRank + localRank)
    (Costed.bind
      (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        auxWords codeWords) fun word =>
      (RAM.rankBoolWordPrefix target word route.localLimit).toCosted)

def selectEvalCosted
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (target : Bool) (occurrence : Nat)
    (codeWords auxWords : List (Option (List Bool))) :
    Costed (Option Nat) :=
  let route := data.routeLayout.routeData.selectRoute target occurrence
  Costed.map (fun local? =>
      local?.map (fun offset => route.blockStart + offset))
    (Costed.bind
      (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
        auxWords codeWords) fun word =>
      (RAM.selectBoolWord target word route.localOccurrence).toCosted)

def toCombinedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteTableData
      bits blocks data.totalMetadataOverhead wordSize
      routeCost localQueryCost queryCost where
  wordSize_pos := data.routeLayout.routeData.wordSize_pos
  wordSize_le_ambient := data.routeLayout.routeData.wordSize_le_ambient
  blockSize := data.routeLayout.routeData.blockSize
  blockSize_pos := data.routeLayout.routeData.blockSize_pos
  blocks_flatten := data.routeLayout.routeData.blocks_flatten
  block_length_le := data.routeLayout.routeData.block_length_le
  blockSize_le_wordSize := data.routeLayout.routeData.blockSize_le_wordSize
  block_code_width_le := data.routeLayout.routeData.block_code_width_le
  codeStore := data.routeLayout.routeData.codeStore
  codeStore_aligned := data.routeLayout.routeData.codeStore_aligned
  routePayload := data.combinedAuxPayload
  routeStore := data.combinedAuxStore
  routePayload_length_eq := by
    simp [combinedAuxPayload, totalMetadataOverhead, classLengthOverhead,
      fixedWeightBlockClassLengthTablePayload_length,
      data.routeLayout.routeData.routePayload_length_eq]
  accessRoute := data.routeLayout.routeData.accessRoute
  rankRoute := data.routeLayout.routeData.rankRoute
  selectRoute := data.routeLayout.routeData.selectRoute
  access_metadata_reads_le := data.routeLayout.routeData.access_metadata_reads_le
  rank_metadata_reads_le := data.routeLayout.routeData.rank_metadata_reads_le
  select_metadata_reads_le := data.routeLayout.routeData.select_metadata_reads_le
  local_query_cost_le := data.routeLayout.routeData.local_query_cost_le
  route_plus_local_le := data.routeLayout.routeData.route_plus_local_le

def toCombinedPackedRouteTableData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableData
      bits blocks data.totalMetadataOverhead wordSize
      routeCost localQueryCost queryCost where
  routeData := data.toCombinedRouteTableData
  fieldWidth := data.routeLayout.fieldWidth
  fieldWidth_le_wordSize := data.routeLayout.fieldWidth_le_wordSize
  accessBlockSlot := data.routeLayout.toPackedRouteTableData.accessBlockSlot
  accessOffsetSlot := data.routeLayout.toPackedRouteTableData.accessOffsetSlot
  rankBlockSlot := data.routeLayout.toPackedRouteTableData.rankBlockSlot
  rankLocalLimitSlot :=
    data.routeLayout.toPackedRouteTableData.rankLocalLimitSlot
  rankBaseRankSlot :=
    data.routeLayout.toPackedRouteTableData.rankBaseRankSlot
  selectBlockSlot := data.routeLayout.toPackedRouteTableData.selectBlockSlot
  selectLocalOccurrenceSlot :=
    data.routeLayout.toPackedRouteTableData.selectLocalOccurrenceSlot
  selectBlockStartSlot :=
    data.routeLayout.toPackedRouteTableData.selectBlockStartSlot
  access_metadata_reads_eq := data.routeLayout.access_metadata_reads_eq
  rank_metadata_reads_eq := data.routeLayout.rank_metadata_reads_eq
  select_metadata_reads_eq := data.routeLayout.select_metadata_reads_eq
  access_block_lt := data.routeLayout.toPackedRouteTableData.access_block_lt
  access_offset_lt := data.routeLayout.toPackedRouteTableData.access_offset_lt
  rank_block_lt := data.routeLayout.toPackedRouteTableData.rank_block_lt
  rank_localLimit_lt :=
    data.routeLayout.toPackedRouteTableData.rank_localLimit_lt
  rank_baseRank_lt := data.routeLayout.toPackedRouteTableData.rank_baseRank_lt
  select_block_lt := data.routeLayout.toPackedRouteTableData.select_block_lt
  select_localOccurrence_lt :=
    data.routeLayout.toPackedRouteTableData.select_localOccurrence_lt
  select_blockStart_lt :=
    data.routeLayout.toPackedRouteTableData.select_blockStart_lt
  access_block_word_eq := fun i =>
    data.combined_route_word_eq_of
      (data.routeLayout.access_block_word_eq i)
  access_offset_word_eq := fun i =>
    data.combined_route_word_eq_of
      (data.routeLayout.access_offset_word_eq i)
  rank_block_word_eq := fun target pos =>
    data.combined_route_word_eq_of
      (data.routeLayout.rank_block_word_eq target pos)
  rank_localLimit_word_eq := fun target pos =>
    data.combined_route_word_eq_of
      (data.routeLayout.rank_localLimit_word_eq target pos)
  rank_baseRank_word_eq := fun target pos =>
    data.combined_route_word_eq_of
      (data.routeLayout.rank_baseRank_word_eq target pos)
  select_block_word_eq := fun target occurrence =>
    data.combined_route_word_eq_of
      (data.routeLayout.select_block_word_eq target occurrence)
  select_localOccurrence_word_eq := fun target occurrence =>
    data.combined_route_word_eq_of
      (data.routeLayout.select_localOccurrence_word_eq
        target occurrence)
  select_blockStart_word_eq := fun target occurrence =>
    data.combined_route_word_eq_of
      (data.routeLayout.select_blockStart_word_eq target occurrence)

def toClassLengthAmbientBlockCompositionData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    FixedWeightAmbientBlockCompositionData
      bits blocks data.totalMetadataOverhead wordSize queryCost := by
  refine
    { wordSize_pos := data.routeLayout.routeData.wordSize_pos
      wordSize_le_ambient := data.routeLayout.routeData.wordSize_le_ambient
      blockSize := data.routeLayout.routeData.blockSize
      blockSize_pos := data.routeLayout.routeData.blockSize_pos
      blocks_flatten := data.routeLayout.routeData.blocks_flatten
      block_length_le := data.routeLayout.routeData.block_length_le
      blockSize_le_wordSize :=
        data.routeLayout.routeData.blockSize_le_wordSize
      block_code_width_le :=
        data.routeLayout.routeData.block_code_width_le
      codeStore := data.routeLayout.routeData.codeStore
      auxPayload := data.combinedAuxPayload
      auxStore := data.combinedAuxStore
      aux_length_eq := data.toCombinedRouteTableData.routePayload_length_eq
      accessCodeReads := fun i =>
        [(data.routeLayout.routeData.accessRoute i).blockIndex]
      accessAuxReads := data.accessAuxReads
      rankCodeReads := fun target pos =>
        [(data.routeLayout.routeData.rankRoute target pos).blockIndex]
      rankAuxReads := data.rankAuxReads
      selectCodeReads := fun target occurrence =>
        [(data.routeLayout.routeData.selectRoute
          target occurrence).blockIndex]
      selectAuxReads := data.selectAuxReads
      accessEvalCosted := data.accessEvalCosted
      rankEvalCosted := data.rankEvalCosted
      selectEvalCosted := data.selectEvalCosted
      access_query_cost_le := ?_
      rank_query_cost_le := ?_
      select_query_cost_le := ?_
      access_eval_exact := ?_
      rank_eval_exact := ?_
      select_eval_exact := ?_ }
  · intro i
    let route := data.routeLayout.routeData.accessRoute i
    have hroute := data.routeLayout.routeData.access_metadata_reads_le i
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hlocal := data.class_length_local_query_cost_le hmem
    have htotal := data.routeLayout.routeData.route_plus_local_le
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    have hclassLength :
        fixedWeightClassLengthFromReadValues
            (some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                route.block.length) ::
              some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                (trueCount route.block)) ::
              boundedPayloadWordReadValues data.combinedAuxStore
                route.metadataReads) =
          (route.block.length, trueCount route.block) :=
      fixedWeightClassLengthFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
    simp [accessEvalCosted, accessAuxReads, route, hcode, haux,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength] at *
    omega
  · intro target pos
    let route := data.routeLayout.routeData.rankRoute target pos
    have hroute :=
      data.routeLayout.routeData.rank_metadata_reads_le target pos
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hlocal := data.class_length_local_query_cost_le hmem
    have htotal := data.routeLayout.routeData.route_plus_local_le
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    have hclassLength :
        fixedWeightClassLengthFromReadValues
            (some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                route.block.length) ::
              some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                (trueCount route.block)) ::
              boundedPayloadWordReadValues data.combinedAuxStore
                route.metadataReads) =
          (route.block.length, trueCount route.block) :=
      fixedWeightClassLengthFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
    simp [rankEvalCosted, rankAuxReads, route, hcode, haux,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength] at *
    omega
  · intro target occurrence
    let route :=
      data.routeLayout.routeData.selectRoute target occurrence
    have hroute :=
      data.routeLayout.routeData.select_metadata_reads_le
        target occurrence
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hlocal := data.class_length_local_query_cost_le hmem
    have htotal := data.routeLayout.routeData.route_plus_local_le
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    have hclassLength :
        fixedWeightClassLengthFromReadValues
            (some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                route.block.length) ::
              some (SuccinctSpace.natToBitsLE data.routeLayout.fieldWidth
                (trueCount route.block)) ::
              boundedPayloadWordReadValues data.combinedAuxStore
                route.metadataReads) =
          (route.block.length, trueCount route.block) :=
      fixedWeightClassLengthFromReadValues_encoded_prefix
        (boundedPayloadWordReadValues data.combinedAuxStore
          route.metadataReads) hlen hclass
    simp [selectEvalCosted, selectAuxReads, route, hcode, haux,
      fixedWeightComputedRRRClassLengthQueryCost,
      fixedWeightComputedRRRDecodeTicks, hclassLength] at *
    omega
  · intro i
    let route := data.routeLayout.routeData.accessRoute i
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    simp only [accessEvalCosted, accessAuxReads, Costed.erase_map]
    change
      (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
          (boundedPayloadWordReadValues data.combinedAuxStore
            (data.classLengthMetadataReads route.block_get ++
              route.metadataReads))
          (boundedPayloadWordReadValues
            data.routeLayout.routeData.codeStore
            [route.blockIndex])).erase[route.offset]? =
        bits[i]?
    rw [hcode]
    rw [haux]
    rw [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_prefix
      (boundedPayloadWordReadValues data.combinedAuxStore
        route.metadataReads) hlen hclass]
    exact route.access_exact
  · intro target pos
    let route := data.routeLayout.routeData.rankRoute target pos
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    have hrun :=
      Succinct.rankBoolWordPrefix_toCosted_run
        target route.block route.localLimit
    simp only [rankEvalCosted, rankAuxReads, Costed.erase_map,
      Costed.erase_bind]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target
              (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
                (boundedPayloadWordReadValues data.combinedAuxStore
                  (data.classLengthMetadataReads route.block_get ++
                    route.metadataReads))
                (boundedPayloadWordReadValues
                  data.routeLayout.routeData.codeStore
                  [route.blockIndex])).erase
              route.localLimit).toCosted.value =
        Succinct.rankPrefix target bits pos
    rw [hcode]
    rw [haux]
    rw [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_prefix
      (boundedPayloadWordReadValues data.combinedAuxStore
        route.metadataReads) hlen hclass]
    change
      route.baseRank +
          (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
        Succinct.rankPrefix target bits pos
    have hram :
        (RAM.rankBoolWordPrefix target route.block route.localLimit).toCosted.value =
          Succinct.rankPrefix target route.block route.localLimit := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hram]
    exact route.rank_exact
  · intro target occurrence
    let route :=
      data.routeLayout.routeData.selectRoute target occurrence
    have hmem : List.Mem route.block blocks :=
      List.mem_of_getElem? route.block_get
    have hcode := data.code_read_values_singleton route.block_get
    have haux :=
      data.classLengthMetadataReadValues_append
        route.block_get route.metadataReads
    have hlen :=
      data.classLengthTable.block_length_lt_fieldWidthPow hmem
    have hclass := trueCount_lt_of_length_lt hlen
    have hrun :=
      Succinct.selectBoolWord_toCosted_run
        target route.block route.localOccurrence
    simp only [selectEvalCosted, selectAuxReads, Costed.erase_map,
      Costed.erase_bind]
    change
      ((RAM.selectBoolWord target
              (fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted
                (boundedPayloadWordReadValues data.combinedAuxStore
                  (data.classLengthMetadataReads route.block_get ++
                    route.metadataReads))
                (boundedPayloadWordReadValues
                  data.routeLayout.routeData.codeStore
                  [route.blockIndex])).erase
              route.localOccurrence).toCosted.value).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    rw [hcode]
    rw [haux]
    rw [fixedWeightComputedRRRDecodeFromClassLengthReadValuesCosted_erase_prefix
      (boundedPayloadWordReadValues data.combinedAuxStore
        route.metadataReads) hlen hclass]
    change
      ((RAM.selectBoolWord target route.block
              route.localOccurrence).toCosted.value).map
          (fun offset => route.blockStart + offset) =
        Succinct.select target bits occurrence
    have hselect :
        (RAM.selectBoolWord target route.block
            route.localOccurrence).toCosted.value =
          Succinct.select target route.block route.localOccurrence := by
      simpa [Costed.run] using congrArg Prod.fst hrun
    rw [hselect]
    exact route.select_exact

def RouteClassLengthEnvelopeProfile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    Prop :=
  data.routeLayout.LayoutPackedProfile /\
    data.classLengthTable.ClassLengthTableProfile /\
    data.toCombinedPackedRouteTableData.PackedRouteTableProfile /\
    data.toClassLengthAmbientBlockCompositionData.DirectoryProfile /\
    data.routeLayout.routeData.routePayload.length = overhead /\
    (fixedWeightBlockClassLengthTablePayload
        data.routeLayout.fieldWidth blocks).length =
      data.classLengthOverhead /\
    data.toCombinedRouteTableData.routePayload.length =
      data.totalMetadataOverhead /\
    SuccinctSpace.flattenPayloadWords
        data.combinedAuxStore.store.words.toList =
      data.combinedAuxPayload /\
    data.totalMetadataOverhead =
      overhead + data.classLengthOverhead /\
    (forall {blockIndex : Nat} {block : List Bool},
      blocks[blockIndex]? = some block ->
        boundedPayloadWordReadValues
            data.classLengthTable.classLengthStore
            [data.classLengthTable.lengthSlot blockIndex,
             data.classLengthTable.classSlot blockIndex] =
         [some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth block.length),
           some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth (trueCount block))]) /\
    (forall {blockIndex : Nat} {block : List Bool},
      blocks[blockIndex]? = some block ->
        boundedPayloadWordReadValues
            data.combinedAuxStore
            [data.combinedLengthSlot blockIndex,
             data.combinedClassSlot blockIndex] =
          [some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth block.length),
           some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth (trueCount block))]) /\
    (forall {blockIndex : Nat} {block : List Bool},
      (hblock : blocks[blockIndex]? = some block) ->
        ((data.classLengthTable.localClassLengthBlockData hblock).toDependentAuxiliaryData).DirectoryProfile) /\
    (forall i,
      let route := data.routeLayout.routeData.accessRoute i
      (data.toClassLengthAmbientBlockCompositionData.accessCosted i).cost <=
          queryCost /\
        boundedPayloadWordReadValues data.combinedAuxStore
            (data.classLengthMetadataReads route.block_get ++
              route.metadataReads) =
          [some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth route.block.length),
           some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads) /\
    (forall target pos,
      let route := data.routeLayout.routeData.rankRoute target pos
      (data.toClassLengthAmbientBlockCompositionData.rankCosted
          target pos).cost <= queryCost /\
        boundedPayloadWordReadValues data.combinedAuxStore
            (data.classLengthMetadataReads route.block_get ++
              route.metadataReads) =
          [some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth route.block.length),
           some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads) /\
    (forall target occurrence,
      let route :=
        data.routeLayout.routeData.selectRoute target occurrence
      (data.toClassLengthAmbientBlockCompositionData.selectCosted
          target occurrence).cost <= queryCost /\
        boundedPayloadWordReadValues data.combinedAuxStore
            (data.classLengthMetadataReads route.block_get ++
              route.metadataReads) =
          [some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth route.block.length),
           some (SuccinctSpace.natToBitsLE
              data.routeLayout.fieldWidth (trueCount route.block))] ++
            boundedPayloadWordReadValues data.combinedAuxStore
              route.metadataReads)

theorem route_class_length_table_envelope_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits blocks overhead wordSize routeCost localQueryCost queryCost) :
    data.RouteClassLengthEnvelopeProfile := by
  refine
    ⟨data.routeLayout.route_field_table_layout_packed_profile,
      data.classLengthTable.class_length_table_profile,
      data.toCombinedPackedRouteTableData.packed_route_table_profile,
      data.toClassLengthAmbientBlockCompositionData.directory_profile,
      data.routeLayout.routeData.routePayload_length_eq,
      ?_,
      data.toCombinedRouteTableData.routePayload_length_eq,
      data.combinedAuxStore.erases,
      rfl,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_,
      ?_⟩
  · exact
      fixedWeightBlockClassLengthTablePayload_length
        data.routeLayout.fieldWidth blocks
  · intro blockIndex block hblock
    exact data.classLengthTable.classLength_read_values_eq hblock
  · intro blockIndex block hblock
    exact data.combined_classLength_read_values_eq hblock
  · intro blockIndex block hblock
    exact
      FixedWeightComputedRRRClassLengthBlockData.dependent_auxiliary_data_profile
        (data.classLengthTable.localClassLengthBlockData hblock)
  · intro i
    exact
      ⟨data.toClassLengthAmbientBlockCompositionData.accessCosted_cost_le i,
        data.classLengthMetadataReadValues_append
          (data.routeLayout.routeData.accessRoute i).block_get
          (data.routeLayout.routeData.accessRoute i).metadataReads⟩
  · intro target pos
    exact
      ⟨data.toClassLengthAmbientBlockCompositionData.rankCosted_cost_le
          target pos,
        data.classLengthMetadataReadValues_append
          (data.routeLayout.routeData.rankRoute target pos).block_get
          (data.routeLayout.routeData.rankRoute target pos).metadataReads⟩
  · intro target occurrence
    exact
      ⟨data.toClassLengthAmbientBlockCompositionData.selectCosted_cost_le
          target occurrence,
        data.classLengthMetadataReadValues_append
          (data.routeLayout.routeData.selectRoute
            target occurrence).block_get
          (data.routeLayout.routeData.selectRoute
            target occurrence).metadataReads⟩

end FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData

/-- Combined auxiliary budget for route metadata plus class/length metadata. -/
def fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
    (slots : Nat) (classLengthOverhead : Nat -> Nat) : Nat -> Nat :=
  fun n =>
    fixedWeightAmbientBlockAuxiliaryOverhead slots n +
      classLengthOverhead n

theorem fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead_littleO
    (slots : Nat) {classLengthOverhead : Nat -> Nat}
    (hclassLength :
      SuccinctSpace.LittleOLinear classLengthOverhead) :
    SuccinctSpace.LittleOLinear
      (fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
        slots classLengthOverhead) := by
  exact
    (fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots).add
      hclassLength

/--
Family of route-field layouts paired with concrete class/length tables.

The route payload keeps the existing sampled-directory budget.  The concrete
class/length table payload is accounted for by the separate
`classLengthOverhead` function so a later block-size construction can prove the
usual `o(n)` condition without weakening the pointwise readback theorem.
-/
structure FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
    (slots routeCost localQueryCost queryCost : Nat)
    (classLengthOverhead : Nat -> Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  classLengthOverhead_littleO :
    SuccinctSpace.LittleOLinear classLengthOverhead
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost
  classLengthOverhead_le :
    forall bits : List Bool,
      ((component bits).classLengthOverhead <=
        classLengthOverhead bits.length)

namespace FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily

def overhead (slots : Nat) (classLengthOverhead : Nat -> Nat) :
    Nat -> Nat :=
  fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead
    slots classLengthOverhead

def compressedOverhead
    (slots : Nat) (classLengthOverhead primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  fun n =>
    primaryOverhead n + overhead slots classLengthOverhead n

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      ((family.componentData bits).totalMetadataOverhead)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toClassLengthAmbientBlockCompositionData

theorem route_class_length_table_envelope_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead) :
    SuccinctSpace.LittleOLinear
        (overhead slots classLengthOverhead) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              overhead slots classLengthOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            overhead slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact
      fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead_littleO
        slots family.classLengthOverhead_littleO
  · intro bits
    let data := family.componentData bits
    let directory := family.directory bits
    have hbounded := directory.word_bounded_directory_profile
    have hclass :
        data.classLengthOverhead <= classLengthOverhead bits.length := by
      simpa [data, componentData] using
        family.classLengthOverhead_le bits
    have haux_le :
        data.totalMetadataOverhead <=
          overhead slots classLengthOverhead bits.length := by
      simp [overhead,
        fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead,
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.totalMetadataOverhead]
      omega
    have haux_le_component :
        (family.componentData bits).totalMetadataOverhead <=
          overhead slots classLengthOverhead bits.length := by
      simpa [data] using haux_le
    exact
      ⟨data.route_class_length_table_envelope_profile,
        directory.directory_profile,
        directory.payload_length,
        by
          rw [directory.payload_length]
          have haux := haux_le_component
          omega,
        directory.aux_length_eq,
        by
          rw [directory.aux_length_eq]
          exact haux_le,
        data.routeLayout.routeData.blocks_flatten,
        hbounded.2.1,
        hbounded.2.2,
        (fun i =>
          ⟨directory.accessCosted_cost_le i,
            directory.accessCosted_erase i⟩),
        (fun target pos =>
          ⟨directory.rankCosted_cost_le target pos,
            directory.rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨directory.selectCosted_cost_le target occurrence,
            directory.selectCosted_erase target occurrence⟩)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots classLengthOverhead primaryOverhead) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead
                slots classLengthOverhead primaryOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            overhead slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  constructor
  · exact
      hprimaryO.add
        (fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead_littleO
          slots family.classLengthOverhead_littleO)
  · intro bits
    let data := family.componentData bits
    let directory := family.directory bits
    have hbounded := directory.word_bounded_directory_profile
    have hclass :
        data.classLengthOverhead <= classLengthOverhead bits.length := by
      simpa [data, componentData] using
        family.classLengthOverhead_le bits
    have haux_le :
        data.totalMetadataOverhead <=
          overhead slots classLengthOverhead bits.length := by
      simp [overhead,
        fixedWeightAmbientComputedRRRRouteClassLengthCombinedOverhead,
        FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.totalMetadataOverhead]
      omega
    have haux_le_component :
        (family.componentData bits).totalMetadataOverhead <=
          overhead slots classLengthOverhead bits.length := by
      simpa [data] using haux_le
    have hprimaryBits := hprimary bits
    exact
      ⟨data.route_class_length_table_envelope_profile,
        directory.directory_profile,
        directory.payload_length,
        by
          rw [directory.payload_length]
          simp [compressedOverhead]
          have haux := haux_le_component
          omega,
        directory.aux_length_eq,
        by
          rw [directory.aux_length_eq]
          exact haux_le,
        data.routeLayout.routeData.blocks_flatten,
        hbounded.2.1,
        hbounded.2.2,
        (fun i =>
          ⟨directory.accessCosted_cost_le i,
            directory.accessCosted_erase i⟩),
        (fun target pos =>
          ⟨directory.rankCosted_cost_le target pos,
            directory.rankCosted_erase target pos⟩),
        (fun target occurrence =>
          ⟨directory.selectCosted_cost_le target occurrence,
            directory.selectCosted_erase target occurrence⟩)⟩

theorem word_bounded_compressed_profile_of_log_chunk_blocks
    {slots routeCost localQueryCost queryCost : Nat}
    {classLengthOverhead : Nat -> Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost classLengthOverhead)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightLogChunkBlocksWithSentinel bits) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead
          slots classLengthOverhead
          fixedWeightLogChunkBlockCountBoundWithSentinel) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead
                slots classLengthOverhead
                fixedWeightLogChunkBlockCountBoundWithSentinel bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            overhead slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    word_bounded_compressed_profile_of_primary_budget
      family fixedWeightLogChunkBlockCountBoundWithSentinel
      fixedWeightLogChunkBlockCountBoundWithSentinel_littleO
      (by
        intro bits
        simpa [hblocks bits] using
          fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound bits)

end FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily

/--
Log-chunk specialization of the route/class-length envelope family.

This fixes the block decomposition to sentinel log chunks and fixes the
class/length metadata budget to the narrow `log log n` field-width budget.
The remaining family component is still the charged route/class-length
envelope data; no proof-only decoded bit wrapper is introduced here.
-/
structure FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
        bits (fixedWeightLogChunkBlocksWithSentinel bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost
  classLengthOverhead_le :
    forall bits : List Bool,
      ((component bits).classLengthOverhead <=
        fixedWeightLogChunkClassLengthOverhead bits.length)

namespace FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily

def overhead (slots : Nat) : Nat -> Nat :=
  FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
    slots fixedWeightLogChunkClassLengthOverhead

def compressedOverhead (slots : Nat) : Nat -> Nat :=
  FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
    slots fixedWeightLogChunkClassLengthOverhead
    fixedWeightLogChunkBlockCountBoundWithSentinel

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
      bits (fixedWeightLogChunkBlocksWithSentinel bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (fixedWeightLogChunkBlocksWithSentinel bits)
      ((family.componentData bits).totalMetadataOverhead)
      (family.wordSize bits.length) queryCost :=
  (family.componentData bits).toClassLengthAmbientBlockCompositionData

def toRouteClassLengthTableEnvelopeFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
      slots routeCost localQueryCost queryCost
      fixedWeightLogChunkClassLengthOverhead where
  wordSize := family.wordSize
  blocks := fixedWeightLogChunkBlocksWithSentinel
  classLengthOverhead_littleO :=
    fixedWeightLogChunkClassLengthOverhead_littleO
  component bits := family.componentData bits
  classLengthOverhead_le := by
    intro bits
    simpa [componentData] using family.classLengthOverhead_le bits

/--
Concrete log-chunk compressed/FID bridge for charged route/class-length
envelopes.

The theorem consumes the log-chunk primary block-code budget and the narrow
class/length metadata overhead.  The final statement has no arbitrary block
family, no `hblocks` premise, and no separate primary-budget hypothesis.
-/
theorem word_bounded_compressed_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (compressedOverhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        let directory := family.directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget
                (fixedWeightLogChunkBlocksWithSentinel bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead slots bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <= overhead slots bits.length /\
          SuccinctSpace.flattenPayloadWords
              (fixedWeightLogChunkBlocksWithSentinel bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  have hprofile :=
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.word_bounded_compressed_profile_of_log_chunk_blocks
      family.toRouteClassLengthTableEnvelopeFamily
      (by
        intro bits
        rfl)
  simpa [compressedOverhead, overhead, componentData, directory,
    toRouteClassLengthTableEnvelopeFamily,
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.componentData,
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.directory]
    using hprofile

end FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily

theorem no_fixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRLogChunkRouteClassLengthTableEnvelopeFamily
        slots routeCost localQueryCost queryCost) :
    False := by
  let n := 2 ^ localQueryCost
  let bits := List.replicate n false
  let blockSize := fixedWeightLogChunkBlockSize bits.length
  have hn_pos : 0 < n := by
    exact Nat.pow_pos (by omega : 0 < 2)
  have hbits_len : bits.length = n := by
    simp [bits]
  have hblockSize_pos : 0 < blockSize := by
    simp [blockSize, fixedWeightLogChunkBlockSize]
  have hblockSize_le_len : blockSize <= bits.length := by
    have hbits_pos : 0 < bits.length := by
      simpa [bits, n] using hn_pos
    have hnonzero : bits.length ≠ 0 := Nat.ne_of_gt hbits_pos
    have hpow :
        Nat.log2 bits.length + 1 <= 2 ^ Nat.log2 bits.length :=
      SuccinctSpace.nat_succ_le_two_pow (Nat.log2 bits.length)
    exact Nat.le_trans (by
      simpa [blockSize, fixedWeightLogChunkBlockSize] using hpow)
      (Nat.log2_self_le hnonzero)
  have hstart : 0 * blockSize < bits.length := by
    simpa [bits, n] using hn_pos
  rcases
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (wordSize := blockSize) hblockSize_pos
        (payload := bits) (i := 0) hstart with
    ⟨block, hchunk⟩
  have hchunkFixed :
      (fixedWeightChunkBlocks blockSize bits)[0]? = some block := by
    simpa [fixedWeightChunkBlocks] using hchunk
  have hblock_get :
      (fixedWeightLogChunkBlocksWithSentinel bits)[0]? = some block := by
    simpa [fixedWeightLogChunkBlocksWithSentinel, blockSize] using
      fixedWeightChunkBlocksWithSentinel_get_chunk hchunkFixed
  have hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits) :=
    List.mem_of_getElem? hblock_get
  have hchunk_eq :=
    SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
  have hblock_le_n : blockSize <= n := by
    simpa [bits] using hblockSize_le_len
  have hblock_eq : block = List.replicate blockSize false := by
    simpa [bits, hblock_le_n] using hchunk_eq
  have hcost_le :
      fixedWeightComputedRRRClassLengthQueryCost block <=
        localQueryCost :=
    (family.componentData bits).class_length_local_query_cost_le hmem
  have hcost_eq :
      fixedWeightComputedRRRClassLengthQueryCost block =
        blockSize + 5 := by
    rw [hblock_eq]
    exact fixedWeightComputedRRRClassLengthQueryCost_replicate_false blockSize
  have hlog : localQueryCost <= Nat.log2 (2 ^ localQueryCost) := by
    have hnonzero : 2 ^ localQueryCost ≠ 0 :=
      Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))
    exact (Nat.le_log2 hnonzero).2 (Nat.le_refl _)
  have hgt : localQueryCost < blockSize + 5 := by
    have hblock_def :
        blockSize = Nat.log2 (2 ^ localQueryCost) + 1 := by
      simp [blockSize, fixedWeightLogChunkBlockSize, bits, n]
    omega
  omega

namespace FixedWeightAmbientComputedRRRRouteFieldTableLayoutData

/--
Build the route/class-length envelope from an eight-table route layout.

The side conditions are the concrete block-size discipline needed by the local
class/length RRR kernel: the layout field width can encode every block length,
and the family-level local query cap covers the class/length decoder for any
block below the route layout's block-size bound.
-/
def toRouteClassLengthTableEnvelopeData
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (hblockSize_lt_fieldWidthPow :
      data.routeData.blockSize < 2 ^ data.fieldWidth)
    (hlocalCost :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        data.routeData.blockSize <= localQueryCost) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData
      bits blocks overhead wordSize routeCost localQueryCost queryCost where
  routeLayout := data
  classLengthTable :=
    { wordSize_pos := data.routeData.wordSize_pos
      wordSize_le_ambient := data.routeData.wordSize_le_ambient
      fieldWidth_le_wordSize := data.fieldWidth_le_wordSize
      blocks_flatten := data.routeData.blocks_flatten
      block_code_width_le := data.routeData.block_code_width_le
      block_length_lt_fieldWidthPow := by
        intro block hmem
        have hle := data.routeData.block_length_le hmem
        omega }
  class_length_local_query_cost_le := by
    intro block hmem
    exact
      fixedWeightComputedRRRClassLengthQueryCost_le_of_block_length_le
        (blockSize := data.routeData.blockSize)
        (data.routeData.block_length_le hmem)
        hlocalCost

theorem route_field_table_layout_to_route_class_length_table_envelope_profile
    {bits : List Bool} {blocks : List (List Bool)}
    {overhead wordSize routeCost localQueryCost queryCost : Nat}
    (data :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits blocks overhead wordSize routeCost localQueryCost queryCost)
    (hblockSize_lt_fieldWidthPow :
      data.routeData.blockSize < 2 ^ data.fieldWidth)
    (hlocalCost :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        data.routeData.blockSize <= localQueryCost) :
    (data.toRouteClassLengthTableEnvelopeData
      hblockSize_lt_fieldWidthPow hlocalCost).RouteClassLengthEnvelopeProfile := by
  exact
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.route_class_length_table_envelope_profile
      (data.toRouteClassLengthTableEnvelopeData
        hblockSize_lt_fieldWidthPow hlocalCost)

end FixedWeightAmbientComputedRRRRouteFieldTableLayoutData

/-- Family of eight-table fixed-width route-field layouts. -/
structure FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
    (slots routeCost localQueryCost queryCost : Nat) where
  wordSize : Nat -> Nat
  blocks : List Bool -> List (List Bool)
  component :
    forall bits : List Bool,
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
        bits (blocks bits)
        (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
        (wordSize bits.length) routeCost localQueryCost queryCost

namespace FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

def overhead (slots : Nat) : Nat -> Nat :=
  fixedWeightAmbientBlockAuxiliaryOverhead slots

def compressedOverhead (slots : Nat) (primaryOverhead : Nat -> Nat) :
    Nat -> Nat :=
  FixedWeightAmbientBlockCompositionFamily.compressedOverhead
    slots primaryOverhead

def componentData
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientComputedRRRRouteFieldTableLayoutData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) routeCost localQueryCost queryCost :=
  family.component bits

def toPackedRouteTableFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost) :
    FixedWeightAmbientComputedRRRPackedRouteTableFamily
      slots routeCost localQueryCost queryCost where
  wordSize := family.wordSize
  blocks := family.blocks
  component bits := (family.componentData bits).toPackedRouteTableData

def directory
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (bits : List Bool) :
    FixedWeightAmbientBlockCompositionData
      bits (family.blocks bits)
      (fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length)
      (family.wordSize bits.length) queryCost :=
  FixedWeightAmbientComputedRRRPackedRouteTableFamily.directory
    family.toPackedRouteTableFamily bits

theorem route_field_table_layout_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost) :
    SuccinctSpace.LittleOLinear (overhead slots) /\
      forall bits : List Bool,
        let data := family.componentData bits
        data.LayoutPackedProfile /\
          data.routeData.routePayload.length =
            fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          ((family.directory bits).payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall i,
            ((family.directory bits).accessCosted i).cost <=
              queryCost) /\
          (forall target pos,
            ((family.directory bits).rankCosted target pos).cost <=
              queryCost) /\
          (forall target occurrence,
            ((family.directory bits).selectCosted target occurrence).cost <=
              queryCost) := by
  constructor
  · exact fixedWeightAmbientBlockAuxiliaryOverhead_littleO slots
  · intro bits
    let data := family.componentData bits
    exact
      ⟨data.route_field_table_layout_packed_profile,
        data.routeData.routePayload_length_eq,
        (family.directory bits).payload_length,
        data.routeData.blocks_flatten,
        (fun i => (family.directory bits).accessCosted_cost_le i),
        (fun target pos =>
          (family.directory bits).rankCosted_cost_le target pos),
        (fun target occurrence =>
          (family.directory bits).selectCosted_cost_le
            target occurrence)⟩

theorem word_bounded_compressed_profile_of_primary_budget
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (primaryOverhead : Nat -> Nat)
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots primaryOverhead) /\
      forall bits : List Bool,
        (family.componentData bits).LayoutPackedProfile /\
          let data := family.directory bits
          data.DirectoryProfile /\
            data.payload.length =
              fixedWeightBlockPayloadBudget (family.blocks bits) +
                fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            data.payload.length <=
              fixedWeightPayloadBudget bits +
                compressedOverhead slots primaryOverhead bits.length /\
            data.auxPayload.length =
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
            SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
            (forall {word : List Bool},
              List.Mem word data.codeStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall {word : List Bool},
              List.Mem word data.auxStore.store.words.toList ->
                word.length <= Nat.log2 bits.length + 1) /\
            (forall i,
              (data.accessCosted i).cost <= queryCost /\
                (data.accessCosted i).erase = bits[i]?) /\
            (forall target pos,
              (data.rankCosted target pos).cost <= queryCost /\
                (data.rankCosted target pos).erase =
                  Succinct.rankPrefix target bits pos) /\
            (forall target occurrence,
              (data.selectCosted target occurrence).cost <= queryCost /\
                (data.selectCosted target occurrence).erase =
                  Succinct.select target bits occurrence) := by
  have hcompressed :=
    FixedWeightAmbientComputedRRRPackedRouteTableFamily.word_bounded_compressed_profile_of_primary_budget
      family.toPackedRouteTableFamily primaryOverhead hprimaryO
      (by
        intro bits
        exact hprimary bits)
  constructor
  · simpa [compressedOverhead,
      FixedWeightAmbientComputedRRRPackedRouteTableFamily.compressedOverhead]
      using hcompressed.1
  · intro bits
    constructor
    · exact (family.componentData bits).route_field_table_layout_packed_profile
    · simpa [directory, toPackedRouteTableFamily, componentData,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.directory,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.componentData,
        FixedWeightAmbientComputedRRRPackedRouteTableFamily.compressedOverhead,
        compressedOverhead]
        using (hcompressed.2 bits).2

/--
Promote an eight-table route-field layout family to the combined
route/class-length envelope family.

The extra side conditions are exactly the block-size discipline needed by the
class/length local RRR kernel, plus a counted `o(n)` budget for the concrete
per-block length/class tables.  The pointwise component is the canonical
`toRouteClassLengthTableEnvelopeData` constructor, so the resulting family uses
the charged combined auxiliary store rather than a proof-only decoded block.
-/
def toRouteClassLengthTableEnvelopeFamily
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (family.componentData bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize <
          2 ^ (family.componentData bits).fieldWidth)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (family.componentData bits).routeData.blockSize <=
          localQueryCost) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
      slots routeCost localQueryCost queryCost classLengthOverhead where
  wordSize := family.wordSize
  blocks := family.blocks
  classLengthOverhead_littleO := hclassLengthO
  component bits :=
    (family.componentData bits).toRouteClassLengthTableEnvelopeData
      (hblockSize_lt_fieldWidthPow bits) (hlocalCost bits)
  classLengthOverhead_le := by
    intro bits
    simpa [
      FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeData.classLengthOverhead,
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutData.toRouteClassLengthTableEnvelopeData,
      componentData]
      using hclassLength_le bits

theorem route_field_table_layout_family_to_route_class_length_table_envelope_family_profile
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead
            (family.componentData bits).fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hblockSize_lt_fieldWidthPow :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize <
          2 ^ (family.componentData bits).fieldWidth)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (family.componentData bits).routeData.blockSize <=
          localQueryCost) :
    SuccinctSpace.LittleOLinear
        (FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
          slots classLengthOverhead) /\
      forall bits : List Bool,
        let data :=
          (family.toRouteClassLengthTableEnvelopeFamily
            classLengthOverhead hclassLengthO hclassLength_le
            hblockSize_lt_fieldWidthPow hlocalCost).componentData bits
        let directory :=
          (family.toRouteClassLengthTableEnvelopeFamily
            classLengthOverhead hclassLengthO hclassLength_le
            hblockSize_lt_fieldWidthPow hlocalCost).directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
                slots classLengthOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.route_class_length_table_envelope_family_profile
      (family.toRouteClassLengthTableEnvelopeFamily
        classLengthOverhead hclassLengthO hclassLength_le
        hblockSize_lt_fieldWidthPow hlocalCost)

/--
Fixed block-size/field-width specialization of the route-layout-to-envelope
family constructor.

This is the common constant-query use case: every component uses the same
ambient block-size cap and field width, the local query budget is the
class/length block-size cost for that cap, and a single `blockSize < 2^fieldWidth`
fact supplies the metadata encoding discipline.
-/
def toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
    {slots blockSize fieldWidth routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost
        (fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize)
        queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hfield :
      forall bits : List Bool,
        (family.componentData bits).fieldWidth = fieldWidth)
    (hblockSize :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize = blockSize)
    (hfit : blockSize < 2 ^ fieldWidth) :
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily
      slots routeCost
      (fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize)
      queryCost classLengthOverhead :=
  family.toRouteClassLengthTableEnvelopeFamily
    classLengthOverhead hclassLengthO
    (by
      intro bits
      simpa [hfield bits] using hclassLength_le bits)
    (by
      intro bits
      simpa [hfield bits, hblockSize bits] using hfit)
    (by
      intro bits
      simp [hblockSize bits])

theorem fixed_block_size_route_class_length_table_envelope_family_profile
    {slots blockSize fieldWidth routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost
        (fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize)
        queryCost)
    (classLengthOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear classLengthOverhead)
    (hclassLength_le :
      forall bits : List Bool,
        fixedWeightBlockClassLengthTableOverhead fieldWidth
            (family.blocks bits) <=
          classLengthOverhead bits.length)
    (hfield :
      forall bits : List Bool,
        (family.componentData bits).fieldWidth = fieldWidth)
    (hblockSize :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize = blockSize)
    (hfit : blockSize < 2 ^ fieldWidth) :
    SuccinctSpace.LittleOLinear
        (FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
          slots classLengthOverhead) /\
      forall bits : List Bool,
        let data :=
          (family.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
            classLengthOverhead hclassLengthO hclassLength_le
            hfield hblockSize hfit).componentData bits
        let directory :=
          (family.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
            classLengthOverhead hclassLengthO hclassLength_le
            hfield hblockSize hfit).directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
                slots classLengthOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
              slots classLengthOverhead bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.route_class_length_table_envelope_family_profile
      (family.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
        classLengthOverhead hclassLengthO hclassLength_le
        hfield hblockSize hfit)

/--
Global block-count/field-width bridge for the fixed block-size route layout.

This is the family-level budget handoff: a concrete route-field layout only has
to prove a useful block-count cap and field-width cap.  Those two facts feed the
class/length table overhead lemma, producing the promoted route/class-length
envelope and the word-bounded compressed/FID profile under the usual primary
fixed-weight payload budget.
-/
theorem fixed_block_size_word_bounded_compressed_profile_of_block_bounds
    {slots blockSize fieldWidth routeCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost
        (fixedWeightComputedRRRClassLengthBlockSizeQueryCost blockSize)
        queryCost)
    (blockCountBound fieldWidthBound primaryOverhead : Nat -> Nat)
    (hclassLengthO :
      SuccinctSpace.LittleOLinear
        (fixedWeightBlockClassLengthTableOverheadBudget
          blockCountBound fieldWidthBound))
    (hprimaryO : SuccinctSpace.LittleOLinear primaryOverhead)
    (hblocks :
      forall bits : List Bool,
        (family.blocks bits).length <= blockCountBound bits.length)
    (hfieldBound :
      forall bits : List Bool,
        fieldWidth <= fieldWidthBound bits.length)
    (hfield :
      forall bits : List Bool,
        (family.componentData bits).fieldWidth = fieldWidth)
    (hblockSize :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize = blockSize)
    (hfit : blockSize < 2 ^ fieldWidth)
    (hprimary :
      forall bits : List Bool,
        fixedWeightBlockPayloadBudget (family.blocks bits) <=
          fixedWeightPayloadBudget bits + primaryOverhead bits.length) :
    SuccinctSpace.LittleOLinear
        (FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
          slots
          (fixedWeightBlockClassLengthTableOverheadBudget
            blockCountBound fieldWidthBound)
          primaryOverhead) /\
      forall bits : List Bool,
        let envelopeFamily :=
          family.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
            (fixedWeightBlockClassLengthTableOverheadBudget
              blockCountBound fieldWidthBound)
            hclassLengthO
            (by
              intro bits
              exact fixedWeightBlockClassLengthTableOverhead_le_budget
                (hblocks bits) (hfieldBound bits))
            hfield hblockSize hfit
        let data := envelopeFamily.componentData bits
        let directory := envelopeFamily.directory bits
        data.RouteClassLengthEnvelopeProfile /\
          directory.DirectoryProfile /\
          directory.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              data.totalMetadataOverhead /\
          directory.payload.length <=
            fixedWeightPayloadBudget bits +
              FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.compressedOverhead
                slots
                (fixedWeightBlockClassLengthTableOverheadBudget
                  blockCountBound fieldWidthBound)
                primaryOverhead bits.length /\
          directory.auxPayload.length = data.totalMetadataOverhead /\
          directory.auxPayload.length <=
            FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.overhead
              slots
              (fixedWeightBlockClassLengthTableOverheadBudget
                blockCountBound fieldWidthBound)
              bits.length /\
          SuccinctSpace.flattenPayloadWords (family.blocks bits) = bits /\
          (forall {word : List Bool},
            List.Mem word directory.codeStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall {word : List Bool},
            List.Mem word directory.auxStore.store.words.toList ->
              word.length <= Nat.log2 bits.length + 1) /\
          (forall i,
            (directory.accessCosted i).cost <= queryCost /\
              (directory.accessCosted i).erase = bits[i]?) /\
          (forall target pos,
            (directory.rankCosted target pos).cost <= queryCost /\
              (directory.rankCosted target pos).erase =
                Succinct.rankPrefix target bits pos) /\
          (forall target occurrence,
            (directory.selectCosted target occurrence).cost <=
                queryCost /\
              (directory.selectCosted target occurrence).erase =
                Succinct.select target bits occurrence) := by
  exact
    FixedWeightAmbientComputedRRRRouteClassLengthTableEnvelopeFamily.word_bounded_compressed_profile_of_primary_budget
      (family.toFixedBlockSizeRouteClassLengthTableEnvelopeFamily
        (fixedWeightBlockClassLengthTableOverheadBudget
          blockCountBound fieldWidthBound)
        hclassLengthO
        (by
          intro bits
          exact fixedWeightBlockClassLengthTableOverhead_le_budget
            (hblocks bits) (hfieldBound bits))
        hfield hblockSize hfit)
      primaryOverhead hprimaryO hprimary

end FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily

theorem no_fixedWeightLogChunkRouteFieldTableLayoutFamilyToEnvelopeUniformCost
    {slots routeCost localQueryCost queryCost : Nat}
    (family :
      FixedWeightAmbientComputedRRRRouteFieldTableLayoutFamily
        slots routeCost localQueryCost queryCost)
    (hblockSize :
      forall bits : List Bool,
        (family.componentData bits).routeData.blockSize =
          fixedWeightLogChunkBlockSize bits.length)
    (hlocalCost :
      forall bits : List Bool,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (family.componentData bits).routeData.blockSize <=
          localQueryCost) :
    False := by
  let bits := List.replicate (2 ^ localQueryCost) false
  have hle :
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
          (fixedWeightLogChunkBlockSize (2 ^ localQueryCost)) <=
        localQueryCost := by
    have hcost := hlocalCost bits
    have hblock := hblockSize bits
    simpa [bits, hblock] using hcost
  have hgt :=
    fixedWeightComputedRRRClassLengthLogChunkBlockSizeQueryCost_gt
      localQueryCost
  omega



end RankSelectSpec

end RMQ
