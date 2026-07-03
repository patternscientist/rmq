import RMQ.Core.RankSelectCompressed.Base.DecodedRoutes

namespace RMQ

namespace RankSelectSpec

theorem list_getElem?_append_middle_of_get?
    {α : Type} (pre mid post : List α) {i : Nat} {x : α}
    (hget : mid[i]? = some x) :
    (pre ++ mid ++ post)[pre.length + i]? = some x := by
  have hi : i < mid.length := (List.getElem?_eq_some_iff.mp hget).1
  have hpreMid : pre.length + i < (pre ++ mid).length := by
    simp [List.length_append]
    omega
  rw [List.getElem?_append_left hpreMid]
  rw [List.getElem?_append_right (by omega)]
  have hsub : pre.length + i - pre.length = i := by omega
  rw [hsub]
  exact hget

theorem boundedPayloadWordStore_get?_of_words_append_middle
    {payload : List Bool} {wordSize : Nat}
    (store : SuccinctSpace.BoundedPayloadWordStore payload wordSize)
    {pre mid post : List (List Bool)} {localSlot : Nat}
    {word : List Bool}
    (hwords : store.store.words.toList = pre ++ mid ++ post)
    (hlocal : mid[localSlot]? = some word) :
    store.store.words[pre.length + localSlot]? = some word := by
  have hlist :
      store.store.words.toList[pre.length + localSlot]? =
        some word := by
    rw [hwords]
    exact list_getElem?_append_middle_of_get? pre mid post hlocal
  simpa [Array.getElem?_toList] using hlist

def fixedWeightRouteFieldTableWords
    (fieldWidth : Nat) (entries : List Nat) : List (List Bool) :=
  entries.map (SuccinctSpace.natToBitsLE fieldWidth)

theorem fixedWeightRouteFieldTableWords_get?
    {fieldWidth : Nat} {entries : List Nat} {slot value : Nat}
    (hget : entries[slot]? = some value) :
    (fixedWeightRouteFieldTableWords fieldWidth entries)[slot]? =
      some (SuccinctSpace.natToBitsLE fieldWidth value) := by
  simp [fixedWeightRouteFieldTableWords, List.getElem?_map, hget]

theorem fixedWeightRouteFieldTableWords_eq_ofEntries
    (fieldWidth : Nat) (entries : List Nat)
    (hbound :
      forall {entry : Nat}, List.Mem entry entries ->
        entry < 2 ^ fieldWidth) :
    fixedWeightRouteFieldTableWords fieldWidth entries =
      (SuccinctSpace.FixedWidthNatTable.ofEntries
        entries fieldWidth hbound).store.words.toList := by
  rw [fixedWidthNatTableOfEntries_words_toList]
  rfl

theorem fixedWeightRouteFieldTablePayload_length
    (fieldWidth : Nat) (entries : List Nat) :
    (SuccinctSpace.flattenPayloadWords
        (fixedWeightRouteFieldTableWords fieldWidth entries)).length =
      entries.length * fieldWidth := by
  have hlength :
      (SuccinctSpace.flattenPayloadWords
          (fixedWeightRouteFieldTableWords fieldWidth entries)).length =
        (fixedWeightRouteFieldTableWords fieldWidth entries).length *
          fieldWidth := by
    apply SuccinctSpace.flattenPayloadWords_length_of_forall_length
    intro word hmem
    have hmap :
        List.Mem word
          (entries.map (SuccinctSpace.natToBitsLE fieldWidth)) := by
      simpa [fixedWeightRouteFieldTableWords] using hmem
    rcases List.mem_map.mp hmap with ⟨entry, _hentry, hword⟩
    rw [<- hword]
    exact SuccinctSpace.natToBitsLE_length fieldWidth entry
  simpa [fixedWeightRouteFieldTableWords] using hlength

def fixedWeightBlockClassLengthTableWords
    (fieldWidth : Nat) (blocks : List (List Bool)) :
    List (List Bool) :=
  fixedWeightRouteFieldTableWords fieldWidth
      (fixedWeightBlockLengthEntries blocks) ++
    fixedWeightRouteFieldTableWords fieldWidth
      (fixedWeightBlockClassEntries blocks)

def fixedWeightBlockClassLengthTablePayload
    (fieldWidth : Nat) (blocks : List (List Bool)) : List Bool :=
  SuccinctSpace.flattenPayloadWords
    (fixedWeightBlockClassLengthTableWords fieldWidth blocks)

def fixedWeightBlockClassLengthTableOverhead
    (fieldWidth : Nat) (blocks : List (List Bool)) : Nat :=
  (blocks.length + blocks.length) * fieldWidth

def fixedWeightBlockClassLengthTableOverheadBudget
    (blockCountBound fieldWidthBound : Nat -> Nat) : Nat -> Nat :=
  fun n => (blockCountBound n + blockCountBound n) * fieldWidthBound n

def fixedWeightChunkBlocks (blockSize : Nat) (bits : List Bool) :
    List (List Bool) :=
  SuccinctSpace.chunkPayloadWords blockSize bits

def fixedWeightChunkBlockCountBound (blockSize : Nat) : Nat -> Nat :=
  fun n => n / blockSize + 1

def fixedWeightChunkBlocksWithSentinel
    (blockSize : Nat) (bits : List Bool) : List (List Bool) :=
  fixedWeightChunkBlocks blockSize bits ++ [[]]

def fixedWeightChunkBlockCountBoundWithSentinel
    (blockSize : Nat) : Nat -> Nat :=
  fun n => n / blockSize + 2

def fixedWeightLogChunkBlockSize (n : Nat) : Nat :=
  Nat.log2 n + 1

def fixedWeightLogChunkBlocks (bits : List Bool) : List (List Bool) :=
  fixedWeightChunkBlocks (fixedWeightLogChunkBlockSize bits.length) bits

def fixedWeightLogChunkBlockCountBound : Nat -> Nat :=
  fun n => n / fixedWeightLogChunkBlockSize n + 1

def fixedWeightLogChunkBlocksWithSentinel
    (bits : List Bool) : List (List Bool) :=
  fixedWeightChunkBlocksWithSentinel
    (fixedWeightLogChunkBlockSize bits.length) bits

def fixedWeightLogChunkBlockCountBoundWithSentinel : Nat -> Nat :=
  fun n => n / fixedWeightLogChunkBlockSize n + 2

def fixedWeightLogChunkClassLengthFieldWidthBound (n : Nat) : Nat :=
  Nat.log2 (fixedWeightLogChunkBlockSize n) + 1

def fixedWeightLogChunkClassLengthOverhead : Nat -> Nat :=
  fun n =>
    fixedWeightBlockClassLengthTableOverheadBudget
      fixedWeightLogChunkBlockCountBoundWithSentinel
      fixedWeightLogChunkClassLengthFieldWidthBound n +
        4 * fixedWeightLogChunkClassLengthFieldWidthBound n

theorem fixedWeightLogChunkBlockSize_pos (n : Nat) :
    0 < fixedWeightLogChunkBlockSize n := by
  simp [fixedWeightLogChunkBlockSize]

theorem fixedWeightLogChunkClassLengthFieldWidthBound_pos (n : Nat) :
    0 < fixedWeightLogChunkClassLengthFieldWidthBound n := by
  simp [fixedWeightLogChunkClassLengthFieldWidthBound]

theorem fixedWeightLogChunkBlockSize_lt_classLengthFieldWidthPow
    (n : Nat) :
    fixedWeightLogChunkBlockSize n <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound n := by
  simpa [fixedWeightLogChunkClassLengthFieldWidthBound] using
    (Nat.lt_log2_self (n := fixedWeightLogChunkBlockSize n))

theorem fixedWeightLogChunkBlockCountBound_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkBlockCountBound := by
  unfold fixedWeightLogChunkBlockCountBound fixedWeightLogChunkBlockSize
  simpa using
    SuccinctSpace.littleOLinear_id_div_log2_succ.add_const 1

theorem fixedWeightLogChunkBlockCountBoundWithSentinel_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkBlockCountBoundWithSentinel := by
  unfold fixedWeightLogChunkBlockCountBoundWithSentinel
    fixedWeightLogChunkBlockSize
  simpa using
    SuccinctSpace.littleOLinear_id_div_log2_succ.add_const 2

theorem fixedWeightLogChunkClassLengthFieldWidthBound_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkClassLengthFieldWidthBound := by
  intro scale hscale
  rcases
      SuccinctSpace.eventually_scale_logLog_succ_le_log_succ scale with
    ⟨threshold, hthreshold⟩
  exact ⟨threshold + 1, by
    intro n hn
    have hn_pos : n ≠ 0 := by omega
    have hlog :
        scale * (Nat.log2 (Nat.log2 n + 1) + 1) <=
          Nat.log2 n + 1 :=
      hthreshold n (by omega)
    have hlog_le_self : Nat.log2 n + 1 <= n := by
      have hpow : Nat.log2 n + 1 <= 2 ^ Nat.log2 n := by
        exact SuccinctSpace.nat_succ_le_two_pow (Nat.log2 n)
      exact Nat.le_trans hpow (Nat.log2_self_le hn_pos)
    exact Nat.le_trans (by
      simpa [fixedWeightLogChunkClassLengthFieldWidthBound,
        fixedWeightLogChunkBlockSize] using hlog) hlog_le_self⟩

theorem fixedWeightLogChunkClassLengthOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightLogChunkClassLengthOverhead := by
  have hsample :
      SuccinctSpace.LittleOLinear
        (SuccinctSpace.logLogSampledDirectoryOverhead 2) :=
    SuccinctSpace.logLogSampledDirectoryOverhead_littleO 2
  have htail :
      SuccinctSpace.LittleOLinear
        (fun n =>
          8 * fixedWeightLogChunkClassLengthFieldWidthBound n) :=
    fixedWeightLogChunkClassLengthFieldWidthBound_littleO.mul_left 8
  apply SuccinctSpace.LittleOLinear.of_le (hsample.add htail)
  intro n
  unfold fixedWeightLogChunkClassLengthOverhead
    fixedWeightBlockClassLengthTableOverheadBudget
    fixedWeightLogChunkBlockCountBoundWithSentinel
    fixedWeightLogChunkClassLengthFieldWidthBound
    fixedWeightLogChunkBlockSize
    SuccinctSpace.logLogSampledDirectoryOverhead
  let q := n / (Nat.log2 n + 1)
  let w := Nat.log2 (Nat.log2 n + 1) + 1
  change ((q + 2 + (q + 2)) * w + 4 * w) <=
    2 * (q * w) + 8 * w
  have hsum : q + 2 + (q + 2) = 2 * q + 4 := by omega
  rw [hsum]
  rw [Nat.add_mul]
  rw [Nat.mul_assoc]
  omega

theorem fixedWeightChunkBlocks_flatten
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightChunkBlocks blockSize bits) = bits := by
  simpa [fixedWeightChunkBlocks] using
    SuccinctSpace.flattenPayloadWords_chunkPayloadWords hblockSize bits

theorem fixedWeightChunkBlocks_length_le
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    (fixedWeightChunkBlocks blockSize bits).length <=
      fixedWeightChunkBlockCountBound blockSize bits.length := by
  simpa [fixedWeightChunkBlocks, fixedWeightChunkBlockCountBound] using
    SuccinctSpace.chunkPayloadWords_length_le_div_add_one
      hblockSize bits

theorem fixedWeightChunkBlocks_block_length_le
    {blockSize : Nat} {bits block : List Bool}
    (hmem : List.Mem block (fixedWeightChunkBlocks blockSize bits)) :
    block.length <= blockSize := by
  simpa [fixedWeightChunkBlocks] using
    SuccinctSpace.chunkPayloadWords_word_length_le
      blockSize (payload := bits) hmem

theorem fixedWeightChunkBlocksWithSentinel_flatten
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightChunkBlocksWithSentinel blockSize bits) = bits := by
  have hsentinel :
      SuccinctSpace.flattenPayloadWords ([[]] : List (List Bool)) = [] := by
    simp [SuccinctSpace.flattenPayloadWords]
  simp [fixedWeightChunkBlocksWithSentinel,
    SuccinctSpace.flattenPayloadWords_append, hsentinel,
    fixedWeightChunkBlocks_flatten hblockSize bits]

theorem fixedWeightChunkBlocksWithSentinel_length_le
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits).length <=
      fixedWeightChunkBlockCountBoundWithSentinel
        blockSize bits.length := by
  have hlen := fixedWeightChunkBlocks_length_le hblockSize bits
  simp [fixedWeightChunkBlocksWithSentinel,
    fixedWeightChunkBlockCountBoundWithSentinel,
    fixedWeightChunkBlockCountBound] at *
  omega

theorem fixedWeightChunkBlocksWithSentinel_block_length_le
    {blockSize : Nat} {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightChunkBlocksWithSentinel blockSize bits)) :
    block.length <= blockSize := by
  rw [fixedWeightChunkBlocksWithSentinel] at hmem
  rcases List.mem_append.mp hmem with hchunk | hsentinel
  · exact fixedWeightChunkBlocks_block_length_le hchunk
  · cases hsentinel with
    | head =>
        simp
    | tail _ htail =>
        cases htail

theorem fixedWeightLogChunkBlocks_flatten
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightLogChunkBlocks bits) = bits := by
  exact
    fixedWeightChunkBlocks_flatten
      (fixedWeightLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightLogChunkBlocks_length_le
    (bits : List Bool) :
    (fixedWeightLogChunkBlocks bits).length <=
      fixedWeightLogChunkBlockCountBound bits.length := by
  exact
    fixedWeightChunkBlocks_length_le
      (fixedWeightLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightLogChunkBlocks_block_length_le
    {bits block : List Bool}
    (hmem : List.Mem block (fixedWeightLogChunkBlocks bits)) :
    block.length <= fixedWeightLogChunkBlockSize bits.length := by
  exact fixedWeightChunkBlocks_block_length_le hmem

theorem fixedWeightLogChunkBlocksWithSentinel_flatten
    (bits : List Bool) :
    SuccinctSpace.flattenPayloadWords
        (fixedWeightLogChunkBlocksWithSentinel bits) = bits := by
  exact
    fixedWeightChunkBlocksWithSentinel_flatten
      (fixedWeightLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightLogChunkBlocksWithSentinel_length_le
    (bits : List Bool) :
    (fixedWeightLogChunkBlocksWithSentinel bits).length <=
      fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  exact
    fixedWeightChunkBlocksWithSentinel_length_le
      (fixedWeightLogChunkBlockSize_pos bits.length) bits

theorem fixedWeightLogChunkBlocksWithSentinel_block_length_le
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    block.length <= fixedWeightLogChunkBlockSize bits.length := by
  exact fixedWeightChunkBlocksWithSentinel_block_length_le hmem

theorem fixedWeightLogChunkBlocksWithSentinel_block_length_lt_classLengthFieldWidthPow
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    block.length <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound bits.length := by
  exact Nat.lt_of_le_of_lt
    (fixedWeightLogChunkBlocksWithSentinel_block_length_le hmem)
    (fixedWeightLogChunkBlockSize_lt_classLengthFieldWidthPow bits.length)

theorem fixedWeightLogChunkBlocksWithSentinel_block_class_lt_classLengthFieldWidthPow
    {bits block : List Bool}
    (hmem :
      List.Mem block (fixedWeightLogChunkBlocksWithSentinel bits)) :
    trueCount block <
      2 ^ fixedWeightLogChunkClassLengthFieldWidthBound bits.length := by
  exact trueCount_lt_of_length_lt
    (fixedWeightLogChunkBlocksWithSentinel_block_length_lt_classLengthFieldWidthPow
      hmem)

theorem fixedWeightLogChunkBlockPayloadBudget_le_length_add_blockCount
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      bits.length +
        (fixedWeightLogChunkBlocksWithSentinel bits).length := by
  have hprimary :=
    fixedWeightBlockPayloadBudget_le_flatten_length_add_blocks
      (fixedWeightLogChunkBlocksWithSentinel bits)
  simpa [fixedWeightLogChunkBlocksWithSentinel_flatten bits] using hprimary

theorem fixedWeightLogChunkBlockPayloadBudget_le_length_add_bound
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      bits.length +
        fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  have hprimary :=
    fixedWeightLogChunkBlockPayloadBudget_le_length_add_blockCount bits
  have hblocks := fixedWeightLogChunkBlocksWithSentinel_length_le bits
  omega

theorem fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_blockCount
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        (fixedWeightLogChunkBlocksWithSentinel bits).length := by
  have hprimary :=
    fixedWeightBlockPayloadBudget_le_payloadBudget_flatten_add_blocks
      (fixedWeightLogChunkBlocksWithSentinel bits)
  simpa [fixedWeightLogChunkBlocksWithSentinel_flatten bits] using hprimary

theorem fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound
    (bits : List Bool) :
    fixedWeightBlockPayloadBudget
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightPayloadBudget bits +
        fixedWeightLogChunkBlockCountBoundWithSentinel bits.length := by
  have hprimary :=
    fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_blockCount bits
  have hblocks := fixedWeightLogChunkBlocksWithSentinel_length_le bits
  omega

theorem fixedWeightComputedRRRClassLengthLogChunkBlockSizeQueryCost_gt
    (localQueryCost : Nat) :
    localQueryCost <
      fixedWeightComputedRRRClassLengthBlockSizeQueryCost
        (fixedWeightLogChunkBlockSize (2 ^ localQueryCost)) := by
  unfold fixedWeightComputedRRRClassLengthBlockSizeQueryCost
    fixedWeightLogChunkBlockSize
  have hpow_nonzero : 2 ^ localQueryCost ≠ 0 := by
    exact Nat.ne_of_gt (Nat.pow_pos (by omega : 0 < 2))
  have hlog : localQueryCost <= Nat.log2 (2 ^ localQueryCost) := by
    exact (Nat.le_log2 hpow_nonzero).2 (Nat.le_refl _)
  have hsucc : localQueryCost + 1 <= 2 ^ localQueryCost :=
    SuccinctSpace.nat_succ_le_two_pow localQueryCost
  have hpow :
      2 ^ localQueryCost <=
        2 ^ (Nat.log2 (2 ^ localQueryCost) + 1) := by
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  omega

theorem no_fixedWeightComputedRRRClassLengthLogChunkBlockSizeUniformCost
    (localQueryCost : Nat) :
    ¬ (forall n : Nat,
        fixedWeightComputedRRRClassLengthBlockSizeQueryCost
            (fixedWeightLogChunkBlockSize n) <=
          localQueryCost) := by
  intro hcost
  have hle := hcost (2 ^ localQueryCost)
  have hgt :=
    fixedWeightComputedRRRClassLengthLogChunkBlockSizeQueryCost_gt
      localQueryCost
  omega

theorem rankPrefix_true_replicate_false (n limit : Nat) :
    Succinct.rankPrefix true (List.replicate n false) limit = 0 := by
  induction n generalizing limit with
  | zero =>
      simpa using Succinct.rankPrefix_nil true limit
  | succ n ih =>
      cases limit with
      | zero =>
          simp [Succinct.rankPrefix]
      | succ limit =>
          simp [List.replicate, Succinct.rankPrefix, ih]

theorem trueCount_replicate_false (n : Nat) :
    trueCount (List.replicate n false) = 0 := by
  simp [trueCount, rankPrefix_true_replicate_false]

theorem fixedWeightComputedRRRClassLengthQueryCost_replicate_false
    (n : Nat) :
    fixedWeightComputedRRRClassLengthQueryCost
        (List.replicate n false) =
      n + 5 := by
  simp [fixedWeightComputedRRRClassLengthQueryCost,
    fixedWeightComputedRRRDecodeTicks, trueCount_replicate_false,
    binomialCount_zero_right]
  omega

namespace FixedWeightAmbientBlockCompositionFamily

theorem word_bounded_compressed_profile_of_log_chunk_blocks
    {slots queryCost : Nat}
    (family : FixedWeightAmbientBlockCompositionFamily slots queryCost)
    (hblocks :
      forall bits : List Bool,
        family.blocks bits = fixedWeightLogChunkBlocksWithSentinel bits) :
    SuccinctSpace.LittleOLinear
        (compressedOverhead slots fixedWeightLogChunkBlockCountBoundWithSentinel) /\
      forall bits : List Bool,
        let data := family.directory bits
        data.DirectoryProfile /\
          data.payload.length =
            fixedWeightBlockPayloadBudget (family.blocks bits) +
              fixedWeightAmbientBlockAuxiliaryOverhead slots bits.length /\
          data.payload.length <=
            fixedWeightPayloadBudget bits +
              compressedOverhead slots
                fixedWeightLogChunkBlockCountBoundWithSentinel bits.length /\
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
  exact
    word_bounded_compressed_profile_of_primary_budget
      family fixedWeightLogChunkBlockCountBoundWithSentinel
      fixedWeightLogChunkBlockCountBoundWithSentinel_littleO
      (by
        intro bits
        simpa [hblocks bits] using
          fixedWeightLogChunkBlockPayloadBudget_le_payloadBudget_add_bound bits)

end FixedWeightAmbientBlockCompositionFamily

theorem fixedWeightLogChunkBlockClassLengthTableOverhead_le
    (bits : List Bool) :
    fixedWeightBlockClassLengthTableOverhead
        (fixedWeightLogChunkClassLengthFieldWidthBound bits.length)
        (fixedWeightLogChunkBlocksWithSentinel bits) <=
      fixedWeightLogChunkClassLengthOverhead bits.length := by
  let width := fixedWeightLogChunkClassLengthFieldWidthBound bits.length
  let bound := fixedWeightLogChunkBlockCountBoundWithSentinel bits.length
  have hblocks :
      (fixedWeightLogChunkBlocksWithSentinel bits).length <= bound := by
    simpa [bound] using
      fixedWeightLogChunkBlocksWithSentinel_length_le bits
  have htwice :
      (fixedWeightLogChunkBlocksWithSentinel bits).length +
          (fixedWeightLogChunkBlocksWithSentinel bits).length <=
        bound + bound := by omega
  have hmul :
      ((fixedWeightLogChunkBlocksWithSentinel bits).length +
          (fixedWeightLogChunkBlocksWithSentinel bits).length) * width <=
        (bound + bound) * width :=
    Nat.mul_le_mul_right width htwice
  have hbudget :
      fixedWeightBlockClassLengthTableOverhead
          (fixedWeightLogChunkClassLengthFieldWidthBound bits.length)
          (fixedWeightLogChunkBlocksWithSentinel bits) <=
        fixedWeightBlockClassLengthTableOverheadBudget
          fixedWeightLogChunkBlockCountBoundWithSentinel
          fixedWeightLogChunkClassLengthFieldWidthBound bits.length := by
    simpa [fixedWeightBlockClassLengthTableOverhead,
      fixedWeightBlockClassLengthTableOverheadBudget, width, bound]
      using hmul
  unfold fixedWeightLogChunkClassLengthOverhead
  omega

theorem fixedWeightLogChunkBlocksWithSentinel_length_mul_blockSize_ge
    (bits : List Bool) :
    bits.length <=
      (fixedWeightLogChunkBlocksWithSentinel bits).length *
        fixedWeightLogChunkBlockSize bits.length := by
  have hflatten := fixedWeightLogChunkBlocksWithSentinel_flatten bits
  have hle :
      (SuccinctSpace.flattenPayloadWords
          (fixedWeightLogChunkBlocksWithSentinel bits)).length <=
        (fixedWeightLogChunkBlocksWithSentinel bits).length *
          fixedWeightLogChunkBlockSize bits.length :=
    SuccinctSpace.flattenPayloadWords_length_le_of_forall_length_le
      (by
        intro word hmem
        exact fixedWeightLogChunkBlocksWithSentinel_block_length_le hmem)
  simpa [hflatten] using hle

theorem fixedWeightLogChunkRouteWidthClassLengthTableOverhead_ge_length
    (bits : List Bool) :
    bits.length <=
      fixedWeightBlockClassLengthTableOverhead
        (fixedWeightLogChunkBlockSize bits.length)
        (fixedWeightLogChunkBlocksWithSentinel bits) := by
  have hcover :=
    fixedWeightLogChunkBlocksWithSentinel_length_mul_blockSize_ge bits
  unfold fixedWeightBlockClassLengthTableOverhead
  exact Nat.le_trans hcover
    (Nat.mul_le_mul_right
      (fixedWeightLogChunkBlockSize bits.length) (by omega))

theorem fixedWeight_notLittleOLinear_of_self_le
    {overhead : Nat -> Nat}
    (hle : forall n, n <= overhead n) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  intro hoverhead
  rcases hoverhead 2 (by omega) with ⟨threshold, hthreshold⟩
  let n := threshold + 1
  have hn : threshold <= n := by omega
  have hscaled : 2 * overhead n <= n := hthreshold n hn
  have hself : n <= overhead n := hle n
  have htwice : 2 * n <= 2 * overhead n :=
    Nat.mul_le_mul_left 2 hself
  omega

def fixedWeightLogChunkRouteWidthClassLengthOverhead : Nat -> Nat :=
  fun n =>
    fixedWeightBlockClassLengthTableOverhead
      (fixedWeightLogChunkBlockSize n)
      (fixedWeightLogChunkBlocksWithSentinel
        (List.replicate n false))

theorem fixedWeightLogChunkRouteWidthClassLengthOverhead_not_littleO :
    ¬ SuccinctSpace.LittleOLinear
      fixedWeightLogChunkRouteWidthClassLengthOverhead := by
  apply fixedWeight_notLittleOLinear_of_self_le
  intro n
  simpa [fixedWeightLogChunkRouteWidthClassLengthOverhead] using
    fixedWeightLogChunkRouteWidthClassLengthTableOverhead_ge_length
      (List.replicate n false)

/--
Dense decoded-table lower bound for log-sized fixed-weight chunks.

This is the size scale of a counted table that has one `blockSize`-bit decoded
word for every possible local code at the log-chunk block size.  It is a
deliberately coarse lower bound for dense all-class decoders; it is already
linear, so such a table cannot serve as the `o(n)` decoder payload in the
compressed/FID capstone.
-/
def fixedWeightLogChunkDenseDecoderLowerBound : Nat -> Nat :=
  fun n =>
    2 ^ fixedWeightLogChunkBlockSize n *
      fixedWeightLogChunkBlockSize n

theorem fixedWeightLogChunkDenseDecoderLowerBound_ge_length
    (n : Nat) :
    n <= fixedWeightLogChunkDenseDecoderLowerBound n := by
  have hpow :
      n <= 2 ^ fixedWeightLogChunkBlockSize n := by
    exact Nat.le_of_lt (by
      simpa [fixedWeightLogChunkBlockSize] using
        (Nat.lt_log2_self (n := n)))
  have hblock : 1 <= fixedWeightLogChunkBlockSize n := by
    exact fixedWeightLogChunkBlockSize_pos n
  have hmul :
      2 ^ fixedWeightLogChunkBlockSize n <=
        2 ^ fixedWeightLogChunkBlockSize n *
          fixedWeightLogChunkBlockSize n := by
    have h :=
      Nat.mul_le_mul_left (2 ^ fixedWeightLogChunkBlockSize n)
        hblock
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
  exact Nat.le_trans hpow hmul

theorem no_fixedWeightLogChunk_dense_decoder_littleO
    {decoderOverhead : Nat -> Nat}
    (hdense :
      forall n,
        fixedWeightLogChunkDenseDecoderLowerBound n <=
          decoderOverhead n) :
    ¬ SuccinctSpace.LittleOLinear decoderOverhead := by
  apply fixedWeight_notLittleOLinear_of_self_le
  intro n
  exact Nat.le_trans
    (fixedWeightLogChunkDenseDecoderLowerBound_ge_length n)
    (hdense n)

theorem fixedWeightChunkBlocksWithSentinel_get_sentinel
    (blockSize : Nat) (bits : List Bool) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits)[
        (fixedWeightChunkBlocks blockSize bits).length]? = some [] := by
  simp [fixedWeightChunkBlocksWithSentinel]

theorem fixedWeightChunkBlocksWithSentinel_get_chunk
    {blockSize : Nat} {bits block : List Bool} {blockIndex : Nat}
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[blockIndex]? =
        some block) :
    (fixedWeightChunkBlocksWithSentinel blockSize bits)[blockIndex]? =
      some block := by
  have hidx :
      blockIndex < (fixedWeightChunkBlocks blockSize bits).length :=
    (List.getElem?_eq_some_iff.mp hget).1
  simpa [fixedWeightChunkBlocksWithSentinel, List.getElem?_append,
    hidx] using hget

theorem fixedWeightChunkBlocks_get?_access_exact
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {i : Nat}
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[i / blockSize]? =
        some block) :
    block[i - (i / blockSize) * blockSize]? = bits[i]? := by
  let start := (i / blockSize) * blockSize
  let offset := i - start
  have hwordEq :
      block = (bits.drop start).take blockSize := by
    have hchunk :
        (SuccinctSpace.chunkPayloadWords blockSize bits)[
            i / blockSize]? = some block := by
      simpa [fixedWeightChunkBlocks] using hget
    simpa [start] using
      SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
  have hstart_le : start <= i := by
    simpa [start] using Nat.div_mul_le_self i blockSize
  have hoffset_lt : offset < blockSize := by
    have hlt := Nat.lt_div_mul_add hblockSize (a := i)
    simp [offset, start]
    omega
  have hpos : start + offset = i := by
    simp [offset]
    omega
  rw [hwordEq]
  rw [List.getElem?_take]
  simp [offset, start, hoffset_lt, hpos]

theorem fixedWeightChunkBlocks_get?_rankPrefix_add_exact
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {target : Bool} {pos : Nat}
    (hpos : pos <= bits.length)
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[pos / blockSize]? =
        some block) :
    Succinct.rankPrefix target bits ((pos / blockSize) * blockSize) +
        Succinct.rankPrefix target block
          (pos - (pos / blockSize) * blockSize) =
      Succinct.rankPrefix target bits pos := by
  let start := (pos / blockSize) * blockSize
  let offset := pos - start
  have hwordEq :
      block = (bits.drop start).take blockSize := by
    have hchunk :
        (SuccinctSpace.chunkPayloadWords blockSize bits)[
            pos / blockSize]? = some block := by
      simpa [fixedWeightChunkBlocks] using hget
    simpa [start] using
      SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
  have hstart_le_pos : start <= pos := by
    simpa [start] using Nat.div_mul_le_self pos blockSize
  have hoffset_lt_blockSize : offset < blockSize := by
    have hlt := Nat.lt_div_mul_add hblockSize (a := pos)
    simp [offset, start]
    omega
  have hoffset_le_drop_length :
      offset <= (bits.drop start).length := by
    rw [List.length_drop]
    omega
  have hoffset_le_take_length :
      offset <= ((bits.drop start).take blockSize).length := by
    rw [List.length_take]
    exact Nat.le_min.mpr
      ⟨Nat.le_of_lt hoffset_lt_blockSize, hoffset_le_drop_length⟩
  have htake :
      Succinct.rankPrefix target ((bits.drop start).take blockSize)
          offset =
        Succinct.rankPrefix target (bits.drop start) offset :=
    Succinct.rankPrefix_take_eq_of_le
      target (bits.drop start) (n := blockSize)
      (limit := offset) hoffset_le_take_length
  have hdrop :
      Succinct.rankPrefix target (bits.drop start) offset =
        Succinct.rankPrefix target bits pos -
          Succinct.rankPrefix target bits start := by
    simpa [offset] using
      Succinct.rankPrefix_drop_eq_sub_of_le
        target bits hstart_le_pos hpos
  have hprefix_le :
      Succinct.rankPrefix target bits start <=
        Succinct.rankPrefix target bits pos :=
    Succinct.rankPrefix_mono_limit target bits hstart_le_pos
  calc
    Succinct.rankPrefix target bits ((pos / blockSize) * blockSize) +
        Succinct.rankPrefix target block
          (pos - (pos / blockSize) * blockSize) =
      Succinct.rankPrefix target bits start +
        Succinct.rankPrefix target block offset := by rfl
    _ = Succinct.rankPrefix target bits start +
        Succinct.rankPrefix target ((bits.drop start).take blockSize)
          offset := by
          rw [hwordEq]
    _ = Succinct.rankPrefix target bits start +
        Succinct.rankPrefix target (bits.drop start) offset := by
          rw [htake]
    _ = Succinct.rankPrefix target bits start +
        (Succinct.rankPrefix target bits pos -
          Succinct.rankPrefix target bits start) := by
          rw [hdrop]
    _ = Succinct.rankPrefix target bits pos := by omega

theorem fixedWeightChunkBlocks_get?_select_exact_of_global_select
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    {bits block : List Bool} {target : Bool}
    {occurrence idx : Nat}
    (hselect : Succinct.select target bits occurrence = some idx)
    (hget :
      (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
        some block) :
    (Succinct.select target block
        (occurrence -
          Succinct.rankPrefix target bits
            ((idx / blockSize) * blockSize))).map
        (fun offset => (idx / blockSize) * blockSize + offset) =
      some idx := by
  let start := (idx / blockSize) * blockSize
  let localOccurrence :=
    occurrence - Succinct.rankPrefix target bits start
  have hidx_lt : idx < bits.length :=
    Succinct.select_bounds hselect
  have hstart_le_idx : start <= idx := by
    simpa [start] using Nat.div_mul_le_self idx blockSize
  have hstart_le_len : start <= bits.length :=
    Nat.le_trans hstart_le_idx (Nat.le_of_lt hidx_lt)
  have hlocal_lt : idx - start < blockSize := by
    have hlt := Nat.lt_div_mul_add hblockSize (a := idx)
    simp [start]
    omega
  have hwordEq :
      block = (bits.drop start).take blockSize := by
    have hchunk :
        (SuccinctSpace.chunkPayloadWords blockSize bits)[
            idx / blockSize]? = some block := by
      simpa [fixedWeightChunkBlocks] using hget
    simpa [start] using
      SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
  have hrank_le :
      Succinct.rankPrefix target bits start <= occurrence :=
    Succinct.rankPrefix_le_occurrence_of_le_select
      hselect hstart_le_idx
  have hdrop :
      Succinct.select target (bits.drop start) localOccurrence =
        some (idx - start) := by
    simpa [localOccurrence] using
      Succinct.select_drop_eq_sub_of_select
        hselect hstart_le_idx hstart_le_len hrank_le
  have htake :
      Succinct.select target ((bits.drop start).take blockSize)
          localOccurrence =
        some (idx - start) :=
    Succinct.select_take_of_select_lt hdrop hlocal_lt
  rw [hwordEq]
  rw [htake]
  change some (start + (idx - start)) = some idx
  have hsum : start + (idx - start) = idx := by omega
  rw [hsum]

theorem fixedWeightBlockClassLengthTableOverhead_le_of_bounds
    {fieldWidth fieldWidthBound blockCountBound : Nat}
    {blocks : List (List Bool)}
    (hblocks : blocks.length <= blockCountBound)
    (hfield : fieldWidth <= fieldWidthBound) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      (blockCountBound + blockCountBound) * fieldWidthBound := by
  unfold fixedWeightBlockClassLengthTableOverhead
  exact Nat.mul_le_mul (by omega) hfield

theorem fixedWeightBlockClassLengthTableOverhead_le_budget
    {fieldWidth : Nat} {blockCountBound fieldWidthBound : Nat -> Nat}
    {blocks : List (List Bool)} {n : Nat}
    (hblocks : blocks.length <= blockCountBound n)
    (hfield : fieldWidth <= fieldWidthBound n) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        blockCountBound fieldWidthBound n := by
  exact fixedWeightBlockClassLengthTableOverhead_le_of_bounds
    hblocks hfield

theorem fixedWeightBlockClassLengthTableOverhead_le_chunk_budget
    {blockSize fieldWidth : Nat} {fieldWidthBound : Nat -> Nat}
    {bits : List Bool} {blocks : List (List Bool)}
    (hblockSize : 0 < blockSize)
    (hblocks :
      blocks = fixedWeightChunkBlocks blockSize bits)
    (hfield : fieldWidth <= fieldWidthBound bits.length) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        (fixedWeightChunkBlockCountBound blockSize)
        fieldWidthBound bits.length := by
  have hcount :
      blocks.length <=
        fixedWeightChunkBlockCountBound blockSize bits.length := by
    rw [hblocks]
    exact fixedWeightChunkBlocks_length_le hblockSize bits
  exact fixedWeightBlockClassLengthTableOverhead_le_budget
    hcount hfield

theorem fixedWeightBlockClassLengthTableOverhead_le_chunk_sentinel_budget
    {blockSize fieldWidth : Nat} {fieldWidthBound : Nat -> Nat}
    {bits : List Bool} {blocks : List (List Bool)}
    (hblockSize : 0 < blockSize)
    (hblocks :
      blocks = fixedWeightChunkBlocksWithSentinel blockSize bits)
    (hfield : fieldWidth <= fieldWidthBound bits.length) :
    fixedWeightBlockClassLengthTableOverhead fieldWidth blocks <=
      fixedWeightBlockClassLengthTableOverheadBudget
        (fixedWeightChunkBlockCountBoundWithSentinel blockSize)
        fieldWidthBound bits.length := by
  have hcount :
      blocks.length <=
        fixedWeightChunkBlockCountBoundWithSentinel
          blockSize bits.length := by
    rw [hblocks]
    exact fixedWeightChunkBlocksWithSentinel_length_le hblockSize bits
  exact fixedWeightBlockClassLengthTableOverhead_le_budget
    hcount hfield

def fixedWeightChunkAccessRouteWithSentinel
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) (i : Nat) :
    FixedWeightAmbientComputedRRRAccessRoute bits
      (fixedWeightChunkBlocksWithSentinel blockSize bits) i := by
  by_cases hi : i < bits.length
  · have hstart_lt :
        (i / blockSize) * blockSize < bits.length := by
      have hstart_le : (i / blockSize) * blockSize <= i :=
        Nat.div_mul_le_self i blockSize
      omega
    cases hgetOpt :
        (fixedWeightChunkBlocks blockSize bits)[i / blockSize]? with
    | none =>
        exfalso
        have hsome :
            ∃ block,
              (fixedWeightChunkBlocks blockSize bits)[i / blockSize]? =
                some block := by
          rcases
              SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
                (wordSize := blockSize) hblockSize
                (payload := bits) (i := i / blockSize) hstart_lt with
            ⟨block, hchunk⟩
          exact ⟨block, by
            simpa [fixedWeightChunkBlocks] using hchunk⟩
        rcases hsome with ⟨block, hget⟩
        simp [hgetOpt] at hget
    | some block =>
        have hget :
            (fixedWeightChunkBlocks blockSize bits)[i / blockSize]? =
              some block := hgetOpt
        refine
          { blockIndex := i / blockSize
            block := block
            block_get :=
              fixedWeightChunkBlocksWithSentinel_get_chunk hget
            offset := i - (i / blockSize) * blockSize
            metadataReads := []
            access_exact := ?_ }
        exact fixedWeightChunkBlocks_get?_access_exact hblockSize hget
  · refine
      { blockIndex := (fixedWeightChunkBlocks blockSize bits).length
        block := []
        block_get :=
          fixedWeightChunkBlocksWithSentinel_get_sentinel blockSize bits
        offset := 0
        metadataReads := []
        access_exact := ?_ }
    have hnone : bits[i]? = none := by
      rw [List.getElem?_eq_none_iff]
      omega
    simp [hnone]

def fixedWeightChunkRankRouteWithSentinel
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) (target : Bool) (pos : Nat) :
    FixedWeightAmbientComputedRRRRankRoute bits
      (fixedWeightChunkBlocksWithSentinel blockSize bits) target pos := by
  by_cases hpos : pos < bits.length
  · have hstart_lt :
        (pos / blockSize) * blockSize < bits.length := by
      have hstart_le : (pos / blockSize) * blockSize <= pos :=
        Nat.div_mul_le_self pos blockSize
      omega
    cases hgetOpt :
        (fixedWeightChunkBlocks blockSize bits)[pos / blockSize]? with
    | none =>
        exfalso
        have hsome :
            ∃ block,
              (fixedWeightChunkBlocks blockSize bits)[pos / blockSize]? =
                some block := by
          rcases
              SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
                (wordSize := blockSize) hblockSize
                (payload := bits) (i := pos / blockSize) hstart_lt with
            ⟨block, hchunk⟩
          exact ⟨block, by
            simpa [fixedWeightChunkBlocks] using hchunk⟩
        rcases hsome with ⟨block, hget⟩
        simp [hgetOpt] at hget
    | some block =>
        have hget :
            (fixedWeightChunkBlocks blockSize bits)[pos / blockSize]? =
              some block := hgetOpt
        refine
          { blockIndex := pos / blockSize
            block := block
            block_get :=
              fixedWeightChunkBlocksWithSentinel_get_chunk hget
            localLimit := pos - (pos / blockSize) * blockSize
            baseRank :=
              Succinct.rankPrefix target bits
                ((pos / blockSize) * blockSize)
            metadataReads := []
            rank_exact := ?_ }
        exact
          fixedWeightChunkBlocks_get?_rankPrefix_add_exact
            hblockSize (Nat.le_of_lt hpos) hget
  · refine
      { blockIndex := (fixedWeightChunkBlocks blockSize bits).length
        block := []
        block_get :=
          fixedWeightChunkBlocksWithSentinel_get_sentinel blockSize bits
        localLimit := 0
        baseRank := Succinct.rankPrefix target bits bits.length
        metadataReads := []
        rank_exact := ?_ }
    have hlen : bits.length <= pos := Nat.le_of_not_gt hpos
    have hrank :=
      Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen
    simp [hrank, Succinct.rankPrefix]

def fixedWeightChunkSelectRouteWithSentinel
    {blockSize : Nat} (hblockSize : 0 < blockSize)
    (bits : List Bool) (target : Bool) (occurrence : Nat) :
    FixedWeightAmbientComputedRRRSelectRoute bits
      (fixedWeightChunkBlocksWithSentinel blockSize bits)
      target occurrence := by
  cases hselectOpt : Succinct.select target bits occurrence with
  | none =>
      refine
        { blockIndex := (fixedWeightChunkBlocks blockSize bits).length
          block := []
          block_get :=
            fixedWeightChunkBlocksWithSentinel_get_sentinel blockSize bits
          localOccurrence := 0
          blockStart := 0
          metadataReads := []
          select_exact := ?_ }
      simpa [Succinct.select, Succinct.selectFrom] using hselectOpt.symm
  | some idx =>
      have hselect :
          Succinct.select target bits occurrence = some idx := hselectOpt
      have hidx_lt : idx < bits.length :=
        Succinct.select_bounds hselect
      have hstart_lt :
          (idx / blockSize) * blockSize < bits.length := by
        have hstart_le : (idx / blockSize) * blockSize <= idx :=
          Nat.div_mul_le_self idx blockSize
        omega
      cases hgetOpt :
          (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? with
      | none =>
          exfalso
          have hsome :
              ∃ block,
                (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
                  some block := by
            rcases
                SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
                  (wordSize := blockSize) hblockSize
                  (payload := bits) (i := idx / blockSize) hstart_lt with
              ⟨block, hchunk⟩
            exact ⟨block, by
              simpa [fixedWeightChunkBlocks] using hchunk⟩
          rcases hsome with ⟨block, hget⟩
          simp [hgetOpt] at hget
      | some block =>
          have hget :
              (fixedWeightChunkBlocks blockSize bits)[idx / blockSize]? =
                some block := hgetOpt
          refine
            { blockIndex := idx / blockSize
              block := block
              block_get :=
                fixedWeightChunkBlocksWithSentinel_get_chunk hget
              localOccurrence :=
                occurrence -
                  Succinct.rankPrefix target bits
                    ((idx / blockSize) * blockSize)
              blockStart := (idx / blockSize) * blockSize
              metadataReads := []
              select_exact := ?_ }
          rw [hselect]
          exact
            fixedWeightChunkBlocks_get?_select_exact_of_global_select
              hblockSize hselect hget

theorem fixedWeightBlockClassLengthTablePayload_length
    (fieldWidth : Nat) (blocks : List (List Bool)) :
    (fixedWeightBlockClassLengthTablePayload fieldWidth blocks).length =
      fixedWeightBlockClassLengthTableOverhead fieldWidth blocks := by
  simp [fixedWeightBlockClassLengthTablePayload,
    fixedWeightBlockClassLengthTableWords,
    fixedWeightBlockClassLengthTableOverhead,
    SuccinctSpace.flattenPayloadWords_append,
    fixedWeightRouteFieldTablePayload_length,
    Nat.add_mul]

def fixedWeightBlockClassLengthBoundedStore
    (blocks : List (List Bool)) {wordSize fieldWidth : Nat}
    (hfield : fieldWidth <= wordSize) :
    SuccinctSpace.BoundedPayloadWordStore
      (fixedWeightBlockClassLengthTablePayload fieldWidth blocks)
      wordSize where
  store :=
    { words :=
        (fixedWeightBlockClassLengthTableWords fieldWidth blocks).toArray
      erases := by
        simp [fixedWeightBlockClassLengthTablePayload] }
  word_length_le := by
    intro word hmem
    have hlist :
        List.Mem word
          (fixedWeightBlockClassLengthTableWords fieldWidth blocks) := by
      simpa using hmem
    rw [fixedWeightBlockClassLengthTableWords] at hlist
    rcases List.mem_append.mp hlist with hlength | hclass
    · have hmap :
          ∃ entry, List.Mem entry (fixedWeightBlockLengthEntries blocks) ∧
            SuccinctSpace.natToBitsLE fieldWidth entry = word := by
        simpa [fixedWeightRouteFieldTableWords] using hlength
      rcases hmap with ⟨entry, _hentry, hword⟩
      rw [<- hword]
      simpa [SuccinctSpace.natToBitsLE_length] using hfield
    · have hmap :
          ∃ entry, List.Mem entry (fixedWeightBlockClassEntries blocks) ∧
            SuccinctSpace.natToBitsLE fieldWidth entry = word := by
        simpa [fixedWeightRouteFieldTableWords] using hclass
      rcases hmap with ⟨entry, _hentry, hword⟩
      rw [<- hword]
      simpa [SuccinctSpace.natToBitsLE_length] using hfield

theorem fixedWeightBlockClassLengthBoundedStore_words_toList
    (blocks : List (List Bool)) {wordSize fieldWidth : Nat}
    (hfield : fieldWidth <= wordSize) :
    (fixedWeightBlockClassLengthBoundedStore
        blocks (wordSize := wordSize) hfield).store.words.toList =
      fixedWeightBlockClassLengthTableWords fieldWidth blocks := by
  rfl

end RankSelectSpec

end RMQ
