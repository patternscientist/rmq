import RMQ.Core.RankSelectCompressedSubLogRankRoute

/-!
# Sub-log dense-word reads for compressed/FID select

This module starts the positive replacement for the generic Clark dense branch.
The generic sparse/dense select source reads raw `bits` words in its dense
case.  Here we expose the constant-size sub-log block window that can cover the
same two machine words when the fixed-weight block size is
`log n / 8 + 1`.
-/

namespace RMQ

namespace RankSelectSpec

def fixedWeightSubLogDenseWindowBlockCount : Nat := 20

def fixedWeightSubLogDenseWindowReadCost : Nat :=
  fixedWeightSubLogDenseWindowBlockCount * 4

theorem fixedWeightSubLogDenseWindowBlockCount_pos :
    0 < fixedWeightSubLogDenseWindowBlockCount := by
  decide

theorem two_machineWordBits_le_eighteen_subLogChunkBlockSize
    (n : Nat) :
    2 * SuccinctRank.machineWordBits n <=
      18 * fixedWeightSubLogChunkBlockSize n := by
  have hlt :
      Nat.log2 n < Nat.log2 n / 8 * 8 + 8 :=
    Nat.lt_div_mul_add (by omega : 0 < 8) (a := Nat.log2 n)
  unfold SuccinctRank.machineWordBits fixedWeightSubLogChunkBlockSize
  omega

theorem two_machineWordBits_add_subLogChunkBlockSize_le_window
    (n : Nat) :
    fixedWeightSubLogChunkBlockSize n +
        2 * SuccinctRank.machineWordBits n <=
      fixedWeightSubLogDenseWindowBlockCount *
        fixedWeightSubLogChunkBlockSize n := by
  have htwo := two_machineWordBits_le_eighteen_subLogChunkBlockSize n
  have hpos := fixedWeightSubLogChunkBlockSize_pos n
  unfold fixedWeightSubLogDenseWindowBlockCount
  omega

theorem subLogMachineWordWindow_covered
    (bits : List Bool) (start : Nat) :
    start + 2 * SuccinctRank.machineWordBits bits.length <=
      (start / fixedWeightSubLogChunkBlockSize bits.length +
          fixedWeightSubLogDenseWindowBlockCount) *
        fixedWeightSubLogChunkBlockSize bits.length := by
  let blockSize := fixedWeightSubLogChunkBlockSize bits.length
  have hblock : 0 < blockSize := by
    exact fixedWeightSubLogChunkBlockSize_pos bits.length
  have hstart :
      start <
        start / blockSize * blockSize + blockSize :=
    Nat.lt_div_mul_add hblock (a := start)
  have hspan :
      blockSize + 2 * SuccinctRank.machineWordBits bits.length <=
        fixedWeightSubLogDenseWindowBlockCount * blockSize := by
    simpa [blockSize] using
      two_machineWordBits_add_subLogChunkBlockSize_le_window bits.length
  calc
    start + 2 * SuccinctRank.machineWordBits bits.length
        <= start / blockSize * blockSize + blockSize +
            2 * SuccinctRank.machineWordBits bits.length := by
          omega
    _ <= start / blockSize * blockSize +
            fixedWeightSubLogDenseWindowBlockCount * blockSize := by
          omega
    _ =
        (start / fixedWeightSubLogChunkBlockSize bits.length +
            fixedWeightSubLogDenseWindowBlockCount) *
          fixedWeightSubLogChunkBlockSize bits.length := by
          simp [blockSize, Nat.add_mul]

def subLogDecodeBlockByIndexCosted
    (bits : List Bool) (blockIndex : Nat) : Costed (List Bool) :=
  Costed.bind
      ((subLogCodeStore bits).store.readWordCosted blockIndex)
      fun code? =>
  Costed.bind
      ((subLogLenStore bits).store.readWordCosted blockIndex)
      fun len? =>
  Costed.bind
      ((subLogClassStore bits).store.readWordCosted blockIndex)
      fun class? =>
  Costed.bind
      (subLogDecodeReadCosted bits
        (fixedWeightSharedDecodeSlotFromReadValues [len?, class?] [code?]))
      fun decoded? =>
    Costed.pure (decoded?.getD [])

theorem subLogDecodeBlockByIndexCosted_cost
    (bits : List Bool) (blockIndex : Nat) :
    (subLogDecodeBlockByIndexCosted bits blockIndex).cost = 4 := by
  simp [subLogDecodeBlockByIndexCosted]

theorem subLogDecodeBlockByIndexCosted_erase_of_get?
    {bits : List Bool} {blockIndex : Nat} {block : List Bool}
    (hblock :
      (fixedWeightSubLogChunkBlocksWithSentinel bits)[blockIndex]? =
        some block) :
    (subLogDecodeBlockByIndexCosted bits blockIndex).erase = block := by
  have hmem :
      List.Mem block (fixedWeightSubLogChunkBlocksWithSentinel bits) :=
    List.mem_of_getElem? hblock
  have hcode := subLogCodeStore_get? hblock
  have hlen := subLogLenStore_get? hblock
  have hclass := subLogClassStore_get? hblock
  have hlenlt := subLogBlock_length_lt hmem
  have hclasslt := subLogBlock_trueCount_lt hmem
  simp only [subLogDecodeBlockByIndexCosted, Costed.erase_bind,
    Costed.erase_pure, subLogDecodeReadCosted,
    SuccinctSpace.PayloadWordStore.readWordCosted_erase]
  rw [hcode, hlen, hclass,
    fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix [] hlenlt
      hclasslt,
    fixedWeightSubLogSharedDecoderStore_get?_of_block hblock]
  simp

def subLogDecodeBlockWindowCosted
    (bits : List Bool) (startBlock count : Nat) :
    Costed (List (List Bool)) :=
  match count with
  | 0 => Costed.pure []
  | count' + 1 =>
      Costed.bind
          (subLogDecodeBlockByIndexCosted bits startBlock) fun block =>
        Costed.map
          (fun rest => block :: rest)
          (subLogDecodeBlockWindowCosted bits (startBlock + 1) count')

theorem subLogDecodeBlockWindowCosted_cost
    (bits : List Bool) (startBlock count : Nat) :
    (subLogDecodeBlockWindowCosted bits startBlock count).cost =
      count * 4 := by
  induction count generalizing startBlock with
  | zero =>
      simp [subLogDecodeBlockWindowCosted, Costed.pure]
  | succ count ih =>
      change
        (Costed.bind
            (subLogDecodeBlockByIndexCosted bits startBlock)
            (fun block =>
              Costed.map
                (fun rest => block :: rest)
                (subLogDecodeBlockWindowCosted
                  bits (startBlock + 1) count))).cost =
          (count + 1) * 4
      rw [Costed.cost_bind, Costed.map_cost,
        subLogDecodeBlockByIndexCosted_cost, ih]
      omega

private theorem list_take_add_eq_take_append_drop_take
    {α : Type} (xs : List α) (a b : Nat) :
    xs.take (a + b) = xs.take a ++ (xs.drop a).take b := by
  induction a generalizing xs with
  | zero =>
      simp
  | succ a ih =>
      cases xs with
      | nil =>
          simp
      | cons x xs =>
          simp [Nat.succ_add, ih]

private theorem subLogDecodeBlockWindowCosted_flatten_take_eq
    (bits : List Bool) (startBlock count takeBits : Nat)
    (hcover :
      takeBits <=
        count * fixedWeightSubLogChunkBlockSize bits.length)
    (hwithin :
      startBlock * fixedWeightSubLogChunkBlockSize bits.length +
          takeBits <= bits.length) :
    (SuccinctSpace.flattenPayloadWords
        (subLogDecodeBlockWindowCosted
          bits startBlock count).erase).take takeBits =
      (bits.drop
        (startBlock * fixedWeightSubLogChunkBlockSize bits.length)).take
        takeBits := by
  let blockSize := fixedWeightSubLogChunkBlockSize bits.length
  have hblockSize : 0 < blockSize := by
    exact fixedWeightSubLogChunkBlockSize_pos bits.length
  induction count generalizing startBlock takeBits with
  | zero =>
      have hzero : takeBits = 0 := by
        simpa [blockSize] using hcover
      simp [hzero, subLogDecodeBlockWindowCosted]
  | succ count ih =>
      by_cases htake_zero : takeBits = 0
      · simp [htake_zero]
      · have hcoverBlock :
            takeBits <= (count + 1) * blockSize := by
          simpa [blockSize] using hcover
        have hwithinBlock :
            startBlock * blockSize + takeBits <= bits.length := by
          simpa [blockSize] using hwithin
        have hbase_lt :
            startBlock * blockSize < bits.length := by
          have hpos : 0 < takeBits := Nat.pos_of_ne_zero htake_zero
          omega
        rcases
            SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
              (wordSize := blockSize) hblockSize
              (payload := bits) (i := startBlock) hbase_lt with
          ⟨block, hchunk⟩
        have hfixed :
            (fixedWeightChunkBlocks blockSize bits)[startBlock]? =
              some block := by
          simpa [fixedWeightChunkBlocks] using hchunk
        have hsentinel :
            (fixedWeightSubLogChunkBlocksWithSentinel bits)[startBlock]? =
              some block := by
          simpa [fixedWeightSubLogChunkBlocksWithSentinel, blockSize] using
            fixedWeightChunkBlocksWithSentinel_get_chunk hfixed
        have hblockEq :
            block = (bits.drop (startBlock * blockSize)).take blockSize := by
          simpa [blockSize] using
            SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hchunk
        have hdecode :=
          subLogDecodeBlockByIndexCosted_erase_of_get? hsentinel
        have hflat :
            SuccinctSpace.flattenPayloadWords
                (subLogDecodeBlockWindowCosted
                  bits startBlock (count + 1)).erase =
              block ++
                SuccinctSpace.flattenPayloadWords
                  (subLogDecodeBlockWindowCosted
                    bits (startBlock + 1) count).erase := by
          simp [subLogDecodeBlockWindowCosted, Costed.erase_bind,
            Costed.erase_map, hdecode, SuccinctSpace.flattenPayloadWords]
        by_cases hle : takeBits <= blockSize
        · have hblock_len_ge :
              takeBits <=
                ((bits.drop (startBlock * blockSize)).take blockSize).length := by
            rw [List.length_take, List.length_drop]
            exact Nat.le_min.mpr ⟨hle, by omega⟩
          rw [hflat, hblockEq, List.take_append]
          have htail_zero :
              takeBits -
                  Nat.min blockSize
                    (bits.length - startBlock * blockSize) = 0 := by
            apply Nat.sub_eq_zero_of_le
            exact Nat.le_min.mpr ⟨hle, by omega⟩
          have htake_take :
              ((bits.drop (startBlock * blockSize)).take blockSize).take
                  takeBits =
                (bits.drop (startBlock * blockSize)).take takeBits := by
            rw [List.take_take]
            have hmin : Nat.min takeBits blockSize = takeBits := by
              exact Nat.min_eq_left hle
            simp [hmin]
          simp [List.length_take, List.length_drop, htail_zero,
            htake_take, blockSize]
        · have hblock_lt : blockSize < takeBits := by omega
          have hblock_len :
              ((bits.drop (startBlock * blockSize)).take blockSize).length =
                blockSize := by
            rw [List.length_take, List.length_drop]
            have hlen : blockSize <= bits.length - startBlock * blockSize := by
              omega
            simp [Nat.min_eq_left hlen]
          have hcover_tail :
              takeBits - blockSize <= count * blockSize := by
            have hcoverBlock' :
                takeBits <= count * blockSize + blockSize := by
              simpa [Nat.add_mul, Nat.mul_comm, Nat.mul_left_comm,
                Nat.mul_assoc] using hcoverBlock
            omega
          have hcover_tail_fixed :
              takeBits - blockSize <=
                count * fixedWeightSubLogChunkBlockSize bits.length := by
            simpa [blockSize] using hcover_tail
          have hwithin_tail :
              (startBlock + 1) * blockSize +
                  (takeBits - blockSize) <= bits.length := by
            rw [Nat.add_mul]
            omega
          have hwithin_tail_fixed :
              (startBlock + 1) *
                    fixedWeightSubLogChunkBlockSize bits.length +
                  (takeBits - blockSize) <= bits.length := by
            simpa [blockSize] using hwithin_tail
          have htail :=
            ih (startBlock + 1) (takeBits - blockSize)
              hcover_tail_fixed hwithin_tail_fixed
          have htake_long :
              ((bits.drop (startBlock * blockSize)).take blockSize).take
                  takeBits =
                (bits.drop (startBlock * blockSize)).take blockSize := by
            rw [List.take_take]
            have hmin : Nat.min takeBits blockSize = blockSize := by
              exact Nat.min_eq_right (Nat.le_of_lt hblock_lt)
            simp [hmin]
          have hsplit :
              (bits.drop (startBlock * blockSize)).take takeBits =
                (bits.drop (startBlock * blockSize)).take blockSize ++
                  (bits.drop ((startBlock + 1) * blockSize)).take
                    (takeBits - blockSize) := by
            have hadd : takeBits = blockSize + (takeBits - blockSize) := by
              omega
            rw [hadd]
            rw [list_take_add_eq_take_append_drop_take]
            simp only [List.drop_drop]
            rw [show startBlock * blockSize + blockSize =
                (startBlock + 1) * blockSize by
              rw [Nat.add_mul]
              simp]
            simp
          rw [hflat, hblockEq, List.take_append, hblock_len, htail,
            htake_long, hsplit]

/--
Extract the machine word beginning at `wordIndex` from an already decoded
sub-log block window.

The arithmetic uses only public shape data (`bits.length` and the fixed block
size); the returned bits come from the charged decoded window.  The final
`min` prevents decoder-table defaults past the sentinel from contributing to a
last, short machine word.
-/
def subLogMachineWordFromDecodedWindow
    (bits : List Bool) (wordIndex : Nat)
    (decodedWindow : List (List Bool)) : List Bool :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let blockSize := fixedWeightSubLogChunkBlockSize bits.length
  let startBlock := start / blockSize
  let localOffset := start - startBlock * blockSize
  let width := Nat.min wordSize (bits.length - start)
  (SuccinctSpace.flattenPayloadWords decodedWindow).drop localOffset |>.take
    width

/--
Read the bounded sub-log block window covering the two machine words beginning
at `wordIndex`, then extract the corresponding machine word from that decoded
window.
-/
def subLogMachineWordReadCosted
    (bits : List Bool) (wordIndex : Nat) : Costed (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let startBlock := start / fixedWeightSubLogChunkBlockSize bits.length
  Costed.bind
    (subLogDecodeBlockWindowCosted bits startBlock
      fixedWeightSubLogDenseWindowBlockCount)
    fun decodedWindow =>
      Costed.pure
        (subLogMachineWordFromDecodedWindow bits wordIndex decodedWindow)

theorem subLogMachineWordReadCosted_cost
    (bits : List Bool) (wordIndex : Nat) :
    (subLogMachineWordReadCosted bits wordIndex).cost =
      fixedWeightSubLogDenseWindowReadCost := by
  simp [subLogMachineWordReadCosted, fixedWeightSubLogDenseWindowReadCost,
    subLogDecodeBlockWindowCosted_cost, Costed.cost_bind, Costed.pure]

theorem subLogMachineWordReadCosted_erase
    (bits : List Bool) (wordIndex : Nat) :
    (subLogMachineWordReadCosted bits wordIndex).erase =
      (bits.drop (wordIndex * SuccinctRank.machineWordBits bits.length)).take
        (SuccinctRank.machineWordBits bits.length) := by
  let wordSize := SuccinctRank.machineWordBits bits.length
  let start := wordIndex * wordSize
  let blockSize := fixedWeightSubLogChunkBlockSize bits.length
  let startBlock := start / blockSize
  let localOffset := start - startBlock * blockSize
  let width := Nat.min wordSize (bits.length - start)
  have hblockSize : 0 < blockSize := by
    exact fixedWeightSubLogChunkBlockSize_pos bits.length
  have hstart_le : startBlock * blockSize <= start := by
    simpa [startBlock] using Nat.div_mul_le_self start blockSize
  have hstart_eq :
      startBlock * blockSize + localOffset = start := by
    simp [localOffset]
    omega
  have hstart_eq_fixed :
      startBlock * fixedWeightSubLogChunkBlockSize bits.length +
          localOffset = start := by
    simpa [blockSize] using hstart_eq
  have hlocal_lt : localOffset < blockSize := by
    have hlt := Nat.lt_div_mul_add hblockSize (a := start)
    have hlt' : start < startBlock * blockSize + blockSize := by
      simpa [startBlock] using hlt
    rw [← hstart_eq] at hlt'
    omega
  simp [subLogMachineWordReadCosted, Costed.erase_bind, Costed.erase_pure]
  change
    subLogMachineWordFromDecodedWindow bits wordIndex
        (subLogDecodeBlockWindowCosted
          bits startBlock fixedWeightSubLogDenseWindowBlockCount).erase =
      (bits.drop start).take wordSize
  by_cases hstart_lt : start < bits.length
  · have hwidth_le_word : width <= wordSize := by
      exact Nat.min_le_left wordSize (bits.length - start)
    have hwidth_le_available : width <= bits.length - start := by
      exact Nat.min_le_right wordSize (bits.length - start)
    have hspan :
        blockSize + 2 * wordSize <=
          fixedWeightSubLogDenseWindowBlockCount * blockSize := by
      simpa [blockSize, wordSize] using
        two_machineWordBits_add_subLogChunkBlockSize_le_window bits.length
    have hcover :
        localOffset + width <=
          fixedWeightSubLogDenseWindowBlockCount * blockSize := by
      omega
    have hcover_fixed :
        localOffset + width <=
          fixedWeightSubLogDenseWindowBlockCount *
            fixedWeightSubLogChunkBlockSize bits.length := by
      simpa [blockSize] using hcover
    have hwithin :
        startBlock * blockSize + (localOffset + width) <= bits.length := by
      rw [← Nat.add_assoc, hstart_eq]
      omega
    have hwithin_fixed :
        startBlock * fixedWeightSubLogChunkBlockSize bits.length +
            (localOffset + width) <= bits.length := by
      simpa [blockSize] using hwithin
    have hprefix :=
      subLogDecodeBlockWindowCosted_flatten_take_eq
        bits startBlock fixedWeightSubLogDenseWindowBlockCount
        (localOffset + width) hcover_fixed hwithin_fixed
    have hdropPrefix :=
      congrArg (fun xs : List Bool => xs.drop localOffset) hprefix
    have hwindow :
        ((SuccinctSpace.flattenPayloadWords
              (subLogDecodeBlockWindowCosted
                bits startBlock
                  fixedWeightSubLogDenseWindowBlockCount).erase).drop
              localOffset).take width =
          (bits.drop start).take width := by
      simpa [List.drop_take, List.drop_drop, hstart_eq,
        hstart_eq_fixed, Nat.add_sub_cancel_left] using hdropPrefix
    have htakeWidth :
        (bits.drop start).take wordSize =
          (bits.drop start).take width := by
      rw [List.take_eq_take_iff]
      rw [List.length_drop]
      have hmin_right :
          Nat.min width (bits.length - start) = width :=
        Nat.min_eq_left hwidth_le_available
      simp [width, hmin_right]
    exact by
      simpa [subLogMachineWordFromDecodedWindow, wordSize, start,
        blockSize, startBlock, localOffset, width] using
        hwindow.trans htakeWidth.symm
  · have hstart_ge : bits.length <= start := Nat.le_of_not_gt hstart_lt
    have hwidth : width = 0 := by
      simp [width]
      omega
    have hdrop_nil : bits.drop start = [] := by
      apply List.eq_nil_of_length_eq_zero
      rw [List.length_drop]
      omega
    simp [subLogMachineWordFromDecodedWindow, wordSize, start, blockSize,
      startBlock, width, hwidth, hdrop_nil]

def subLogDenseTwoWordSelectCosted
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let wordSize := SuccinctRank.machineWordBits bits.length
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind (subLogMachineWordReadCosted bits firstWordIndex) fun firstWord =>
    Costed.bind
      (RMQ.RAM.rankBoolWordPrefix target firstWord firstOffset).toCosted
      fun beforeFirst =>
        Costed.bind
          (RMQ.RAM.rankBoolWordPrefix
            target firstWord firstWord.length).toCosted
          fun uptoFirst =>
            let firstCount := uptoFirst - beforeFirst
            if localOccurrence < firstCount then
              Costed.map
                (fun local? =>
                  local?.map fun offset => firstWordStart + offset)
                (RMQ.RAM.selectBoolWord target firstWord
                  (beforeFirst + localOccurrence)).toCosted
            else
              Costed.bind
                (subLogMachineWordReadCosted bits (firstWordIndex + 1))
                fun secondWord =>
                  Costed.map
                    (fun local? =>
                      local?.map fun offset =>
                        (firstWordIndex + 1) * wordSize + offset)
                    (RMQ.RAM.selectBoolWord target secondWord
                      (localOccurrence - firstCount)).toCosted

theorem subLogDenseTwoWordSelectCosted_cost_le
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).cost <=
      2 * fixedWeightSubLogDenseWindowReadCost + 3 := by
  unfold subLogDenseTwoWordSelectCosted
  by_cases hchoose :
      q - baseOccurrence <
        RMQ.RAM.boolRankPrefix target
          (subLogMachineWordReadCosted bits
            (basePosition / SuccinctRank.machineWordBits bits.length)).value
          (subLogMachineWordReadCosted bits
            (basePosition / SuccinctRank.machineWordBits bits.length)).value.length -
        RMQ.RAM.boolRankPrefix target
          (subLogMachineWordReadCosted bits
            (basePosition / SuccinctRank.machineWordBits bits.length)).value
          (basePosition -
            basePosition / SuccinctRank.machineWordBits bits.length *
              SuccinctRank.machineWordBits bits.length)
  · simp [Costed.cost_bind, subLogMachineWordReadCosted_cost,
      RMQ.RAM.Exec.toCosted, hchoose]
    omega
  · simp [Costed.cost_bind, subLogMachineWordReadCosted_cost,
      RMQ.RAM.Exec.toCosted, hchoose]
    omega

set_option linter.unusedSimpArgs false in
theorem subLogDenseTwoWordSelectCosted_exact_of_payload_routing_facts
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat)
    (hfacts :
      GenericSelect.DenseLocalPayloadRoutingFacts
        target bits (SuccinctRank.machineWordBits bits.length)
          basePosition baseOccurrence q) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).erase =
      Succinct.select target bits q := by
  let wordSize := SuccinctRank.machineWordBits bits.length
  let bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks bits
      (by
        simpa [wordSize] using
          SuccinctRank.machineWordBits_pos bits.length)
  have haligned :
      GenericSelect.SelectAlignedBitWords bits wordSize bitWords := by
    simpa [wordSize, bitWords] using
      GenericSelect.selectAlignedBitWords_ofChunks bits
        (GenericSelect.wordBits_pos bits.length)
  have hcert :
      GenericSelect.DenseLocalSpanCertificate
        target bits wordSize bitWords basePosition baseOccurrence q :=
    GenericSelect.denseLocalSpanCertificate_of_payload_routing_facts
      haligned (by simpa [wordSize] using hfacts)
  have hfirstWord :
      (subLogMachineWordReadCosted
        bits (basePosition / wordSize)).erase = hcert.firstWord := by
    rw [subLogMachineWordReadCosted_erase]
    exact (haligned.get_eq_take_drop hcert.first_read).symm
  by_cases hchoose :
      q - baseOccurrence <
        RMQ.RAM.boolRankPrefix target hcert.firstWord
          hcert.firstWord.length -
          RMQ.RAM.boolRankPrefix target hcert.firstWord
            (basePosition - basePosition / wordSize * wordSize)
  · have hexact := hcert.first_branch_exact hchoose
    simp [subLogDenseTwoWordSelectCosted, wordSize, Costed.erase_bind,
      Costed.erase_map, Costed.erase_pure, RMQ.RAM.Exec.toCosted,
      hfirstWord, hchoose, hexact]
  · have hsecond := hcert.second_branch_exact hchoose
    rcases hsecond with ⟨secondWord, hsecondRead, hexact⟩
    have hsecondWord :
        (subLogMachineWordReadCosted
          bits (basePosition / wordSize + 1)).erase = secondWord := by
      rw [subLogMachineWordReadCosted_erase]
      exact (haligned.get_eq_take_drop hsecondRead).symm
    simp [subLogDenseTwoWordSelectCosted, wordSize, Costed.erase_bind,
      Costed.erase_map, Costed.erase_pure, RMQ.RAM.Exec.toCosted,
      hfirstWord, hsecondWord, hchoose, hexact]

set_option linter.unusedSimpArgs false in
theorem subLogDenseTwoWordSelectCosted_exact_of_canonical_dense_exact
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat)
    (hvalid : q < GenericSelect.occurrenceCount bits target)
    (hgeneric :
      (GenericSelect.denseTwoWordSelectCosted target
        (SuccinctSpace.BoundedPayloadWordStore.ofChunks bits
          (GenericSelect.wordBits_pos bits.length))
        basePosition baseOccurrence q).erase =
        Succinct.select target bits q) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).erase =
      Succinct.select target bits q := by
  let wordSize := GenericSelect.wordBits bits.length
  let bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunks bits
      (GenericSelect.wordBits_pos bits.length)
  have haligned :
      GenericSelect.SelectAlignedBitWords bits wordSize bitWords := by
    simpa [wordSize, bitWords] using
      GenericSelect.selectAlignedBitWords_ofChunks bits
        (GenericSelect.wordBits_pos bits.length)
  rcases GenericSelect.select_exists_of_lt_occurrenceCount
      bits target hvalid with ⟨pos, hselect⟩
  have hselect_some : Succinct.select target bits q ≠ none := by
    simp [hselect]
  cases hfirst :
      (bitWords.store.readWordCosted
        (basePosition / wordSize)).value with
  | none =>
      have hfirstMachine :
          (bitWords.store.readWordCosted
            (basePosition / SuccinctRank.machineWordBits bits.length)).value =
            none := by
        simpa [wordSize, GenericSelect.wordBits] using hfirst
      have hfirstGetMachine :
          bitWords.store.words[
              basePosition / SuccinctRank.machineWordBits bits.length]? =
            none := by
        simpa [bitWords,
          SuccinctSpace.PayloadWordStore.readWordCosted, RMQ.RAM.readArray?,
          RMQ.RAM.Exec.toCosted] using hfirstMachine
      have hgenericNone :
          (GenericSelect.denseTwoWordSelectCosted target bitWords
            basePosition baseOccurrence q).erase = none := by
        simp [GenericSelect.denseTwoWordSelectCosted, bitWords, wordSize,
          Costed.erase_bind, Costed.erase_pure,
          SuccinctSpace.PayloadWordStore.readWordCosted,
          RMQ.RAM.readArray?, RMQ.RAM.Exec.toCosted, hfirstMachine,
          hfirstGetMachine, GenericSelect.wordBits]
      have hbad :
          Succinct.select target bits q = none := by
        exact hgeneric.symm.trans (by
          simpa [bitWords, wordSize] using hgenericNone)
      exact False.elim (hselect_some hbad)
  | some firstWord =>
      have hfirstMachine :
          (bitWords.store.readWordCosted
            (basePosition / SuccinctRank.machineWordBits bits.length)).value =
            some firstWord := by
        simpa [wordSize, GenericSelect.wordBits] using hfirst
      have hfirstGetMachine :
          bitWords.store.words[
              basePosition / SuccinctRank.machineWordBits bits.length]? =
            some firstWord := by
        simpa [bitWords,
          SuccinctSpace.PayloadWordStore.readWordCosted, RMQ.RAM.readArray?,
          RMQ.RAM.Exec.toCosted] using hfirstMachine
      have hfirstGet :
          bitWords.store.words[basePosition / wordSize]? =
            some firstWord := by
        simpa [bitWords, wordSize,
          SuccinctSpace.PayloadWordStore.readWordCosted, RMQ.RAM.readArray?,
          RMQ.RAM.Exec.toCosted] using hfirst
      have hfirstWord :
          (subLogMachineWordReadCosted
            bits (basePosition / wordSize)).erase = firstWord := by
        rw [subLogMachineWordReadCosted_erase]
        simpa [wordSize, GenericSelect.wordBits] using
          (haligned.get_eq_take_drop hfirstGet).symm
      have hfirstWordMachine :
          (subLogMachineWordReadCosted
            bits (basePosition /
              SuccinctRank.machineWordBits bits.length)).erase =
            firstWord := by
        simpa [wordSize, GenericSelect.wordBits] using hfirstWord
      by_cases hchoose :
          q - baseOccurrence <
            RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
              RMQ.RAM.boolRankPrefix target firstWord
                (basePosition - basePosition / wordSize * wordSize)
      case pos =>
        have hchooseMachine :
            q - baseOccurrence <
              RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
                RMQ.RAM.boolRankPrefix target firstWord
                  (basePosition -
                    basePosition /
                      SuccinctRank.machineWordBits bits.length *
                      SuccinctRank.machineWordBits bits.length) := by
          simpa [wordSize, GenericSelect.wordBits] using hchoose
        have heq :
            (subLogDenseTwoWordSelectCosted
              target bits basePosition baseOccurrence q).erase =
              (GenericSelect.denseTwoWordSelectCosted target bitWords
                basePosition baseOccurrence q).erase := by
          simp [subLogDenseTwoWordSelectCosted,
            GenericSelect.denseTwoWordSelectCosted, bitWords, wordSize,
            Costed.erase_bind, Costed.erase_map, Costed.erase_pure,
            RMQ.RAM.Exec.toCosted,
            SuccinctSpace.PayloadWordStore.readWordCosted,
            RMQ.RAM.readArray?, hfirstMachine, hfirstGetMachine, hfirstGet,
            hfirstWordMachine, hchooseMachine,
            GenericSelect.wordBits]
        exact heq.trans (by simpa [bitWords, wordSize] using hgeneric)
      case neg =>
        have hchooseMachine :
            ¬ q - baseOccurrence <
              RMQ.RAM.boolRankPrefix target firstWord firstWord.length -
                RMQ.RAM.boolRankPrefix target firstWord
                  (basePosition -
                    basePosition /
                      SuccinctRank.machineWordBits bits.length *
                      SuccinctRank.machineWordBits bits.length) := by
          intro hbad
          exact hchoose (by
            simpa [wordSize, GenericSelect.wordBits] using hbad)
        cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            have hsecondMachine :
                (bitWords.store.readWordCosted
                  (basePosition /
                    SuccinctRank.machineWordBits bits.length + 1)).value =
                  none := by
              simpa [wordSize, GenericSelect.wordBits] using hsecond
            have hsecondGetMachine :
                bitWords.store.words[
                    basePosition /
                      SuccinctRank.machineWordBits bits.length + 1]? =
                  none := by
              simpa [bitWords,
                SuccinctSpace.PayloadWordStore.readWordCosted,
                RMQ.RAM.readArray?, RMQ.RAM.Exec.toCosted] using
                hsecondMachine
            have hgenericNone :
                (GenericSelect.denseTwoWordSelectCosted target bitWords
                  basePosition baseOccurrence q).erase = none := by
              simp [GenericSelect.denseTwoWordSelectCosted, bitWords,
                wordSize, Costed.erase_bind, Costed.erase_pure,
                SuccinctSpace.PayloadWordStore.readWordCosted,
                RMQ.RAM.readArray?, RMQ.RAM.Exec.toCosted,
                hfirstMachine, hfirstGet, hchooseMachine, hsecondMachine,
                hfirstGetMachine, hsecondGetMachine, GenericSelect.wordBits]
            have hbad :
                Succinct.select target bits q = none := by
              exact hgeneric.symm.trans (by
                simpa [bitWords, wordSize] using hgenericNone)
            exact False.elim (hselect_some hbad)
        | some secondWord =>
            have hsecondMachine :
                (bitWords.store.readWordCosted
                  (basePosition /
                    SuccinctRank.machineWordBits bits.length + 1)).value =
                  some secondWord := by
              simpa [wordSize, GenericSelect.wordBits] using hsecond
            have hsecondGetMachine :
                bitWords.store.words[
                    basePosition /
                      SuccinctRank.machineWordBits bits.length + 1]? =
                  some secondWord := by
              simpa [bitWords,
                SuccinctSpace.PayloadWordStore.readWordCosted,
                RMQ.RAM.readArray?, RMQ.RAM.Exec.toCosted] using
                hsecondMachine
            have hsecondGet :
                bitWords.store.words[basePosition / wordSize + 1]? =
                  some secondWord := by
              simpa [bitWords, wordSize,
                SuccinctSpace.PayloadWordStore.readWordCosted,
                RMQ.RAM.readArray?, RMQ.RAM.Exec.toCosted] using hsecond
            have hsecondWord :
                (subLogMachineWordReadCosted
                  bits (basePosition / wordSize + 1)).erase =
                  secondWord := by
              rw [subLogMachineWordReadCosted_erase]
              simpa [wordSize, GenericSelect.wordBits] using
                (haligned.get_eq_take_drop hsecondGet).symm
            have hsecondWordMachine :
                (subLogMachineWordReadCosted
                  bits
                    (basePosition /
                      SuccinctRank.machineWordBits bits.length + 1)).erase =
                  secondWord := by
              simpa [wordSize, GenericSelect.wordBits] using hsecondWord
            have heq :
                (subLogDenseTwoWordSelectCosted
                  target bits basePosition baseOccurrence q).erase =
                  (GenericSelect.denseTwoWordSelectCosted target bitWords
                    basePosition baseOccurrence q).erase := by
              simp [subLogDenseTwoWordSelectCosted,
                GenericSelect.denseTwoWordSelectCosted, bitWords, wordSize,
                Costed.erase_bind, Costed.erase_map, Costed.erase_pure,
                RMQ.RAM.Exec.toCosted,
                SuccinctSpace.PayloadWordStore.readWordCosted,
                RMQ.RAM.readArray?, hfirstMachine, hfirstGet,
                hfirstGetMachine, hsecondMachine, hsecondGetMachine,
                hsecondGet, hfirstWordMachine,
                hsecondWordMachine, hchooseMachine, GenericSelect.wordBits]
            exact heq.trans (by simpa [bitWords, wordSize] using hgeneric)

theorem subLogDenseTwoWordSelectCosted_erase_of_exact
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat)
    (hexact :
      (subLogDenseTwoWordSelectCosted
        target bits basePosition baseOccurrence q).erase =
        Succinct.select target bits q) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).erase =
      Succinct.select target bits q := by
  exact hexact

end RankSelectSpec

namespace RankSelect

abbrev fixedWeightSubLogDenseWindowBlockCount :=
  RMQ.RankSelectSpec.fixedWeightSubLogDenseWindowBlockCount

abbrev fixedWeightSubLogDenseWindowReadCost :=
  RMQ.RankSelectSpec.fixedWeightSubLogDenseWindowReadCost

abbrev subLogMachineWordReadCosted :=
  RMQ.RankSelectSpec.subLogMachineWordReadCosted

theorem subLogMachineWordReadCostedCost
    (bits : List Bool) (wordIndex : Nat) :
    (subLogMachineWordReadCosted bits wordIndex).cost =
      fixedWeightSubLogDenseWindowReadCost := by
  exact
    RMQ.RankSelectSpec.subLogMachineWordReadCosted_cost bits wordIndex

theorem subLogMachineWordReadCostedErase
    (bits : List Bool) (wordIndex : Nat) :
    (subLogMachineWordReadCosted bits wordIndex).erase =
      (bits.drop (wordIndex * SuccinctRank.machineWordBits bits.length)).take
        (SuccinctRank.machineWordBits bits.length) := by
  exact
    RMQ.RankSelectSpec.subLogMachineWordReadCosted_erase bits wordIndex

abbrev subLogDenseTwoWordSelectCosted :=
  RMQ.RankSelectSpec.subLogDenseTwoWordSelectCosted

theorem subLogDenseTwoWordSelectCostedCostLe
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).cost <=
      2 * fixedWeightSubLogDenseWindowReadCost + 3 := by
  exact
    RMQ.RankSelectSpec.subLogDenseTwoWordSelectCosted_cost_le
      target bits basePosition baseOccurrence q

theorem subLogDenseTwoWordSelectCostedEraseOfExact
    (target : Bool) (bits : List Bool)
    (basePosition baseOccurrence q : Nat)
    (hexact :
      (subLogDenseTwoWordSelectCosted
        target bits basePosition baseOccurrence q).erase =
        Succinct.select target bits q) :
    (subLogDenseTwoWordSelectCosted
      target bits basePosition baseOccurrence q).erase =
      Succinct.select target bits q := by
  exact
    RMQ.RankSelectSpec.subLogDenseTwoWordSelectCosted_erase_of_exact
      target bits basePosition baseOccurrence q hexact

end RankSelect

end RMQ
