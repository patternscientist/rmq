import RMQ.Core.RankSelectCompressedSubLogDirectory

/-!
# Sub-log rank route tables

This module builds the rank half of the concrete sub-log compressed/FID route
directory.  The global rank at a block boundary is reconstructed from a sparse
wide superblock table plus a narrow per-block relative table; the local block
is still decoded through the charged sub-log code/length/class/shared-decoder
stores.
-/

namespace RMQ

namespace RankSelectSpec

def subLogRankSuperblockSpan (bits : List Bool) : Nat :=
  fixedWeightSubLogChunkBlockSize bits.length

theorem subLogRankSuperblockSpan_pos (bits : List Bool) :
    0 < subLogRankSuperblockSpan bits := by
  exact fixedWeightSubLogChunkBlockSize_pos bits.length

def subLogRankBlockStart (bits : List Bool) (blockIndex : Nat) : Nat :=
  Nat.min
    (blockIndex * fixedWeightSubLogChunkBlockSize bits.length)
    bits.length

def subLogRankBlockPrefix
    (bits : List Bool) (target : Bool) (blockIndex : Nat) : Nat :=
  Succinct.rankPrefix target bits
    (subLogRankBlockStart bits blockIndex)

def subLogRankSuperWidth (bits : List Bool) : Nat :=
  Nat.log2 bits.length + 1

def subLogRankRelativeWidth (bits : List Bool) : Nat :=
  2 * subLogClassWidth bits + 1

def subLogRankSuperEntryCount (bits : List Bool) : Nat :=
  (fixedWeightSubLogChunkBlocksWithSentinel bits).length /
      subLogRankSuperblockSpan bits + 1

def subLogRankSuperEntries
    (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (subLogRankSuperEntryCount bits)).map fun superIndex =>
    subLogRankBlockPrefix bits target
      (superIndex * subLogRankSuperblockSpan bits)

def subLogRankRelativeValue
    (bits : List Bool) (target : Bool) (blockIndex : Nat) : Nat :=
  SuccinctSpace.twoLevelRelative
    (subLogRankBlockPrefix bits target)
    (subLogRankSuperblockSpan bits)
    blockIndex

def subLogRankRelativeEntries
    (bits : List Bool) (target : Bool) : List Nat :=
  (List.range (fixedWeightSubLogChunkBlocksWithSentinel bits).length).map
    (subLogRankRelativeValue bits target)

def subLogRankSuperStore (bits : List Bool) (target : Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords (subLogRankSuperWidth bits)
          (subLogRankSuperEntries bits target)))
      (subLogRankSuperWidth bits) :=
  SuccinctSpace.fixedWidthTableStore (subLogRankSuperWidth bits)
    (subLogRankSuperEntries bits target)

def subLogRankRelativeStore (bits : List Bool) (target : Bool) :
    SuccinctSpace.BoundedPayloadWordStore
      (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords (subLogRankRelativeWidth bits)
          (subLogRankRelativeEntries bits target)))
      (subLogRankRelativeWidth bits) :=
  SuccinctSpace.fixedWidthTableStore (subLogRankRelativeWidth bits)
    (subLogRankRelativeEntries bits target)

theorem rankPrefix_sub_le_distance
    (target : Bool) (bits : List Bool) {lo hi : Nat}
    (hlo : lo <= hi) (hhi : hi <= bits.length) :
    Succinct.rankPrefix target bits hi -
        Succinct.rankPrefix target bits lo <= hi - lo := by
  have hdrop :=
    Succinct.rankPrefix_drop_eq_sub_of_le
      target bits hlo hhi
  rw [<- hdrop]
  exact Succinct.rankPrefix_le_limit target (bits.drop lo) (hi - lo)

theorem subLogRankBlockStart_mono
    (bits : List Bool) {a b : Nat} (hab : a <= b) :
    subLogRankBlockStart bits a <= subLogRankBlockStart bits b := by
  unfold subLogRankBlockStart
  have hmul :
      a * fixedWeightSubLogChunkBlockSize bits.length <=
        b * fixedWeightSubLogChunkBlockSize bits.length :=
    Nat.mul_le_mul_right _ hab
  change
    Nat.min (a * fixedWeightSubLogChunkBlockSize bits.length) bits.length <=
      Nat.min (b * fixedWeightSubLogChunkBlockSize bits.length) bits.length
  exact Nat.le_min.mpr
    (And.intro
      (Nat.le_trans (Nat.min_le_left _ bits.length) hmul)
      (Nat.min_le_right _ _))

theorem subLogRankBlockPrefix_mono
    (bits : List Bool) (target : Bool) {a b : Nat}
    (hab : a <= b) :
    subLogRankBlockPrefix bits target a <=
      subLogRankBlockPrefix bits target b := by
  unfold subLogRankBlockPrefix
  exact Succinct.rankPrefix_mono_limit target bits
    (subLogRankBlockStart_mono bits hab)

theorem subLogRankBlockStart_sub_le
    (bits : List Bool) {a b : Nat} (hab : a <= b) :
    subLogRankBlockStart bits b - subLogRankBlockStart bits a <=
      (b - a) * fixedWeightSubLogChunkBlockSize bits.length := by
  let step := fixedWeightSubLogChunkBlockSize bits.length
  have hmul : a * step <= b * step :=
    Nat.mul_le_mul_right step hab
  change
    Nat.min (b * step) bits.length -
        Nat.min (a * step) bits.length <=
      (b - a) * step
  by_cases hlen : bits.length <= a * step
  case pos =>
    have hminA : Nat.min (a * step) bits.length = bits.length :=
      Nat.min_eq_right hlen
    have hminB : Nat.min (b * step) bits.length = bits.length :=
      Nat.min_eq_right (Nat.le_trans hlen hmul)
    rw [hminA, hminB]
    simp
  case neg =>
    have hminA : Nat.min (a * step) bits.length = a * step :=
      Nat.min_eq_left (Nat.le_of_not_ge hlen)
    have hminB_le : Nat.min (b * step) bits.length <= b * step :=
      Nat.min_le_left _ _
    rw [hminA]
    have hsub := Nat.sub_le_sub_right hminB_le (a * step)
    have hrewrite :
        b * step - a * step = (b - a) * step := by
      exact (Nat.sub_mul b a step).symm
    simpa [hrewrite] using hsub

theorem subLogRankRelativeValue_le_span_square
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    subLogRankRelativeValue bits target blockIndex <=
      subLogRankSuperblockSpan bits * subLogRankSuperblockSpan bits := by
  let span := subLogRankSuperblockSpan bits
  let boundary := blockIndex / span * span
  have hboundary_le : boundary <= blockIndex :=
    SuccinctSpace.superblock_boundary_le span blockIndex
  have hstart_le :
      subLogRankBlockStart bits boundary <=
        subLogRankBlockStart bits blockIndex :=
    subLogRankBlockStart_mono bits hboundary_le
  have hprefix_le :
      subLogRankBlockPrefix bits target boundary <=
        subLogRankBlockPrefix bits target blockIndex :=
    subLogRankBlockPrefix_mono bits target hboundary_le
  have hsub_rank :
      subLogRankBlockPrefix bits target blockIndex -
          subLogRankBlockPrefix bits target boundary <=
        subLogRankBlockStart bits blockIndex -
          subLogRankBlockStart bits boundary := by
    unfold subLogRankBlockPrefix
    exact rankPrefix_sub_le_distance target bits hstart_le
      (by unfold subLogRankBlockStart; exact Nat.min_le_right _ _)
  have hsub_start :
      subLogRankBlockStart bits blockIndex -
          subLogRankBlockStart bits boundary <=
        (blockIndex - boundary) *
          fixedWeightSubLogChunkBlockSize bits.length :=
    subLogRankBlockStart_sub_le bits hboundary_le
  have hmod :
      blockIndex - boundary = blockIndex % span := by
    have hdecomp := SuccinctSpace.superblock_decompose span blockIndex
    unfold boundary
    omega
  have hmod_le :
      blockIndex % span <= span := by
    exact Nat.le_of_lt
      (SuccinctSpace.superblock_offset_lt span blockIndex
        (subLogRankSuperblockSpan_pos bits))
  unfold subLogRankRelativeValue SuccinctSpace.twoLevelRelative
  change
    subLogRankBlockPrefix bits target blockIndex -
        subLogRankBlockPrefix bits target boundary <=
      span * span
  calc
    subLogRankBlockPrefix bits target blockIndex -
        subLogRankBlockPrefix bits target boundary
        <= subLogRankBlockStart bits blockIndex -
            subLogRankBlockStart bits boundary := hsub_rank
    _ <= (blockIndex - boundary) *
        fixedWeightSubLogChunkBlockSize bits.length := hsub_start
    _ = (blockIndex % span) * span := by
      rw [hmod]
      rfl
    _ <= span * span := Nat.mul_le_mul_right span hmod_le

theorem subLogRankRelativeValue_lt_width
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    subLogRankRelativeValue bits target blockIndex <
      2 ^ subLogRankRelativeWidth bits := by
  let span := subLogRankSuperblockSpan bits
  have hrel := subLogRankRelativeValue_le_span_square
    bits target blockIndex
  have hspan_lt :
      span < 2 ^ subLogClassWidth bits := by
    simpa [span, subLogRankSuperblockSpan, subLogClassWidth] using
      fixedWeightSubLogChunkBlockSize_lt_classLengthFieldWidthPow
        bits.length
  have hspan_le : span <= 2 ^ subLogClassWidth bits :=
    Nat.le_of_lt hspan_lt
  have hsquare :
      span * span <=
        2 ^ subLogClassWidth bits * 2 ^ subLogClassWidth bits :=
    Nat.mul_le_mul hspan_le hspan_le
  have hpow_eq :
      2 ^ subLogClassWidth bits * 2 ^ subLogClassWidth bits =
        2 ^ (2 * subLogClassWidth bits) := by
    rw [<- Nat.pow_add]
    congr 1
    omega
  have hpow_lt :
      2 ^ (2 * subLogClassWidth bits) <
        2 ^ subLogRankRelativeWidth bits := by
    unfold subLogRankRelativeWidth
    have hpos : 0 < 2 ^ (2 * subLogClassWidth bits) :=
      Nat.pow_pos (by omega)
    rw [show 2 * subLogClassWidth bits + 1 =
      Nat.succ (2 * subLogClassWidth bits) by omega]
    rw [Nat.pow_succ]
    omega
  exact Nat.lt_of_le_of_lt
    (Nat.le_trans hrel (by simpa [hpow_eq] using hsquare))
    hpow_lt

theorem subLogRankBlockPrefix_lt_superWidth
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    subLogRankBlockPrefix bits target blockIndex <
      2 ^ subLogRankSuperWidth bits := by
  have hrank :
      subLogRankBlockPrefix bits target blockIndex <= bits.length := by
    unfold subLogRankBlockPrefix
    exact Nat.le_trans
      (Succinct.rankPrefix_le_limit target bits _)
      (by unfold subLogRankBlockStart; exact Nat.min_le_right _ _)
  have hlen : bits.length < 2 ^ subLogRankSuperWidth bits := by
    simpa [subLogRankSuperWidth] using
      (Nat.lt_log2_self (n := bits.length))
  exact Nat.lt_of_le_of_lt hrank hlen

theorem subLogRankSuperEntries_get?
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex < (fixedWeightSubLogChunkBlocksWithSentinel bits).length) :
    (subLogRankSuperEntries bits target)[
        blockIndex / subLogRankSuperblockSpan bits]? =
      some (subLogRankBlockPrefix bits target
        ((blockIndex / subLogRankSuperblockSpan bits) *
          subLogRankSuperblockSpan bits)) := by
  have hslot :
      blockIndex / subLogRankSuperblockSpan bits <
        subLogRankSuperEntryCount bits := by
    have hle :
        blockIndex / subLogRankSuperblockSpan bits <=
          (fixedWeightSubLogChunkBlocksWithSentinel bits).length /
            subLogRankSuperblockSpan bits :=
      Nat.div_le_div_right (Nat.le_of_lt hblockIndex)
    unfold subLogRankSuperEntryCount
    omega
  simp [subLogRankSuperEntries, List.getElem?_map,
    List.getElem?_range hslot]

theorem subLogRankRelativeEntries_get?
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex < (fixedWeightSubLogChunkBlocksWithSentinel bits).length) :
    (subLogRankRelativeEntries bits target)[blockIndex]? =
      some (subLogRankRelativeValue bits target blockIndex) := by
  simp [subLogRankRelativeEntries, List.getElem?_map,
    List.getElem?_range hblockIndex]

theorem subLogRankSuperStore_get?
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex < (fixedWeightSubLogChunkBlocksWithSentinel bits).length) :
    (subLogRankSuperStore bits target).store.words[
        blockIndex / subLogRankSuperblockSpan bits]? =
      some (SuccinctSpace.natToBitsLE (subLogRankSuperWidth bits)
        (subLogRankBlockPrefix bits target
          ((blockIndex / subLogRankSuperblockSpan bits) *
            subLogRankSuperblockSpan bits))) := by
  exact SuccinctSpace.fixedWidthTableStore_get? _ _
    (subLogRankSuperEntries_get? hblockIndex)

theorem subLogRankRelativeStore_get?
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex < (fixedWeightSubLogChunkBlocksWithSentinel bits).length) :
    (subLogRankRelativeStore bits target).store.words[blockIndex]? =
      some (SuccinctSpace.natToBitsLE (subLogRankRelativeWidth bits)
        (subLogRankRelativeValue bits target blockIndex)) := by
  exact SuccinctSpace.fixedWidthTableStore_get? _ _
    (subLogRankRelativeEntries_get? hblockIndex)

def subLogRankBaseCosted
    (bits : List Bool) (target : Bool) (blockIndex : Nat) : Costed Nat :=
  SuccinctSpace.twoLevelReadCosted2
    (subLogRankSuperStore bits target)
    (subLogRankRelativeStore bits target)
    (blockIndex / subLogRankSuperblockSpan bits)
    blockIndex

theorem subLogRankBaseCosted_cost
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    (subLogRankBaseCosted bits target blockIndex).cost = 2 := by
  simp [subLogRankBaseCosted,
    SuccinctSpace.twoLevelReadCosted2_cost]

theorem subLogRankBaseCosted_erase
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex < (fixedWeightSubLogChunkBlocksWithSentinel bits).length) :
    (subLogRankBaseCosted bits target blockIndex).erase =
      subLogRankBlockPrefix bits target blockIndex := by
  let boundary :=
    blockIndex / subLogRankSuperblockSpan bits *
      subLogRankSuperblockSpan bits
  have hsuper := subLogRankSuperStore_get?
    (bits := bits) (target := target) hblockIndex
  have hrel := subLogRankRelativeStore_get?
    (bits := bits) (target := target) hblockIndex
  have hbase_lt :
      subLogRankBlockPrefix bits target boundary <
        2 ^ subLogRankSuperWidth bits :=
    subLogRankBlockPrefix_lt_superWidth bits target boundary
  have hrel_lt :
      subLogRankRelativeValue bits target blockIndex <
        2 ^ subLogRankRelativeWidth bits :=
    subLogRankRelativeValue_lt_width bits target blockIndex
  have hread :=
    SuccinctSpace.twoLevelReadCosted2_erase_eq
      (subLogRankSuperStore bits target)
      (subLogRankRelativeStore bits target)
      (blockIndex / subLogRankSuperblockSpan bits)
      blockIndex
      (subLogRankSuperWidth bits)
      (subLogRankRelativeWidth bits)
      (subLogRankBlockPrefix bits target boundary)
      (subLogRankRelativeValue bits target blockIndex)
      (by simpa [boundary] using hsuper)
      hrel hbase_lt hrel_lt
  have hboundary_le : boundary <= blockIndex := by
    simpa [boundary] using
      SuccinctSpace.superblock_boundary_le
        (subLogRankSuperblockSpan bits) blockIndex
  have hprefix_le :
      subLogRankBlockPrefix bits target boundary <=
        subLogRankBlockPrefix bits target blockIndex :=
    subLogRankBlockPrefix_mono bits target hboundary_le
  unfold subLogRankBaseCosted
  rw [hread]
  exact SuccinctSpace.twoLevelRelative_add
    (subLogRankBlockPrefix bits target)
    (subLogRankSuperblockSpan bits)
    blockIndex
    hprefix_le

theorem fixedWeightChunkBlocks_length_mul_blockSize_cover
    {blockSize : Nat} (hblockSize : 0 < blockSize) (bits : List Bool) :
    bits.length <=
      (fixedWeightChunkBlocks blockSize bits).length * blockSize := by
  by_cases hcover :
      bits.length <=
        (fixedWeightChunkBlocks blockSize bits).length * blockSize
  case pos =>
    exact hcover
  case neg =>
    have hlt :
        (fixedWeightChunkBlocks blockSize bits).length * blockSize <
          bits.length := Nat.lt_of_not_ge hcover
    have hsome :=
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (wordSize := blockSize) hblockSize
        (payload := bits)
        (i := (fixedWeightChunkBlocks blockSize bits).length)
        (by simpa [fixedWeightChunkBlocks] using hlt)
    cases hsome with
    | intro block hblock =>
        have hnone :
            (fixedWeightChunkBlocks blockSize bits)[
                (fixedWeightChunkBlocks blockSize bits).length]? = none := by
          simp
        simp [fixedWeightChunkBlocks] at hblock

def subLogRankBlockIndex (bits : List Bool) (pos : Nat) : Nat :=
  if pos < bits.length then
    pos / fixedWeightSubLogChunkBlockSize bits.length
  else
    (fixedWeightSubLogChunkBlocks bits).length

def subLogRankLocalLimit (bits : List Bool) (pos : Nat) : Nat :=
  if pos < bits.length then
    pos -
      (pos / fixedWeightSubLogChunkBlockSize bits.length) *
        fixedWeightSubLogChunkBlockSize bits.length
  else
    0

def subLogRankBlock (bits : List Bool) (pos : Nat) : List Bool :=
  ((fixedWeightSubLogChunkBlocksWithSentinel bits)[
      subLogRankBlockIndex bits pos]?).getD []

theorem subLogRankBlock_get?
    (bits : List Bool) (pos : Nat) :
    (fixedWeightSubLogChunkBlocksWithSentinel bits)[
        subLogRankBlockIndex bits pos]? =
      some (subLogRankBlock bits pos) := by
  by_cases hpos : pos < bits.length
  case pos =>
    have hstart_lt :
        (pos / fixedWeightSubLogChunkBlockSize bits.length) *
            fixedWeightSubLogChunkBlockSize bits.length < bits.length := by
      have hstart_le :
          (pos / fixedWeightSubLogChunkBlockSize bits.length) *
              fixedWeightSubLogChunkBlockSize bits.length <= pos :=
        Nat.div_mul_le_self pos
          (fixedWeightSubLogChunkBlockSize bits.length)
      omega
    have hsome :=
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (wordSize := fixedWeightSubLogChunkBlockSize bits.length)
        (fixedWeightSubLogChunkBlockSize_pos bits.length)
        (payload := bits)
        (i := pos / fixedWeightSubLogChunkBlockSize bits.length)
        (by simpa [fixedWeightChunkBlocks] using hstart_lt)
    cases hsome with
    | intro block hchunkRaw =>
        have hchunk :
            (fixedWeightSubLogChunkBlocks bits)[
                pos / fixedWeightSubLogChunkBlockSize bits.length]? =
              some block := by
          simpa [fixedWeightSubLogChunkBlocks] using hchunkRaw
        have hsent :
            (fixedWeightSubLogChunkBlocksWithSentinel bits)[
                pos / fixedWeightSubLogChunkBlockSize bits.length]? =
              some block := by
          simpa [fixedWeightSubLogChunkBlocks,
            fixedWeightSubLogChunkBlocksWithSentinel] using
            fixedWeightChunkBlocksWithSentinel_get_chunk hchunk
        simp [subLogRankBlock, subLogRankBlockIndex, hpos, hsent]
  case neg =>
    have hsent :
        (fixedWeightSubLogChunkBlocksWithSentinel bits)[
            (fixedWeightSubLogChunkBlocks bits).length]? = some [] := by
      simpa [fixedWeightSubLogChunkBlocks,
        fixedWeightSubLogChunkBlocksWithSentinel] using
        fixedWeightChunkBlocksWithSentinel_get_sentinel
          (fixedWeightSubLogChunkBlockSize bits.length) bits
    simp [subLogRankBlock, subLogRankBlockIndex, hpos, hsent]

theorem subLogRankBlockPrefix_add_local_exact
    (bits : List Bool) (target : Bool) (pos : Nat) :
    subLogRankBlockPrefix bits target (subLogRankBlockIndex bits pos) +
        Succinct.rankPrefix target
          (subLogRankBlock bits pos)
          (subLogRankLocalLimit bits pos) =
      Succinct.rankPrefix target bits pos := by
  by_cases hpos : pos < bits.length
  case pos =>
    have hstart_lt :
        (pos / fixedWeightSubLogChunkBlockSize bits.length) *
            fixedWeightSubLogChunkBlockSize bits.length < bits.length := by
      have hstart_le :
          (pos / fixedWeightSubLogChunkBlockSize bits.length) *
              fixedWeightSubLogChunkBlockSize bits.length <= pos :=
        Nat.div_mul_le_self pos
          (fixedWeightSubLogChunkBlockSize bits.length)
      omega
    have hstart_le_len :
        (pos / fixedWeightSubLogChunkBlockSize bits.length) *
            fixedWeightSubLogChunkBlockSize bits.length <= bits.length :=
      Nat.le_of_lt hstart_lt
    have hsome :=
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        (wordSize := fixedWeightSubLogChunkBlockSize bits.length)
        (fixedWeightSubLogChunkBlockSize_pos bits.length)
        (payload := bits)
        (i := pos / fixedWeightSubLogChunkBlockSize bits.length)
        (by simpa [fixedWeightChunkBlocks] using hstart_lt)
    cases hsome with
    | intro block hchunkRaw =>
        have hchunk :
            (fixedWeightSubLogChunkBlocks bits)[
                pos / fixedWeightSubLogChunkBlockSize bits.length]? =
              some block := by
          simpa [fixedWeightSubLogChunkBlocks] using hchunkRaw
        have hsent :
            (fixedWeightSubLogChunkBlocksWithSentinel bits)[
                pos / fixedWeightSubLogChunkBlockSize bits.length]? =
              some block := by
          simpa [fixedWeightSubLogChunkBlocks,
            fixedWeightSubLogChunkBlocksWithSentinel] using
            fixedWeightChunkBlocksWithSentinel_get_chunk hchunk
        have hblock_eq :
            subLogRankBlock bits pos = block := by
          simp [subLogRankBlock, subLogRankBlockIndex, hpos, hsent]
        have hexact :=
          fixedWeightChunkBlocks_get?_rankPrefix_add_exact
            (blockSize := fixedWeightSubLogChunkBlockSize bits.length)
            (target := target)
            (fixedWeightSubLogChunkBlockSize_pos bits.length)
            (bits := bits)
            (block := block)
            (pos := pos)
            (Nat.le_of_lt hpos)
            (by
              simpa [fixedWeightSubLogChunkBlocks] using hchunk)
        simpa [subLogRankBlockIndex, subLogRankLocalLimit,
          subLogRankBlockPrefix, subLogRankBlockStart, hpos,
          Nat.min_eq_left hstart_le_len, hblock_eq] using hexact
  case neg =>
    have hlen : bits.length <= pos := Nat.le_of_not_gt hpos
    have hcover :
        bits.length <=
          (fixedWeightChunkBlocks
            (fixedWeightSubLogChunkBlockSize bits.length) bits).length *
            fixedWeightSubLogChunkBlockSize bits.length :=
      fixedWeightChunkBlocks_length_mul_blockSize_cover
        (fixedWeightSubLogChunkBlockSize_pos bits.length) bits
    have hsent :
        (fixedWeightSubLogChunkBlocksWithSentinel bits)[
            (fixedWeightSubLogChunkBlocks bits).length]? = some [] := by
      simpa [fixedWeightSubLogChunkBlocks,
        fixedWeightSubLogChunkBlocksWithSentinel] using
        fixedWeightChunkBlocksWithSentinel_get_sentinel
          (fixedWeightSubLogChunkBlockSize bits.length) bits
    have hrank :=
      Succinct.rankPrefix_eq_rankPrefix_length_of_length_le
        target bits hlen
    have hstart :
        subLogRankBlockStart bits (subLogRankBlockIndex bits pos) =
          bits.length := by
      simpa [subLogRankBlockStart, subLogRankBlockIndex,
        fixedWeightSubLogChunkBlocks, hpos] using
        Nat.min_eq_right hcover
    have hprefix :
        subLogRankBlockPrefix bits target (subLogRankBlockIndex bits pos) =
          Succinct.rankPrefix target bits bits.length := by
      simp [subLogRankBlockPrefix, hstart]
    have hprefix' :
        subLogRankBlockPrefix bits target
            (fixedWeightSubLogChunkBlocks bits).length =
          Succinct.rankPrefix target bits bits.length := by
      simpa [subLogRankBlockIndex, hpos] using hprefix
    calc
      subLogRankBlockPrefix bits target (subLogRankBlockIndex bits pos) +
          Succinct.rankPrefix target (subLogRankBlock bits pos)
            (subLogRankLocalLimit bits pos)
          = Succinct.rankPrefix target bits bits.length := by
            simp [hprefix', subLogRankBlock, subLogRankBlockIndex,
              subLogRankLocalLimit, hpos, hsent, Succinct.rankPrefix]
      _ = Succinct.rankPrefix target bits pos := hrank.symm

def subLogRankCosted
    (bits : List Bool) (target : Bool) (pos : Nat) : Costed Nat :=
  let blockIndex := subLogRankBlockIndex bits pos
  Costed.bind (subLogRankBaseCosted bits target blockIndex) fun base =>
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
    Costed.pure
      (base +
        Succinct.rankPrefix target (decoded?.getD [])
          (subLogRankLocalLimit bits pos))

theorem subLogRankCosted_cost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankCosted bits target pos).cost = 6 := by
  simp [subLogRankCosted, subLogRankBaseCosted,
    SuccinctSpace.twoLevelReadCosted2, subLogDecodeReadCosted]

theorem subLogRankCosted_erase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  let blockIndex := subLogRankBlockIndex bits pos
  let block := subLogRankBlock bits pos
  have hblock : (fixedWeightSubLogChunkBlocksWithSentinel bits)[
        blockIndex]? = some block := by
    simpa [blockIndex, block] using subLogRankBlock_get? bits pos
  have hidx :
      blockIndex <
        (fixedWeightSubLogChunkBlocksWithSentinel bits).length :=
    (List.getElem?_eq_some_iff.mp hblock).1
  have hmem :
      List.Mem block
        (fixedWeightSubLogChunkBlocksWithSentinel bits) :=
    List.mem_of_getElem? hblock
  have hbase :=
    subLogRankBaseCosted_erase
      (bits := bits) (target := target) hidx
  have hcode := subLogCodeStore_get? hblock
  have hlen := subLogLenStore_get? hblock
  have hclass := subLogClassStore_get? hblock
  have hlenlt := subLogBlock_length_lt hmem
  have hclasslt := subLogBlock_trueCount_lt hmem
  simp only [subLogRankCosted, Costed.erase_bind, Costed.erase_pure,
    subLogDecodeReadCosted, SuccinctSpace.PayloadWordStore.readWordCosted_erase]
  rw [hbase, hcode, hlen, hclass,
    fixedWeightSharedDecodeSlotFromReadValues_encoded_prefix [] hlenlt hclasslt,
    fixedWeightSubLogSharedDecoderStore_get?_of_block hblock]
  simp only [Option.getD_some]
  exact subLogRankBlockPrefix_add_local_exact bits target pos

def fixedWeightSubLogRankRoutePayload
    (bits : List Bool) (target : Bool) : List Bool :=
  SuccinctSpace.flattenPayloadWords
      (SuccinctSpace.fixedWidthTableWords (subLogRankSuperWidth bits)
        (subLogRankSuperEntries bits target)) ++
    SuccinctSpace.flattenPayloadWords
      (SuccinctSpace.fixedWidthTableWords (subLogRankRelativeWidth bits)
        (subLogRankRelativeEntries bits target))

def fixedWeightSubLogRankRouteOverhead : Nat -> Nat := fun n =>
  8 * (fixedWeightSubLogChunkBlockCountBoundWithSentinel n +
      fixedWeightSubLogChunkBlockSize n) +
    (fixedWeightSubLogChunkClassLengthOverhead n +
      fixedWeightSubLogChunkBlockCountBoundWithSentinel n)

theorem fixedWidthTablePayload_length_eq
    (width : Nat) (entries : List Nat) :
    (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords width entries)).length =
      entries.length * width := by
  calc
    (SuccinctSpace.flattenPayloadWords
        (SuccinctSpace.fixedWidthTableWords width entries)).length =
        (SuccinctSpace.fixedWidthTableWords width entries).length * width := by
          apply SuccinctSpace.flattenPayloadWords_length_of_forall_length
          intro word hmem
          cases List.mem_map.mp hmem with
          | intro entry hrest =>
              cases hrest with
              | intro _ hword =>
                  rw [<- hword]
                  exact SuccinctSpace.natToBitsLE_length width entry
    _ = entries.length * width := by
          simp [SuccinctSpace.fixedWidthTableWords]

theorem subLogRankSuperEntries_length
    (bits : List Bool) (target : Bool) :
    (subLogRankSuperEntries bits target).length =
      subLogRankSuperEntryCount bits := by
  simp [subLogRankSuperEntries]

theorem subLogRankRelativeEntries_length
    (bits : List Bool) (target : Bool) :
    (subLogRankRelativeEntries bits target).length =
      (fixedWeightSubLogChunkBlocksWithSentinel bits).length := by
  simp [subLogRankRelativeEntries]

theorem subLogRankSuperWidth_le_eight_span (n : Nat) :
    Nat.log2 n + 1 <= 8 * fixedWeightSubLogChunkBlockSize n := by
  unfold fixedWeightSubLogChunkBlockSize
  omega

theorem fixedWeightSubLogChunkBlockSize_littleO :
    SuccinctSpace.LittleOLinear fixedWeightSubLogChunkBlockSize := by
  have hlog :
      SuccinctSpace.LittleOLinear
        (fun n => Nat.log2 n + 1) := by
    intro scale hscale
    exact SuccinctSpace.eventually_scale_log2_succ_le_self scale
  apply SuccinctSpace.LittleOLinear.of_le hlog
  intro n
  unfold fixedWeightSubLogChunkBlockSize
  omega

theorem fixedWeightSubLogRankRoutePayload_length_le
    (bits : List Bool) (target : Bool) :
    (fixedWeightSubLogRankRoutePayload bits target).length <=
      fixedWeightSubLogRankRouteOverhead bits.length := by
  let blockCount :=
    (fixedWeightSubLogChunkBlocksWithSentinel bits).length
  let span := fixedWeightSubLogChunkBlockSize bits.length
  let bound :=
    fixedWeightSubLogChunkBlockCountBoundWithSentinel bits.length
  let classWidth :=
    fixedWeightSubLogChunkClassLengthFieldWidthBound bits.length
  have hcount : blockCount <= bound := by
    simpa [blockCount, bound] using
      fixedWeightSubLogChunkBlocksWithSentinel_length_le bits
  have hsuperLen :
      (SuccinctSpace.flattenPayloadWords
          (SuccinctSpace.fixedWidthTableWords
            (subLogRankSuperWidth bits)
            (subLogRankSuperEntries bits target))).length <=
        8 * (bound + span) := by
    rw [fixedWidthTablePayload_length_eq]
    rw [subLogRankSuperEntries_length]
    have hwidth : subLogRankSuperWidth bits <= 8 * span := by
      simpa [subLogRankSuperWidth, span] using
        subLogRankSuperWidth_le_eight_span bits.length
    have hentries :
        subLogRankSuperEntryCount bits =
          blockCount / span + 1 := by
      simp [subLogRankSuperEntryCount, blockCount, span,
        subLogRankSuperblockSpan]
    rw [hentries]
    have hmul :
        (blockCount / span) * span <= blockCount :=
      Nat.div_mul_le_self blockCount span
    calc
      (blockCount / span + 1) * subLogRankSuperWidth bits
          <= (blockCount / span + 1) * (8 * span) :=
            Nat.mul_le_mul_left _ hwidth
      _ = 8 * ((blockCount / span) * span + span) := by
            rw [Nat.add_mul, Nat.one_mul, Nat.mul_add]
            simp [Nat.mul_assoc, Nat.mul_comm]
      _ <= 8 * (blockCount + span) := by
            exact Nat.mul_le_mul_left 8 (Nat.add_le_add_right hmul span)
      _ <= 8 * (bound + span) := by
            exact Nat.mul_le_mul_left 8 (Nat.add_le_add_right hcount span)
  have hrelLen :
      (SuccinctSpace.flattenPayloadWords
          (SuccinctSpace.fixedWidthTableWords
            (subLogRankRelativeWidth bits)
            (subLogRankRelativeEntries bits target))).length <=
        fixedWeightSubLogChunkClassLengthOverhead bits.length + bound := by
    rw [fixedWidthTablePayload_length_eq]
    rw [subLogRankRelativeEntries_length]
    have hclass :
        subLogClassWidth bits = classWidth := by
      rfl
    have hrelWidth :
        subLogRankRelativeWidth bits = 2 * classWidth + 1 := by
      simp [subLogRankRelativeWidth, hclass]
    rw [hrelWidth]
    have hmul :
        blockCount * (2 * classWidth + 1) <=
          bound * (2 * classWidth + 1) :=
      Nat.mul_le_mul_right _ hcount
    have hbound :
        bound * (2 * classWidth + 1) <=
          fixedWeightSubLogChunkClassLengthOverhead bits.length + bound := by
      unfold fixedWeightSubLogChunkClassLengthOverhead
        fixedWeightBlockClassLengthTableOverheadBudget
      change
        bound * (2 * classWidth + 1) <=
          (bound + bound) * classWidth + 4 * classWidth + bound
      have hmul :
          bound * (2 * classWidth + 1) =
            (bound + bound) * classWidth + bound := by
        rw [Nat.mul_add, Nat.mul_one]
        congr 1
        rw [<- Nat.mul_assoc]
        have htwo : bound * 2 = bound + bound := by omega
        rw [htwo]
      rw [hmul]
      omega
    calc
      blockCount * (2 * classWidth + 1)
          <= bound * (2 * classWidth + 1) := hmul
      _ <= fixedWeightSubLogChunkClassLengthOverhead bits.length + bound :=
            hbound
  simpa [fixedWeightSubLogRankRoutePayload,
    fixedWeightSubLogRankRouteOverhead, List.length_append, bound, span]
    using Nat.add_le_add hsuperLen hrelLen

theorem fixedWeightSubLogRankRouteOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogRankRouteOverhead := by
  have hsuper :
      SuccinctSpace.LittleOLinear
        (fun n =>
          8 * (fixedWeightSubLogChunkBlockCountBoundWithSentinel n +
            fixedWeightSubLogChunkBlockSize n)) :=
    (fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO.add
        fixedWeightSubLogChunkBlockSize_littleO).mul_left 8
  have hrel :
      SuccinctSpace.LittleOLinear
        (fun n =>
          fixedWeightSubLogChunkClassLengthOverhead n +
            fixedWeightSubLogChunkBlockCountBoundWithSentinel n) :=
    fixedWeightSubLogChunkClassLengthOverhead_littleO.add
      fixedWeightSubLogChunkBlockCountBoundWithSentinel_littleO
  simpa [fixedWeightSubLogRankRouteOverhead, Nat.add_assoc] using
    hsuper.add hrel

theorem fixedWeightSubLogRankRouteProfile
    (bits : List Bool) (target : Bool) :
    (fixedWeightSubLogRankRoutePayload bits target).length <=
        fixedWeightSubLogRankRouteOverhead bits.length /\
      SuccinctSpace.LittleOLinear fixedWeightSubLogRankRouteOverhead /\
      (forall pos,
        (subLogRankCosted bits target pos).cost = 6 /\
          (subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall {word : List Bool},
        List.Mem word
            (subLogRankSuperStore bits target).store.words.toList ->
          word.length <= subLogRankSuperWidth bits) /\
      forall {word : List Bool},
        List.Mem word
            (subLogRankRelativeStore bits target).store.words.toList ->
          word.length <= subLogRankRelativeWidth bits := by
  exact And.intro
    (fixedWeightSubLogRankRoutePayload_length_le bits target)
    (And.intro fixedWeightSubLogRankRouteOverhead_littleO
      (And.intro
        (fun pos =>
          And.intro (subLogRankCosted_cost bits target pos)
            (subLogRankCosted_erase bits target pos))
        (And.intro
          (subLogRankSuperStore bits target).word_length_le
          (subLogRankRelativeStore bits target).word_length_le)))

def fixedWeightSubLogConcreteRankPayload
    (bits : List Bool) : List Bool :=
  (fixedWeightSubLogConcretePayload bits ++
      fixedWeightSubLogRankRoutePayload bits true) ++
    fixedWeightSubLogRankRoutePayload bits false

def fixedWeightSubLogConcreteRankOverhead : Nat -> Nat := fun n =>
  fixedWeightSubLogConcreteRouteDecoderOverhead n +
    (fixedWeightSubLogRankRouteOverhead n +
      fixedWeightSubLogRankRouteOverhead n)

theorem fixedWeightSubLogConcreteRankPayload_length_le
    (bits : List Bool) :
    (fixedWeightSubLogConcreteRankPayload bits).length <=
      fixedWeightPayloadBudget bits +
        fixedWeightSubLogConcreteRankOverhead bits.length := by
  have hbase := fixedWeightSubLogConcretePayload_length_le bits
  have htrue := fixedWeightSubLogRankRoutePayload_length_le bits true
  have hfalse := fixedWeightSubLogRankRoutePayload_length_le bits false
  simp [fixedWeightSubLogConcreteRankPayload,
    fixedWeightSubLogConcreteRankOverhead, List.length_append]
  omega

theorem fixedWeightSubLogConcreteRankOverhead_littleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogConcreteRankOverhead := by
  simpa [fixedWeightSubLogConcreteRankOverhead, Nat.add_assoc] using
    fixedWeightSubLogConcreteRouteDecoderOverhead_littleO.add
      (fixedWeightSubLogRankRouteOverhead_littleO.add
        fixedWeightSubLogRankRouteOverhead_littleO)

theorem fixedWeightSubLogConcreteRankAccessRankProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcreteRankPayload bits).length <=
        fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcreteRankOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcreteRankOverhead /\
      (forall i,
        (subLogAccessCosted bits i).cost <= 6 /\
          (subLogAccessCosted bits i).erase = bits[i]?) /\
      forall target pos,
        (subLogRankCosted bits target pos).cost <= 6 /\
          (subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos := by
  exact And.intro
    (fixedWeightSubLogConcreteRankPayload_length_le bits)
    (And.intro fixedWeightSubLogConcreteRankOverhead_littleO
      (And.intro
        (fun i => And.intro
          (by
            rw [subLogAccessCosted_cost]
            omega)
          (subLogAccessCosted_erase bits i))
        (fun target pos => And.intro
          (by
            rw [subLogRankCosted_cost]
            omega)
          (subLogRankCosted_erase bits target pos))))

end RankSelectSpec

namespace RankSelect

abbrev subLogRankBaseCosted :=
  RMQ.RankSelectSpec.subLogRankBaseCosted

theorem subLogRankBaseCostedCost
    (bits : List Bool) (target : Bool) (blockIndex : Nat) :
    (subLogRankBaseCosted bits target blockIndex).cost = 2 := by
  exact
    RMQ.RankSelectSpec.subLogRankBaseCosted_cost
      bits target blockIndex

theorem subLogRankBaseCostedErase
    {bits : List Bool} {target : Bool} {blockIndex : Nat}
    (hblockIndex :
      blockIndex <
        (RMQ.RankSelectSpec.fixedWeightSubLogChunkBlocksWithSentinel
          bits).length) :
    (subLogRankBaseCosted bits target blockIndex).erase =
      RMQ.RankSelectSpec.subLogRankBlockPrefix bits target blockIndex := by
  exact
    RMQ.RankSelectSpec.subLogRankBaseCosted_erase hblockIndex

abbrev subLogRankCosted :=
  RMQ.RankSelectSpec.subLogRankCosted

theorem subLogRankCostedCost
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankCosted bits target pos).cost = 6 := by
  exact RMQ.RankSelectSpec.subLogRankCosted_cost bits target pos

theorem subLogRankCostedErase
    (bits : List Bool) (target : Bool) (pos : Nat) :
    (subLogRankCosted bits target pos).erase =
      Succinct.rankPrefix target bits pos := by
  exact RMQ.RankSelectSpec.subLogRankCosted_erase bits target pos

abbrev fixedWeightSubLogRankRoutePayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogRankRoutePayload

abbrev fixedWeightSubLogRankRouteOverhead :=
  RMQ.RankSelectSpec.fixedWeightSubLogRankRouteOverhead

theorem fixedWeightSubLogRankRoutePayloadLengthLe
    (bits : List Bool) (target : Bool) :
    (fixedWeightSubLogRankRoutePayload bits target).length <=
      fixedWeightSubLogRankRouteOverhead bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogRankRoutePayload_length_le
      bits target

theorem fixedWeightSubLogRankRouteOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogRankRouteOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogRankRouteOverhead_littleO

theorem fixedWeightSubLogRankRouteProfile
    (bits : List Bool) (target : Bool) :
    (fixedWeightSubLogRankRoutePayload bits target).length <=
        fixedWeightSubLogRankRouteOverhead bits.length /\
      SuccinctSpace.LittleOLinear fixedWeightSubLogRankRouteOverhead /\
      (forall pos,
        (subLogRankCosted bits target pos).cost = 6 /\
          (subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos) /\
      (forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.subLogRankSuperStore
              bits target).store.words.toList ->
          word.length <=
            RMQ.RankSelectSpec.subLogRankSuperWidth bits) /\
      forall {word : List Bool},
        List.Mem word
            (RMQ.RankSelectSpec.subLogRankRelativeStore
              bits target).store.words.toList ->
          word.length <=
            RMQ.RankSelectSpec.subLogRankRelativeWidth bits := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogRankRouteProfile bits target

abbrev fixedWeightSubLogConcreteRankPayload :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteRankPayload

abbrev fixedWeightSubLogConcreteRankOverhead :=
  RMQ.RankSelectSpec.fixedWeightSubLogConcreteRankOverhead

theorem fixedWeightSubLogConcreteRankPayloadLengthLe
    (bits : List Bool) :
    (fixedWeightSubLogConcreteRankPayload bits).length <=
      RMQ.RankSelectSpec.fixedWeightPayloadBudget bits +
        fixedWeightSubLogConcreteRankOverhead bits.length := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcreteRankPayload_length_le bits

theorem fixedWeightSubLogConcreteRankOverheadLittleO :
    SuccinctSpace.LittleOLinear
      fixedWeightSubLogConcreteRankOverhead := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcreteRankOverhead_littleO

theorem fixedWeightSubLogConcreteRankAccessRankProfile
    (bits : List Bool) :
    (fixedWeightSubLogConcreteRankPayload bits).length <=
        RMQ.RankSelectSpec.fixedWeightPayloadBudget bits +
          fixedWeightSubLogConcreteRankOverhead bits.length /\
      SuccinctSpace.LittleOLinear
        fixedWeightSubLogConcreteRankOverhead /\
      (forall i,
        (RMQ.RankSelectSpec.subLogAccessCosted bits i).cost <= 6 /\
          (RMQ.RankSelectSpec.subLogAccessCosted bits i).erase = bits[i]?) /\
      forall target pos,
        (subLogRankCosted bits target pos).cost <= 6 /\
          (subLogRankCosted bits target pos).erase =
            Succinct.rankPrefix target bits pos := by
  exact
    RMQ.RankSelectSpec.fixedWeightSubLogConcreteRankAccessRankProfile bits

end RankSelect

end RMQ
