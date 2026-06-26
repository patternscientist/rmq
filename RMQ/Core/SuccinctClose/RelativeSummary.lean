import RMQ.Core.SuccinctClose.RangeSummary

/-!
# Relative BP block summaries

Relative min/max/argmin BP summary tables, canonical parameter arithmetic, and
interior-directory budget setup. The historical `RMQ.SuccinctCloseProposal`
namespace is preserved so theorem names remain stable.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace
/-!
## Relative BP block summaries

The absolute min/max summaries above are intentionally too wide for the final
word-RAM profile: storing a `Theta(log n)` excess value for every block costs
too much.  The relative layer below stores sparse absolute superblock
baselines, then encodes each block's min/max excess as a shifted delta inside
the superblock span.  The block-local argmin is stored as a local offset.
-/

theorem rankPrefix_le_rankPrefix_add_distance
    (target : Bool) (bits : List Bool) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= bits.length) :
    Succinct.rankPrefix target bits hi <=
      Succinct.rankPrefix target bits lo + (hi - lo) := by
  have hdrop :=
    Succinct.rankPrefix_drop_eq_sub_of_le
      target bits hlohi hhi
  have htail :=
    Succinct.rankPrefix_le_limit target (bits.drop lo) (hi - lo)
  have hmono := Succinct.rankPrefix_mono_limit target bits hlohi
  omega

theorem bpExcessAt_le_bpExcessAt_add_distance_right
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= shape.bpCode.length) :
    bpExcessAt shape hi <= bpExcessAt shape lo + (hi - lo) := by
  unfold bpExcessAt
  have hopen :=
    rankPrefix_le_rankPrefix_add_distance
      true shape.bpCode hlohi hhi
  have hcloseMono :=
    Succinct.rankPrefix_mono_limit false shape.bpCode hlohi
  have hloLen : lo <= shape.bpCode.length := Nat.le_trans hlohi hhi
  have hnonneg := bpExcessAt_prefix_nonnegative shape hloLen
  have hsubMono :
      Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode hi <=
        Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode lo :=
    Nat.sub_le_sub_left hcloseMono
      (Succinct.rankPrefix true shape.bpCode hi)
  omega

theorem bpExcessAt_le_bpExcessAt_add_distance_left
    (shape : Cartesian.CartesianShape) {lo hi : Nat}
    (hlohi : lo <= hi) (hhi : hi <= shape.bpCode.length) :
    bpExcessAt shape lo <= bpExcessAt shape hi + (hi - lo) := by
  unfold bpExcessAt
  have hopenMono :=
    Succinct.rankPrefix_mono_limit true shape.bpCode hlohi
  have hclose :=
    rankPrefix_le_rankPrefix_add_distance
      false shape.bpCode hlohi hhi
  have hloLen : lo <= shape.bpCode.length := Nat.le_trans hlohi hhi
  have hhiNonneg := bpExcessAt_prefix_nonnegative shape hhi
  have hsubMono :
      Succinct.rankPrefix true shape.bpCode lo -
          Succinct.rankPrefix false shape.bpCode lo <=
        Succinct.rankPrefix true shape.bpCode hi -
          Succinct.rankPrefix false shape.bpCode lo :=
    Nat.sub_le_sub_right hopenMono
      (Succinct.rankPrefix false shape.bpCode lo)
  omega

def bpSuperblockStartBlock (blocksPerSuper block : Nat) : Nat :=
  (block / blocksPerSuper) * blocksPerSuper

def bpSuperblockSpan (blockSize blocksPerSuper : Nat) : Nat :=
  blocksPerSuper * blockSize

def bpSuperblockStartPos
    (blockSize blocksPerSuper block : Nat) : Nat :=
  blockStartOf blockSize (bpSuperblockStartBlock blocksPerSuper block)

theorem bpSuperblockStartBlock_le
    {blocksPerSuper block : Nat} :
    bpSuperblockStartBlock blocksPerSuper block <= block := by
  unfold bpSuperblockStartBlock
  by_cases hzero : blocksPerSuper = 0
  · simp [hzero]
  · exact Nat.div_mul_le_self block blocksPerSuper

theorem block_lt_bpSuperblockStartBlock_add_blocksPerSuper
    {blocksPerSuper block : Nat} (hblocks : 0 < blocksPerSuper) :
    block < bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper := by
  unfold bpSuperblockStartBlock
  have h := (Nat.div_add_mod block blocksPerSuper).symm
  have hmod := Nat.mod_lt block hblocks
  calc
    block = blocksPerSuper * (block / blocksPerSuper) +
        block % blocksPerSuper := h
    _ = (block / blocksPerSuper) * blocksPerSuper +
        block % blocksPerSuper := by rw [Nat.mul_comm]
    _ < (block / blocksPerSuper) * blocksPerSuper +
        blocksPerSuper := Nat.add_lt_add_left hmod _

theorem blockStart_add_offset_le_blockCount_mul
    {blockSize blockCount block offset : Nat}
    (hblock : block < blockCount) (hoffset : offset <= blockSize) :
    blockStartOf blockSize block + offset <= blockCount * blockSize := by
  unfold blockStartOf
  have hsucc : block + 1 <= blockCount := by omega
  have hmul := Nat.mul_le_mul_right blockSize hsucc
  have hleft :
      block * blockSize + offset <= (block + 1) * blockSize := by
    have hsuccMul :
        (block + 1) * blockSize = block * blockSize + blockSize := by
      rw [Nat.add_mul]
      simp
    rw [hsuccMul]
    exact Nat.add_le_add_left hoffset (block * blockSize)
  exact Nat.le_trans hleft hmul

theorem bpSuperblockStartPos_le_blockStart_add_offset
    {blockSize blocksPerSuper block offset : Nat} :
    bpSuperblockStartPos blockSize blocksPerSuper block <=
      blockStartOf blockSize block + offset := by
  unfold bpSuperblockStartPos blockStartOf
  have hblock := bpSuperblockStartBlock_le
      (blocksPerSuper := blocksPerSuper) (block := block)
  have hmul := Nat.mul_le_mul_right blockSize hblock
  omega

theorem blockStart_add_offset_le_bpSuperblockEnd
    {blockSize blocksPerSuper block offset : Nat}
    (hblocks : 0 < blocksPerSuper) (hoffset : offset <= blockSize) :
    blockStartOf blockSize block + offset <=
      bpSuperblockStartPos blockSize blocksPerSuper block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpSuperblockStartPos bpSuperblockSpan blockStartOf
  have hblock :
      block + 1 <=
        bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper := by
    have hlt :=
      block_lt_bpSuperblockStartBlock_add_blocksPerSuper
        (block := block) hblocks
    omega
  have hmul := Nat.mul_le_mul_right blockSize hblock
  have hleft :
      block * blockSize + offset <= (block + 1) * blockSize := by
    have hsuccMul :
        (block + 1) * blockSize = block * blockSize + blockSize := by
      rw [Nat.add_mul]
      simp
    rw [hsuccMul]
    exact Nat.add_le_add_left hoffset (block * blockSize)
  have hend :
      (bpSuperblockStartBlock blocksPerSuper block + blocksPerSuper) *
          blockSize =
        bpSuperblockStartBlock blocksPerSuper block * blockSize +
          blocksPerSuper * blockSize := by
    rw [Nat.add_mul]
  exact Nat.le_trans hleft (by simpa [hend] using hmul)

theorem bpBlockSample_excess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block offset : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape (blockStartOf blockSize block + offset) <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hlohi :=
    bpSuperblockStartPos_le_blockStart_add_offset
      (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
      (block := block) (offset := offset)
  have hsampleLeBlockCount :
      blockStartOf blockSize block + offset <= blockCount * blockSize :=
    blockStart_add_offset_le_blockCount_mul hblock hoffset
  have hsampleLen :
      blockStartOf blockSize block + offset <= shape.bpCode.length :=
    Nat.le_trans hsampleLeBlockCount hcover
  have hdist :
      blockStartOf blockSize block + offset -
          bpSuperblockStartPos blockSize blocksPerSuper block <=
        bpSuperblockSpan blockSize blocksPerSuper := by
    have hend :=
      blockStart_add_offset_le_bpSuperblockEnd
        (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
        (block := block) (offset := offset) hblocks hoffset
    omega
  have hvar :=
    bpExcessAt_le_bpExcessAt_add_distance_right
      shape hlohi hsampleLen
  omega

theorem bpBlockSample_baseline_le_excess_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block offset : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpExcessAt shape (blockStartOf blockSize block + offset) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hlohi :=
    bpSuperblockStartPos_le_blockStart_add_offset
      (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
      (block := block) (offset := offset)
  have hsampleLeBlockCount :
      blockStartOf blockSize block + offset <= blockCount * blockSize :=
    blockStart_add_offset_le_blockCount_mul hblock hoffset
  have hsampleLen :
      blockStartOf blockSize block + offset <= shape.bpCode.length :=
    Nat.le_trans hsampleLeBlockCount hcover
  have hdist :
      blockStartOf blockSize block + offset -
          bpSuperblockStartPos blockSize blocksPerSuper block <=
        bpSuperblockSpan blockSize blocksPerSuper := by
    have hend :=
      blockStart_add_offset_le_bpSuperblockEnd
        (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
        (block := block) (offset := offset) hblocks hoffset
    omega
  have hvar :=
    bpExcessAt_le_bpExcessAt_add_distance_left
      shape hlohi hsampleLen
  omega

theorem natListMinFrom_le_of_mem
    {seed value : Nat} {values : List Nat}
    (hmem : List.Mem value values) :
    natListMinFrom seed values <= value := by
  induction values generalizing seed with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_trans
            (natListMinFrom_le_seed (Nat.min seed value) tail)
            (Nat.min_le_right seed value)
      | tail _ htail =>
          exact ih (seed := Nat.min seed head) htail

theorem le_natListMinFrom_add_of_forall_mem
    {lower seed span : Nat} {values : List Nat}
    (hseed : lower <= seed + span)
    (hmem : forall {value : Nat}, List.Mem value values ->
      lower <= value + span) :
    lower <= natListMinFrom seed values + span := by
  induction values generalizing seed with
  | nil =>
      simpa [natListMinFrom] using hseed
  | cons head tail ih =>
      have hhead : lower <= head + span :=
        hmem List.mem_cons_self
      have htail : forall {value : Nat}, List.Mem value tail ->
          lower <= value + span := by
        intro value hvalue
        exact hmem (List.mem_cons_of_mem head hvalue)
      have hminSeed : lower <= Nat.min seed head + span := by
        by_cases hle : seed <= head
        · simpa [Nat.min_eq_left hle] using hseed
        · have hheadLe : head <= seed := Nat.le_of_not_ge hle
          simpa [Nat.min_eq_right hheadLe] using hhead
      exact ih hminSeed htail

theorem le_natListMax_of_mem
    {value : Nat} {values : List Nat}
    (hmem : List.Mem value values) :
    value <= natListMax values := by
  induction values with
  | nil =>
      cases hmem
  | cons head tail ih =>
      cases hmem with
      | head =>
          exact Nat.le_max_left value (natListMax tail)
      | tail _ htail =>
          have htailLe := ih htail
          exact Nat.le_trans htailLe (Nat.le_max_right head (natListMax tail))

theorem bpBlockExcessSamples_offset_mem
    (shape : Cartesian.CartesianShape)
    {blockSize block offset : Nat}
    (hoffset : offset <= blockSize) :
    List.Mem
      (bpExcessAt shape (blockStartOf blockSize block + offset))
      (bpBlockExcessSamples shape blockSize block) := by
  unfold bpBlockExcessSamples
  apply List.mem_map.mpr
  refine ⟨offset, ?_, rfl⟩
  simp [Nat.lt_succ_iff, hoffset]

theorem bpBlockMinExcess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMinExcess shape blockSize block <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMinExcess
  have hmem :=
    bpBlockExcessSamples_offset_mem
      shape (blockSize := blockSize) (block := block) (offset := 0)
      (by omega)
  have hle :=
    natListMinFrom_le_of_mem
      (seed := shape.bpCode.length) hmem
  have hsample :=
    bpBlockSample_excess_le_baseline_add_span
      shape hblocks hblock hcover (block := block) (offset := 0)
      (by omega)
  exact Nat.le_trans hle hsample

theorem bpBlockMinExcess_baseline_le_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpBlockMinExcess shape blockSize block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMinExcess
  apply le_natListMinFrom_add_of_forall_mem
  · have hbaselineLen :
        bpSuperblockStartPos blockSize blocksPerSuper block <=
          shape.bpCode.length := by
      have hstartLe :
          bpSuperblockStartPos blockSize blocksPerSuper block <=
            blockStartOf blockSize block := by
        simpa using
          bpSuperblockStartPos_le_blockStart_add_offset
            (blockSize := blockSize) (blocksPerSuper := blocksPerSuper)
            (block := block) (offset := 0)
      have hblockStartLe :
          blockStartOf blockSize block <= blockCount * blockSize := by
        simpa using
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := 0) hblock (by omega)
      exact Nat.le_trans (Nat.le_trans hstartLe hblockStartLe) hcover
    have hbaselineExcess :=
      bpExcessAt_le_length shape
        (bpSuperblockStartPos blockSize blocksPerSuper block)
    omega
  · intro value hmem
    unfold bpBlockExcessSamples at hmem
    rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
    have hoffset : offset <= blockSize := by
      simp at hoffsetMem
      omega
    rw [← hvalue]
    exact
      bpBlockSample_baseline_le_excess_add_span
        shape hblocks hblock hcover (block := block)
        (offset := offset) hoffset

theorem bpBlockMaxExcess_le_baseline_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMaxExcess shape blockSize block <=
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpBlockMaxExcess
  apply natListMax_le_of_forall_mem
  intro value hmem
  unfold bpBlockExcessSamples at hmem
  rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
  have hoffset : offset <= blockSize := by
    simp at hoffsetMem
    omega
  rw [← hvalue]
  exact
    bpBlockSample_excess_le_baseline_add_span
      shape hblocks hblock hcover (block := block)
      (offset := offset) hoffset

theorem bpBlockMaxExcess_baseline_le_add_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) <=
      bpBlockMaxExcess shape blockSize block +
        bpSuperblockSpan blockSize blocksPerSuper := by
  have hmem :=
    bpBlockExcessSamples_offset_mem
      shape (blockSize := blockSize) (block := block) (offset := 0)
      (by omega)
  have hsampleLeMax :
      bpExcessAt shape (blockStartOf blockSize block + 0) <=
        bpBlockMaxExcess shape blockSize block := by
    unfold bpBlockMaxExcess
    exact le_natListMax_of_mem hmem
  have hbaselineSample :=
    bpBlockSample_baseline_le_excess_add_span
      shape hblocks hblock hcover (block := block) (offset := 0)
      (by omega)
  omega

def bpRelativeExcessEntry
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block value : Nat) : Nat :=
  value + bpSuperblockSpan blockSize blocksPerSuper -
    bpExcessAt shape
      (bpSuperblockStartPos blockSize blocksPerSuper block)

theorem bpRelativeExcessEntry_le_two_span
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper block value : Nat}
    (hupper :
      value <=
        bpExcessAt shape
            (bpSuperblockStartPos blockSize blocksPerSuper block) +
          bpSuperblockSpan blockSize blocksPerSuper)
    (hlower :
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) <=
        value + bpSuperblockSpan blockSize blocksPerSuper) :
    bpRelativeExcessEntry shape blockSize blocksPerSuper block value <=
      2 * bpSuperblockSpan blockSize blocksPerSuper := by
  unfold bpRelativeExcessEntry
  omega

def bpBlockRelativeMinExcess
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block : Nat) : Nat :=
  bpRelativeExcessEntry shape blockSize blocksPerSuper block
    (bpBlockMinExcess shape blockSize block)

def bpBlockRelativeMaxExcess
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper block : Nat) : Nat :=
  bpRelativeExcessEntry shape blockSize blocksPerSuper block
    (bpBlockMaxExcess shape blockSize block)

def bpBlockArgMinLocalOffset
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) : Nat :=
  bpBlockArgMinPrefixPos shape blockSize block -
    blockStartOf blockSize block

theorem bpBlockArgMinPrefixPosFrom_le_start_add
    (shape : Cartesian.CartesianShape)
    {start limit pos steps best : Nat}
    (hbest : best <= start + limit)
    (hpos : pos + steps <= start + limit + 1) :
    bpBlockArgMinPrefixPosFrom shape pos steps best <=
      start + limit := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpBlockArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpBlockArgMinPrefixPosFrom
      have hposLe : pos <= start + limit := by omega
      have hsample :
          Nat.min pos shape.bpCode.length <= start + limit := by
        exact Nat.le_trans (Nat.min_le_left pos shape.bpCode.length) hposLe
      by_cases hlt :
          bpExcessAt shape (Nat.min pos shape.bpCode.length) <
            bpExcessAt shape best
      · simp [hlt]
        apply ih
        · exact hsample
        · omega
      · simp [hlt]
        apply ih
        · exact hbest
        · omega

theorem bpBlockArgMinLocalOffset_le_blockSize
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockArgMinLocalOffset shape blockSize block <= blockSize := by
  unfold bpBlockArgMinLocalOffset
  have hargLen :=
    bpBlockArgMinPrefixPos_le_length shape blockSize block
  have hblockStartLen :
      blockStartOf blockSize block <= shape.bpCode.length := by
    have hblockStartLe :
        blockStartOf blockSize block <= blockCount * blockSize := by
      simpa using
        blockStart_add_offset_le_blockCount_mul
          (blockSize := blockSize) (blockCount := blockCount)
          (block := block) (offset := 0) hblock (by omega)
    exact Nat.le_trans hblockStartLe hcover
  have hargUpper :
      bpBlockArgMinPrefixPos shape blockSize block <=
        blockStartOf blockSize block + blockSize := by
    -- The absolute argmin scans only the block samples.  This arithmetic bound
    -- is the one remaining local-position fact needed by the relative table.
    have hblockEndLen :
        blockStartOf blockSize block + blockSize <=
          shape.bpCode.length := by
      have hblockEndLe :
          blockStartOf blockSize block + blockSize <=
            blockCount * blockSize := by
        exact
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := blockSize) hblock (by omega)
      exact Nat.le_trans hblockEndLe hcover
    unfold bpBlockArgMinPrefixPos
    apply bpBlockArgMinPrefixPosFrom_le_start_add
    · exact Nat.le_trans
        (Nat.min_le_left (blockStartOf blockSize block)
          shape.bpCode.length) (by omega)
    · omega
  omega

def bpSuperblockBaselineEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper superCount : Nat) : List Nat :=
  (List.range superCount).map fun super =>
    bpExcessAt shape (blockStartOf blockSize (super * blocksPerSuper))

def bpBlockRelativeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockRelativeMinExcess shape blockSize blocksPerSuper block

def bpBlockRelativeMaxExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block

def bpBlockArgMinLocalOffsetEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) : List Nat :=
  (List.range blockCount).map fun block =>
    bpBlockArgMinLocalOffset shape blockSize block

theorem bpSuperblockBaselineEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper superCount : Nat) :
    (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
      superCount).length = superCount := by
  simp [bpSuperblockBaselineEntries]

theorem bpBlockRelativeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) :
    (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
      blockCount).length = blockCount := by
  simp [bpBlockRelativeMinExcessEntries]

theorem bpBlockRelativeMaxExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount : Nat) :
    (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
      blockCount).length = blockCount := by
  simp [bpBlockRelativeMaxExcessEntries]

theorem bpBlockArgMinLocalOffsetEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount).length =
      blockCount := by
  simp [bpBlockArgMinLocalOffsetEntries]

theorem bpSuperblockBaselineEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper superCount superWidth entry : Nat}
    (hwidth : shape.bpCode.length < 2 ^ superWidth)
    (hmem :
      List.Mem entry
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)) :
    entry < 2 ^ superWidth := by
  unfold bpSuperblockBaselineEntries at hmem
  rcases List.mem_map.mp hmem with ⟨super, _hsuper, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpExcessAt_le_length shape
      (blockStartOf blockSize (super * blocksPerSuper))) hwidth

theorem bpBlockRelativeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount relativeWidth entry : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockRelativeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  apply Nat.lt_of_le_of_lt
  · unfold bpBlockRelativeMinExcess
    apply bpRelativeExcessEntry_le_two_span
    · exact bpBlockMinExcess_le_baseline_add_span
        shape hblocks hblock hcover
    · exact bpBlockMinExcess_baseline_le_add_span
        shape hblocks hblock hcover
  · exact hrelativeWidth

theorem bpBlockRelativeMaxExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount relativeWidth entry : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockRelativeMaxExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  apply Nat.lt_of_le_of_lt
  · unfold bpBlockRelativeMaxExcess
    apply bpRelativeExcessEntry_le_two_span
    · exact bpBlockMaxExcess_le_baseline_add_span
        shape hblocks hblock hcover
    · exact bpBlockMaxExcess_baseline_le_add_span
        shape hblocks hblock hcover
  · exact hrelativeWidth

theorem bpBlockArgMinLocalOffsetEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount relativeWidth entry : Nat}
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hrelativeWidth : blockSize < 2 ^ relativeWidth)
    (hmem :
      List.Mem entry
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)) :
    entry < 2 ^ relativeWidth := by
  unfold bpBlockArgMinLocalOffsetEntries at hmem
  rcases List.mem_map.mp hmem with ⟨block, hblockMem, hentry⟩
  have hblock : block < blockCount := by
    simp at hblockMem
    exact hblockMem
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpBlockArgMinLocalOffset_le_blockSize shape hblock hcover)
    hrelativeWidth

def relativeBPCloseSummaryPayloadOverhead
    (superSlots blockSlots : Nat) (n : Nat) : Nat :=
  sampledDirectoryOverhead superSlots n +
    logLogSampledDirectoryOverhead blockSlots n

theorem relativeBPCloseSummaryPayloadOverhead_littleO
    (superSlots blockSlots : Nat) :
    LittleOLinear
      (relativeBPCloseSummaryPayloadOverhead superSlots blockSlots) := by
  unfold relativeBPCloseSummaryPayloadOverhead
  exact
    (sampledDirectoryOverhead_littleO superSlots).add
      (logLogSampledDirectoryOverhead_littleO blockSlots)

theorem relativeBPCloseSummaryPayloadOverhead_le_compact
    (superSlots blockSlots n : Nat) :
    relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n <=
      compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots n := by
  simp [relativeBPCloseSummaryPayloadOverhead,
    compactBPCloseSummaryPayloadOverhead, sampledDirectoryOverhead,
    Nat.add_comm]

structure PayloadLiveBPRelativeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat) where
  baselineTable :
    FixedWidthNatTable
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount) superWidth
  minRelTable :
    FixedWidthNatTable
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount) relativeWidth
  maxRelTable :
    FixedWidthNatTable
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount) relativeWidth
  argOffsetTable :
    FixedWidthNatTable
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
      relativeWidth
  payload_length_eq :
    baselineTable.payload.length + minRelTable.payload.length +
      maxRelTable.payload.length + argOffsetTable.payload.length = overhead

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) : List Bool :=
  table.baselineTable.payload ++ table.minRelTable.payload ++
    table.maxRelTable.payload ++ table.argOffsetTable.payload

def summaryCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : Costed (Option (Nat × Nat × Nat × Nat)) :=
  Costed.bind (table.baselineTable.readCosted (block / blocksPerSuper))
    fun baseline? =>
      Costed.bind (table.minRelTable.readCosted block) fun minRel? =>
        Costed.bind (table.maxRelTable.readCosted block) fun maxRel? =>
          Costed.map
            (fun argOffset? =>
              match baseline?, minRel?, maxRel?, argOffset? with
              | some baseline, some minRel, some maxRel, some argOffset =>
                  some (baseline, minRel, maxRel, argOffset)
              | _, _, _, _ => none)
            (table.argOffsetTable.readCosted block)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    table.payload.length = overhead := by
  have h := table.payload_length_eq
  simp only [payload, List.length_append]
  omega

theorem summaryCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).cost <= 4 := by
  unfold summaryCosted
  cases (table.baselineTable.readCosted (block / blocksPerSuper)).value
  <;> cases (table.minRelTable.readCosted block).value
  <;> cases (table.maxRelTable.readCosted block).value
  <;> simp [Costed.bind, Costed.map]

theorem summaryCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).erase =
      match
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)[block / blocksPerSuper]?,
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]?,
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]?,
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
      with
      | some baseline, some minRel, some maxRel, some argOffset =>
          some (baseline, minRel, maxRel, argOffset)
      | _, _, _, _ => none := by
  unfold summaryCosted
  have hbaseline :
      (table.baselineTable.readCosted (block / blocksPerSuper)).value =
        (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
          superCount)[block / blocksPerSuper]? := by
    exact table.baselineTable.readCosted_erase (block / blocksPerSuper)
  have hmin :
      (table.minRelTable.readCosted block).value =
        (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]? := by
    exact table.minRelTable.readCosted_erase block
  have hmax :
      (table.maxRelTable.readCosted block).value =
        (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
          blockCount)[block]? := by
    exact table.maxRelTable.readCosted_erase block
  have harg :
      (table.argOffsetTable.readCosted block).value =
        (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]? := by
    exact table.argOffsetTable.readCosted_erase block
  cases hbaselineEntry :
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount)[block / blocksPerSuper]?
  <;> cases hminEntry :
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]?
  <;> cases hmaxEntry :
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]?
  <;> cases hargEntry :
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hbaseline, hmin, hmax,
    harg, hbaselineEntry, hminEntry, hmaxEntry, hargEntry]

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {index : Nat} {word : List Bool},
      table.baselineTable.store.words[index]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  constructor
  · intro index word hword
    have hlen := table.baselineTable.read_word_length_of_some hword
    omega
  constructor
  · intro block word hword
    have hlen := table.minRelTable.read_word_length_of_some hword
    omega
  constructor
  · intro block word hword
    have hlen := table.maxRelTable.read_word_length_of_some hword
    omega
  intro block word hword
  have hlen := table.argOffsetTable.read_word_length_of_some hword
  omega

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    table.payload.length = overhead /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  constructor
  · exact table.payload_length
  intro block
  exact ⟨table.summaryCosted_cost_le_four block,
    table.summaryCosted_erase block⟩

end PayloadLiveBPRelativeMinMaxArgSummaryTable

def concreteBPRelativeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth) :
    PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      (superCount * superWidth + 3 * (blockCount * relativeWidth)) where
  baselineTable :=
    FixedWidthNatTable.ofEntries
      (bpSuperblockBaselineEntries shape blockSize blocksPerSuper superCount)
      superWidth
      (by
        intro entry hmem
        exact bpSuperblockBaselineEntries_mem_bound hsuperWidth hmem)
  minRelTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockRelativeMinExcessEntries_mem_bound
          hblocks hcover hrelativeWidth hmem)
  maxRelTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockRelativeMaxExcessEntries_mem_bound
          hblocks hcover hrelativeWidth hmem)
  argOffsetTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
      relativeWidth
      (by
        intro entry hmem
        exact bpBlockArgMinLocalOffsetEntries_mem_bound
          hcover hargWidth hmem)
  payload_length_eq := by
    have hbase :
        (FixedWidthNatTable.ofEntries
          (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
            superCount)
          superWidth
          (by
            intro entry hmem
            exact bpSuperblockBaselineEntries_mem_bound
              hsuperWidth hmem)).payload.length =
          superCount * superWidth := by
      simpa [bpSuperblockBaselineEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
            superCount)
          superWidth
          (by
            intro entry hmem
            exact bpSuperblockBaselineEntries_mem_bound
              hsuperWidth hmem)).payload_length
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMinExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockRelativeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMinExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload_length
    have hmax :
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMaxExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockRelativeMaxExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
            blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockRelativeMaxExcessEntries_mem_bound
              hblocks hcover hrelativeWidth hmem)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockArgMinLocalOffsetEntries_mem_bound
              hcover hargWidth hmem)).payload.length =
          blockCount * relativeWidth := by
      simpa [bpBlockArgMinLocalOffsetEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)
          relativeWidth
          (by
            intro entry hmem
            exact bpBlockArgMinLocalOffsetEntries_mem_bound
              hcover hargWidth hmem)).payload_length
    omega

theorem concreteBPRelativeMinMaxArgSummaryTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    table.payload.length =
        superCount * superWidth + 3 * (blockCount * relativeWidth) /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  exact
    (concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth).profile

theorem concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth superSlots blockSlots n : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperPayload :
      superCount * superWidth <= sampledDirectoryOverhead superSlots n)
    (hblockPayload :
      3 * (blockCount * relativeWidth) <=
        logLogSampledDirectoryOverhead blockSlots n) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    LittleOLinear
      (relativeBPCloseSummaryPayloadOverhead superSlots blockSlots) /\
      table.payload.length <=
        relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  let table :=
    concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth
  constructor
  · exact relativeBPCloseSummaryPayloadOverhead_littleO
      superSlots blockSlots
  constructor
  · have hlen :
        table.payload.length =
          superCount * superWidth + 3 * (blockCount * relativeWidth) :=
      table.payload_length
    change table.payload.length <=
      relativeBPCloseSummaryPayloadOverhead superSlots blockSlots n
    unfold relativeBPCloseSummaryPayloadOverhead
    omega
  intro block
  exact ⟨table.summaryCosted_cost_le_four block,
    table.summaryCosted_erase block⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth superSlots blockSlots n : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperPayload :
      superCount * superWidth <= sampledDirectoryOverhead superSlots n)
    (hblockPayload :
      3 * (blockCount * relativeWidth) <=
        logLogSampledDirectoryOverhead blockSlots n) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead blockSlots 0 0 superSlots n /\
      forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
                superCount)[block / blocksPerSuper]?,
              (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
                blockCount)[block]?,
              (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none := by
  let table :=
    concreteBPRelativeMinMaxArgSummaryTable shape blockSize
      blocksPerSuper blockCount superCount superWidth relativeWidth
      hblocks hcover hsuperWidth hrelativeWidth hargWidth
  have hrel :=
    concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile
      shape blockSize blocksPerSuper blockCount superCount superWidth
      relativeWidth superSlots blockSlots n hblocks hcover hsuperWidth
      hrelativeWidth hargWidth hsuperPayload hblockPayload
  constructor
  · exact
      compactBPCloseSummaryPayloadOverhead_littleO
        blockSlots 0 0 superSlots
  constructor
  · exact Nat.le_trans hrel.2.1
      (relativeBPCloseSummaryPayloadOverhead_le_compact
        superSlots blockSlots n)
  · exact hrel.2.2

theorem concreteBPRelativeMinMaxArgSummaryTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth : Nat)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperWidth : shape.bpCode.length < 2 ^ superWidth)
    (hrelativeWidth :
      2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth)
    (hargWidth : blockSize < 2 ^ relativeWidth)
    (hsuperMachine :
      superWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth
    (forall {index : Nat} {word : List Bool},
      table.baselineTable.store.words[index]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.read_words_length_le_machine
      (concreteBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        hblocks hcover hsuperWidth hrelativeWidth hargWidth)
      hsuperMachine hrelativeMachine

def canonicalBPRelativeSummaryBase
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.log2 shape.size + 1

def canonicalBPRelativeSummaryBlockSizeRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummaryBlocksPerSuperRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummaryBlockCountRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  shape.size / canonicalBPRelativeSummaryBase shape

def canonicalBPRelativeSummarySuperCountRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBlockCountRaw shape /
      canonicalBPRelativeSummaryBlocksPerSuperRaw shape + 1

def canonicalBPRelativeSummarySuperWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits shape.bpCode.length

def canonicalBPRelativeSummaryRelativeWidthRaw
    (shape : Cartesian.CartesianShape) : Nat :=
  2 * (Nat.log2 (canonicalBPRelativeSummaryBase shape) + 1) + 3

def canonicalBPRelativeSummarySuperSlots : Nat := 16

def canonicalBPRelativeSummaryBlockSlots : Nat := 64

def canonicalBPRelativeMinMaxArgSummaryTableActive
    (shape : Cartesian.CartesianShape) : Prop :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let blocksPerSuper := canonicalBPRelativeSummaryBlocksPerSuperRaw shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  let superCount := canonicalBPRelativeSummarySuperCountRaw shape
  let superWidth := canonicalBPRelativeSummarySuperWidth shape
  let relativeWidth := canonicalBPRelativeSummaryRelativeWidthRaw shape
  blockCount * blockSize <= shape.bpCode.length /\
    2 * bpSuperblockSpan blockSize blocksPerSuper < 2 ^ relativeWidth /\
    blockSize < 2 ^ relativeWidth /\
    superCount * superWidth <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size /\
    3 * (blockCount * relativeWidth) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size /\
    relativeWidth <=
      SuccinctRank.machineWordBits shape.bpCode.length

instance canonicalBPRelativeMinMaxArgSummaryTableActive_decidable
    (shape : Cartesian.CartesianShape) :
    Decidable (canonicalBPRelativeMinMaxArgSummaryTableActive shape) := by
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive
  infer_instance

def canonicalBPRelativeSummaryBlockSize
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlockSizeRaw shape
  else
    0

def canonicalBPRelativeSummaryBlocksPerSuper
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlocksPerSuperRaw shape
  else
    1

def canonicalBPRelativeSummaryBlockCount
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryBlockCountRaw shape
  else
    0

def canonicalBPRelativeSummarySuperCount
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummarySuperCountRaw shape
  else
    0

def canonicalBPRelativeSummaryRelativeWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  if canonicalBPRelativeMinMaxArgSummaryTableActive shape then
    canonicalBPRelativeSummaryRelativeWidthRaw shape
  else
    0

private theorem canonicalBPRelativeSummary_active_parts
    {shape : Cartesian.CartesianShape}
    (hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length /\
      2 * bpSuperblockSpan
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryBlockSizeRaw shape <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummarySuperCountRaw shape *
          canonicalBPRelativeSummarySuperWidth shape <=
        sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
          shape.size /\
      3 * (canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryRelativeWidthRaw shape) <=
        logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
          shape.size /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRank.machineWordBits shape.bpCode.length := by
  simpa [canonicalBPRelativeMinMaxArgSummaryTableActive] using hactive

def canonicalBPRelativeSummaryLargeRegime
    (shape : Cartesian.CartesianShape) : Prop :=
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  base <= blockCount /\
    canonicalBPRelativeSummarySuperWidth shape <= 8 * base /\
    2 * bpSuperblockSpan
        (canonicalBPRelativeSummaryBlockSizeRaw shape)
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
    canonicalBPRelativeSummaryBlockSizeRaw shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
    canonicalBPRelativeSummaryRelativeWidthRaw shape <=
      canonicalBPRelativeSummarySuperWidth shape

theorem canonicalBPRelativeSummary_large_parts
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummaryBase shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperWidth shape <=
        8 * canonicalBPRelativeSummaryBase shape /\
      2 * bpSuperblockSpan
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryBlockSizeRaw shape <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        canonicalBPRelativeSummarySuperWidth shape := by
  simpa [canonicalBPRelativeSummaryLargeRegime] using hlarge

private theorem canonicalBPRelativeSummary_raw_cover
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryBlockSizeRaw shape <=
      shape.bpCode.length := by
  rw [Cartesian.CartesianShape.bpCode_length]
  have hdiv :
      (shape.size / canonicalBPRelativeSummaryBase shape) *
          canonicalBPRelativeSummaryBase shape <= shape.size :=
    Nat.div_mul_le_self shape.size (canonicalBPRelativeSummaryBase shape)
  have hmul := Nat.mul_le_mul_left 2 hdiv
  simpa [canonicalBPRelativeSummaryBlockCountRaw,
    canonicalBPRelativeSummaryBlockSizeRaw, Nat.mul_assoc,
    Nat.mul_left_comm, Nat.mul_comm] using hmul

private theorem canonicalBPRelativeSummary_superPayload_bound_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummarySuperCountRaw shape *
        canonicalBPRelativeSummarySuperWidth shape <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size := by
  rcases canonicalBPRelativeSummary_large_parts (shape := shape) hlarge with
    ⟨hbase_le_count, hsuperWidth, _hspan, _harg, _hmachine⟩
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  have hbase_pos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hdiv_pos : 1 <= blockCount / base := by
    exact (Nat.le_div_iff_mul_le hbase_pos).2 (by
      simpa [Nat.mul_comm] using hbase_le_count)
  have hsuperCount_le :
      blockCount / base + 1 <= 2 * (blockCount / base) := by
    omega
  have hright_le :
      (2 * (blockCount / base)) * (8 * base) <= 16 * blockCount := by
    have hdiv :
        (blockCount / base) * base <= blockCount :=
      Nat.div_mul_le_self blockCount base
    have hmul := Nat.mul_le_mul_left 16 hdiv
    calc
      (2 * (blockCount / base)) * (8 * base) =
          16 * ((blockCount / base) * base) := by
        calc
          (2 * (blockCount / base)) * (8 * base) =
              (2 * (blockCount / base)) * (base * 8) := by
            rw [Nat.mul_comm 8 base]
          _ = ((2 * (blockCount / base)) * base) * 8 := by
            rw [← Nat.mul_assoc]
          _ = (2 * ((blockCount / base) * base)) * 8 := by
            rw [Nat.mul_assoc 2 (blockCount / base) base]
          _ = 8 * (2 * ((blockCount / base) * base)) := by
            rw [Nat.mul_comm]
          _ = (8 * 2) * ((blockCount / base) * base) := by
            rw [Nat.mul_assoc]
          _ = 16 * ((blockCount / base) * base) := by
            simp
      _ <= 16 * blockCount := hmul
  have hmul :
      (blockCount / base + 1) *
          canonicalBPRelativeSummarySuperWidth shape <=
        (2 * (blockCount / base)) * (8 * base) :=
    Nat.mul_le_mul hsuperCount_le hsuperWidth
  have hbudget := Nat.le_trans hmul hright_le
  simpa [canonicalBPRelativeSummarySuperCountRaw,
    canonicalBPRelativeSummaryBlockCountRaw, canonicalBPRelativeSummaryBase,
    canonicalBPRelativeSummarySuperSlots, sampledDirectoryOverhead, base,
    blockCount] using hbudget

private theorem canonicalBPRelativeSummary_blockPayload_bound_raw
    (shape : Cartesian.CartesianShape) :
    3 * (canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryRelativeWidthRaw shape) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let blockCount := canonicalBPRelativeSummaryBlockCountRaw shape
  let logBase := Nat.log2 base + 1
  have hlog_pos : 0 < logBase := by
    simp [logBase]
  have hfactor :
      3 * (2 * logBase + 3) <= 64 * logBase := by
    omega
  have hmul := Nat.mul_le_mul_left blockCount hfactor
  simpa [canonicalBPRelativeSummaryRelativeWidthRaw,
    canonicalBPRelativeSummaryBlockCountRaw, canonicalBPRelativeSummaryBase,
    canonicalBPRelativeSummaryBlockSlots, logLogSampledDirectoryOverhead,
    base, blockCount, logBase, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using hmul

theorem natLog2_ge_of_pow_le
    {k n : Nat} (hpow : 2 ^ k <= n) :
    k <= Nat.log2 n := by
  have hn : n ≠ 0 := by
    intro hzero
    subst n
    have hpos : 0 < 2 ^ k := Nat.pow_pos (by omega)
    omega
  exact (Nat.le_log2 hn).2 hpow

theorem natLog2_succ_le_of_pos_lt_pow
    {n k : Nat} (hnpos : 0 < n) (hlt : n < 2 ^ k) :
    Nat.log2 n + 1 <= k := by
  by_cases hk : k <= Nat.log2 n
  · have hn : n ≠ 0 := by omega
    have hpow : 2 ^ k <= n := (Nat.le_log2 hn).1 hk
    omega
  · omega

theorem nat_succ_square_le_two_pow_of_six_le
    (q : Nat) :
    6 <= q -> (q + 1) * (q + 1) <= 2 ^ q := by
  exact Nat.strongRecOn q (fun q ih hq => by
    by_cases hq8 : 8 <= q
    · have hprev : 6 <= q - 2 := by omega
      have hprev_lt : q - 2 < q := by omega
      have ihprev := ih (q - 2) hprev_lt hprev
      have hlin : q + 1 <= 2 * ((q - 2) + 1) := by omega
      have hsq :
          (q + 1) * (q + 1) <=
            2 * (2 * (((q - 2) + 1) * ((q - 2) + 1))) := by
        have hmul := Nat.mul_le_mul hlin hlin
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
      have hpowMul : 2 * (2 * 2 ^ (q - 2)) = 2 ^ q := by
        have hqeq : q = (q - 2) + 2 := by omega
        calc
          2 * (2 * 2 ^ (q - 2)) = 2 ^ ((q - 2) + 2) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by rw [← hqeq]
      exact Nat.le_trans hsq
        (by
          have hmul := Nat.mul_le_mul_left 2
            (Nat.mul_le_mul_left 2 ihprev)
          simpa [hpowMul] using hmul)
    · have hqCases : q = 6 ∨ q = 7 := by omega
      rcases hqCases with hqeq | hqeq
      · subst q
        decide
      · subst q
        decide)

theorem nat_log2_succ_square_le_self_of_log2_ge_six
    {n : Nat} (hn : n ≠ 0) (hlog : 6 <= Nat.log2 n) :
    (Nat.log2 n + 1) * (Nat.log2 n + 1) <= n := by
  exact Nat.le_trans
    (nat_succ_square_le_two_pow_of_six_le (Nat.log2 n) hlog)
    (Nat.log2_self_le hn)

theorem canonicalBPRelativeSummaryBase_le_blockCountRaw_of_size_ge
    {shape : Cartesian.CartesianShape}
    (hsize : 2 ^ 128 <= shape.size) :
    canonicalBPRelativeSummaryBase shape <=
      canonicalBPRelativeSummaryBlockCountRaw shape := by
  have hsize_pos : shape.size ≠ 0 := by
    have hpow : 0 < 2 ^ 128 := Nat.pow_pos (by omega)
    omega
  have hlog128 : 128 <= Nat.log2 shape.size :=
    natLog2_ge_of_pow_le hsize
  have hlog6 : 6 <= Nat.log2 shape.size := by omega
  have hsquare :=
    nat_log2_succ_square_le_self_of_log2_ge_six
      (n := shape.size) hsize_pos hlog6
  have hbase_pos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  exact (Nat.le_div_iff_mul_le hbase_pos).2 (by
    simpa [canonicalBPRelativeSummaryBase,
      canonicalBPRelativeSummaryBlockCountRaw, Nat.mul_comm] using
      hsquare)

theorem canonicalBPRelativeSummaryBase_ge_128_of_size_ge
    {shape : Cartesian.CartesianShape}
    (hsize : 2 ^ 128 <= shape.size) :
    128 <= canonicalBPRelativeSummaryBase shape := by
  have hlog128 : 128 <= Nat.log2 shape.size :=
    natLog2_ge_of_pow_le hsize
  simp [canonicalBPRelativeSummaryBase]
  omega

theorem canonicalBPRelativeSummaryBase_le_superWidth_of_size_pos
    {shape : Cartesian.CartesianShape}
    (hsize_pos : 0 < shape.size) :
    canonicalBPRelativeSummaryBase shape <=
      canonicalBPRelativeSummarySuperWidth shape := by
  unfold canonicalBPRelativeSummaryBase
  unfold canonicalBPRelativeSummarySuperWidth
  rw [Cartesian.CartesianShape.bpCode_length]
  unfold SuccinctRank.machineWordBits
  have hlen_pos : 0 < 2 * shape.size := by omega
  have hpown : 2 ^ Nat.log2 shape.size <= shape.size := by
    exact Nat.log2_self_le (by omega)
  have hpowLen : 2 ^ Nat.log2 shape.size <= 2 * shape.size := by
    omega
  have hlogLen :
      Nat.log2 shape.size <= Nat.log2 (2 * shape.size) :=
    (Nat.le_log2 (by omega)).2 hpowLen
  omega

theorem canonicalBPRelativeSummaryBlockSize_le_two_machine_of_size_pos
    {shape : Cartesian.CartesianShape}
    (hsize_pos : 0 < shape.size) :
    canonicalBPRelativeSummaryBlockSize shape <=
      2 * SuccinctRank.machineWordBits shape.bpCode.length := by
  by_cases hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hbase :=
      canonicalBPRelativeSummaryBase_le_superWidth_of_size_pos
        (shape := shape) hsize_pos
    simp [canonicalBPRelativeSummaryBlockSize, hactive,
      canonicalBPRelativeSummaryBlockSizeRaw,
      canonicalBPRelativeSummarySuperWidth] at hbase ⊢
    omega
  · simp [canonicalBPRelativeSummaryBlockSize, hactive]

theorem canonicalBPRelativeSummarySuperWidth_le_eight_base_of_size_pos
    {shape : Cartesian.CartesianShape}
    (hsize_pos : 0 < shape.size) :
    canonicalBPRelativeSummarySuperWidth shape <=
      8 * canonicalBPRelativeSummaryBase shape := by
  unfold canonicalBPRelativeSummarySuperWidth
  rw [Cartesian.CartesianShape.bpCode_length]
  unfold SuccinctRank.machineWordBits
  let base := canonicalBPRelativeSummaryBase shape
  have hbase_pos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hn_lt : shape.size < 2 ^ base := by
    simpa [base, canonicalBPRelativeSummaryBase] using
      Nat.lt_log2_self (n := shape.size)
  have hlen_lt_base :
      2 * shape.size < 2 ^ (base + 1) := by
    have hmul := Nat.mul_lt_mul_of_pos_left hn_lt (by omega : 0 < 2)
    simpa [Nat.pow_succ, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hmul
  have hpow_le :
      2 ^ (base + 1) <= 2 ^ (8 * base) := by
    exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
  have hlen_lt : 2 * shape.size < 2 ^ (8 * base) :=
    Nat.lt_of_lt_of_le hlen_lt_base hpow_le
  have hlen_pos : 0 < 2 * shape.size := by omega
  have hlog :=
    natLog2_succ_le_of_pos_lt_pow hlen_pos hlen_lt
  simpa [base] using hlog

theorem four_mul_square_lt_two_pow_two_log_succ_add_three
    (base : Nat) :
    2 * (2 * (base * base)) <
      2 ^ (2 * (Nat.log2 base + 1) + 3) := by
  let width := Nat.log2 base + 1
  let powWidth := 2 ^ width
  have hbase_lt : base < powWidth := by
    simpa [width, powWidth] using Nat.lt_log2_self (n := base)
  have hbase_square :
      base * base <= powWidth * powWidth :=
    Nat.mul_le_mul (Nat.le_of_lt hbase_lt) (Nat.le_of_lt hbase_lt)
  have hscaled :
      2 * (2 * (base * base)) <=
        2 * (2 * (powWidth * powWidth)) :=
    Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 hbase_square)
  have hpowWidth_pos : 0 < powWidth * powWidth := by
    exact Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.pow_pos (by omega))
  have hstrict :
      2 * (2 * (powWidth * powWidth)) <
        8 * (powWidth * powWidth) := by
    omega
  have htarget :
      8 * (powWidth * powWidth) =
        2 ^ (2 * (Nat.log2 base + 1) + 3) := by
    have hexp : width + width + 3 = 2 * width + 3 := by omega
    calc
      8 * (powWidth * powWidth) =
          2 ^ (width + width + 3) := by
        simp [powWidth, Nat.pow_add, Nat.mul_assoc, Nat.mul_comm]
      _ = 2 ^ (2 * (Nat.log2 base + 1) + 3) := by
        rw [hexp]
  exact Nat.lt_of_le_of_lt hscaled (by simpa [htarget] using hstrict)

theorem canonicalBPRelativeSummarySpanRaw_width_bound
    (shape : Cartesian.CartesianShape) :
    2 * bpSuperblockSpan
        (canonicalBPRelativeSummaryBlockSizeRaw shape)
        (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape := by
  simpa [bpSuperblockSpan, canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryRelativeWidthRaw,
    canonicalBPRelativeSummaryBase, Nat.mul_assoc, Nat.mul_left_comm,
    Nat.mul_comm] using
    four_mul_square_lt_two_pow_two_log_succ_add_three
      (canonicalBPRelativeSummaryBase shape)

theorem canonicalBPRelativeSummaryBlockSizeRaw_width_bound
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape := by
  have hspan := canonicalBPRelativeSummarySpanRaw_width_bound shape
  let base := canonicalBPRelativeSummaryBase shape
  have hbase_pos : 1 <= base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hbase_le_square : base <= base * base := by
    calc
      base = base * 1 := by rw [Nat.mul_one]
      _ <= base * base := Nat.mul_le_mul_left base hbase_pos
  have hle : 2 * base <= 2 * (2 * (base * base)) := by
    have hmul := Nat.mul_le_mul_left 2 hbase_le_square
    have hright :
        2 * (base * base) <= 2 * (2 * (base * base)) := by
      omega
    exact Nat.le_trans hmul hright
  have hleRaw :
      canonicalBPRelativeSummaryBlockSizeRaw shape <=
        2 * bpSuperblockSpan
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) := by
    simpa [base, bpSuperblockSpan,
      canonicalBPRelativeSummaryBlockSizeRaw,
      canonicalBPRelativeSummaryBlocksPerSuperRaw,
      Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hle
  exact Nat.lt_of_le_of_lt hleRaw hspan

theorem canonicalBPRelativeSummaryRelativeWidthRaw_le_base_of_base_ge_128
    {shape : Cartesian.CartesianShape}
    (hbase : 128 <= canonicalBPRelativeSummaryBase shape) :
    canonicalBPRelativeSummaryRelativeWidthRaw shape <=
      canonicalBPRelativeSummaryBase shape := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  have hbase_ne : base ≠ 0 := by omega
  have hlogBase_ge : 6 <= Nat.log2 base := by
    have h128 : 2 ^ 7 <= base := by
      simpa using hbase
    have hlog7 : 7 <= Nat.log2 base :=
      natLog2_ge_of_pow_le h128
    omega
  have hsquare :=
    nat_log2_succ_square_le_self_of_log2_ge_six
      (n := base) hbase_ne hlogBase_ge
  have hlogBase_three : 3 <= logBase := by
    have hlog7 : 7 <= Nat.log2 base := by
      have h128 : 2 ^ 7 <= base := by
        simpa using hbase
      exact natLog2_ge_of_pow_le h128
    omega
  have hthree_le_square : 3 * logBase <= logBase * logBase :=
    Nat.mul_le_mul_right logBase hlogBase_three
  have hrel_le_three :
      2 * logBase + 3 <= 3 * logBase := by
    omega
  have hrel :
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        3 * logBase := by
    simpa [canonicalBPRelativeSummaryRelativeWidthRaw, base, logBase]
      using hrel_le_three
  have hsq : logBase * logBase <= base := by
    simpa [logBase] using hsquare
  have hthree_le_base : 3 * logBase <= base :=
    Nat.le_trans hthree_le_square hsq
  exact Nat.le_trans hrel (by simpa [base] using hthree_le_base)

theorem canonicalBPRelativeSummaryLargeRegime_of_size_ge
    {shape : Cartesian.CartesianShape}
    (hsize : 2 ^ 128 <= shape.size) :
    canonicalBPRelativeSummaryLargeRegime shape := by
  have hsize_pos : 0 < shape.size := by
    have hpow : 0 < 2 ^ 128 := Nat.pow_pos (by omega)
    omega
  have hbase_ge :=
    canonicalBPRelativeSummaryBase_ge_128_of_size_ge
      (shape := shape) hsize
  have hrel_le_base :=
    canonicalBPRelativeSummaryRelativeWidthRaw_le_base_of_base_ge_128
      (shape := shape) hbase_ge
  have hbase_le_super :=
    canonicalBPRelativeSummaryBase_le_superWidth_of_size_pos
      (shape := shape) hsize_pos
  unfold canonicalBPRelativeSummaryLargeRegime
  exact ⟨
    canonicalBPRelativeSummaryBase_le_blockCountRaw_of_size_ge
      (shape := shape) hsize,
    canonicalBPRelativeSummarySuperWidth_le_eight_base_of_size_pos
      (shape := shape) hsize_pos,
    canonicalBPRelativeSummarySpanRaw_width_bound shape,
    canonicalBPRelativeSummaryBlockSizeRaw_width_bound shape,
    Nat.le_trans hrel_le_base hbase_le_super⟩

theorem canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeMinMaxArgSummaryTableActive shape := by
  rcases canonicalBPRelativeSummary_large_parts (shape := shape) hlarge with
    ⟨_hbase_le_count, _hsuperWidth, hspan, harg, hmachine⟩
  unfold canonicalBPRelativeMinMaxArgSummaryTableActive
  exact ⟨canonicalBPRelativeSummary_raw_cover shape, hspan, harg,
    canonicalBPRelativeSummary_superPayload_bound_of_large
      (shape := shape) hlarge,
    canonicalBPRelativeSummary_blockPayload_bound_raw shape,
    hmachine⟩

theorem canonicalBPRelativeSummary_blocksPerSuper_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlocksPerSuper shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · simp [canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryBlocksPerSuperRaw,
      canonicalBPRelativeSummaryBase, hactive]
  · simp [canonicalBPRelativeSummaryBlocksPerSuper, hactive]

theorem canonicalBPRelativeSummary_cover
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCount shape *
        canonicalBPRelativeSummaryBlockSize shape <=
      shape.bpCode.length := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlockSize, hactive] using hparts.1
  · simp [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlockSize, hactive]

theorem canonicalBPRelativeSummary_superWidth_bound
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      2 ^ canonicalBPRelativeSummarySuperWidth shape := by
  unfold canonicalBPRelativeSummarySuperWidth
  unfold SuccinctRank.machineWordBits
  exact Nat.lt_log2_self (n := shape.bpCode.length)

theorem canonicalBPRelativeSummary_relativeWidth_bound
    (shape : Cartesian.CartesianShape) :
    2 * bpSuperblockSpan
        (canonicalBPRelativeSummaryBlockSize shape)
        (canonicalBPRelativeSummaryBlocksPerSuper shape) <
      2 ^ canonicalBPRelativeSummaryRelativeWidth shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using hparts.2.1
  · simp [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummaryRelativeWidth, bpSuperblockSpan, hactive]

theorem canonicalBPRelativeSummary_argWidth_bound
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockSize shape <
      2 ^ canonicalBPRelativeSummaryRelativeWidth shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using hparts.2.2.1
  · simp [canonicalBPRelativeSummaryBlockSize,
      canonicalBPRelativeSummaryRelativeWidth, hactive]

theorem canonicalBPRelativeSummary_superPayload_bound
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummarySuperCount shape *
        canonicalBPRelativeSummarySuperWidth shape <=
      sampledDirectoryOverhead canonicalBPRelativeSummarySuperSlots
        shape.size := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummarySuperCount, hactive] using
      hparts.2.2.2.1
  · simp [canonicalBPRelativeSummarySuperCount, hactive]

theorem canonicalBPRelativeSummary_blockPayload_bound
    (shape : Cartesian.CartesianShape) :
    3 * (canonicalBPRelativeSummaryBlockCount shape *
        canonicalBPRelativeSummaryRelativeWidth shape) <=
      logLogSampledDirectoryOverhead canonicalBPRelativeSummaryBlockSlots
        shape.size := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryRelativeWidth, hactive] using
      hparts.2.2.2.2.1
  · simp [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryRelativeWidth, hactive]

theorem canonicalBPRelativeSummary_superWidth_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummarySuperWidth shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  exact Nat.le_refl _

theorem canonicalBPRelativeSummary_relativeWidth_machine
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryRelativeWidth shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hparts :=
      canonicalBPRelativeSummary_active_parts (shape := shape) hactive
    simpa [canonicalBPRelativeSummaryRelativeWidth, hactive] using
      hparts.2.2.2.2.2
  · simp [canonicalBPRelativeSummaryRelativeWidth, hactive]

def concreteBPRelativeMinMaxArgSummaryTable_canonical
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeMinMaxArgSummaryTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      (canonicalBPRelativeSummarySuperCount shape *
          canonicalBPRelativeSummarySuperWidth shape +
        3 * (canonicalBPRelativeSummaryBlockCount shape *
          canonicalBPRelativeSummaryRelativeWidth shape)) :=
  concreteBPRelativeMinMaxArgSummaryTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlocksPerSuper shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (canonicalBPRelativeSummarySuperCount shape)
    (canonicalBPRelativeSummarySuperWidth shape)
    (canonicalBPRelativeSummaryRelativeWidth shape)
    (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
    (canonicalBPRelativeSummary_cover shape)
    (canonicalBPRelativeSummary_superWidth_bound shape)
    (canonicalBPRelativeSummary_relativeWidth_bound shape)
    (canonicalBPRelativeSummary_argWidth_bound shape)

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile
    (shape : Cartesian.CartesianShape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    LittleOLinear
      (compactBPCloseSummaryPayloadOverhead
        canonicalBPRelativeSummaryBlockSlots 0 0
        canonicalBPRelativeSummarySuperSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummarySuperCount shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuper shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlocksPerSuper shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSize shape)
                (canonicalBPRelativeSummaryBlockCount shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  have hprofile :=
    concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      canonicalBPRelativeSummarySuperSlots
      canonicalBPRelativeSummaryBlockSlots
      shape.size
      (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
      (canonicalBPRelativeSummary_cover shape)
      (canonicalBPRelativeSummary_superWidth_bound shape)
      (canonicalBPRelativeSummary_relativeWidth_bound shape)
      (canonicalBPRelativeSummary_argWidth_bound shape)
      (canonicalBPRelativeSummary_superPayload_bound shape)
      (canonicalBPRelativeSummary_blockPayload_bound shape)
  have hwords :=
    concreteBPRelativeMinMaxArgSummaryTable_read_words_length_le_machine
      shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlocksPerSuper shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (canonicalBPRelativeSummarySuperCount shape)
      (canonicalBPRelativeSummarySuperWidth shape)
      (canonicalBPRelativeSummaryRelativeWidth shape)
      (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
      (canonicalBPRelativeSummary_cover shape)
      (canonicalBPRelativeSummary_superWidth_bound shape)
      (canonicalBPRelativeSummary_relativeWidth_bound shape)
      (canonicalBPRelativeSummary_argWidth_bound shape)
      (canonicalBPRelativeSummary_superWidth_machine shape)
      (canonicalBPRelativeSummary_relativeWidth_machine shape)
  exact ⟨hprofile.1, hprofile.2.1, hprofile.2.2, hwords.1,
    hwords.2.1, hwords.2.2.1, hwords.2.2.2⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large
    (shape : Cartesian.CartesianShape)
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    canonicalBPRelativeSummaryBlockSize shape =
        canonicalBPRelativeSummaryBlockSizeRaw shape /\
      canonicalBPRelativeSummaryBlocksPerSuper shape =
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      canonicalBPRelativeSummaryBlockCount shape =
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperCount shape =
        canonicalBPRelativeSummarySuperCountRaw shape /\
      canonicalBPRelativeSummaryRelativeWidth shape =
        canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      LittleOLinear
        (compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hprofile :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile
      shape
  exact ⟨by
      simp [canonicalBPRelativeSummaryBlockSize, hactive],
    by
      simp [canonicalBPRelativeSummaryBlocksPerSuper, hactive],
    by
      simp [canonicalBPRelativeSummaryBlockCount, hactive],
    by
      simp [canonicalBPRelativeSummarySuperCount, hactive],
    by
      simp [canonicalBPRelativeSummaryRelativeWidth, hactive],
    by
      simpa [canonicalBPRelativeSummaryBlockSize,
        canonicalBPRelativeSummaryBlocksPerSuper,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummarySuperCount,
        canonicalBPRelativeSummaryRelativeWidth, hactive] using hprofile⟩

theorem canonicalBPRelativeSummaryBlockSizeRaw_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlockSizeRaw shape := by
  simp [canonicalBPRelativeSummaryBlockSizeRaw,
    canonicalBPRelativeSummaryBase]

theorem canonicalBPRelativeSummaryBlockSize_pos_of_active
    {shape : Cartesian.CartesianShape}
    (hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape) :
    0 < canonicalBPRelativeSummaryBlockSize shape := by
  simpa [canonicalBPRelativeSummaryBlockSize, hactive] using
    canonicalBPRelativeSummaryBlockSizeRaw_pos shape

theorem canonicalBPRelativeSummaryBlockSize_pos_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    0 < canonicalBPRelativeSummaryBlockSize shape :=
  canonicalBPRelativeSummaryBlockSize_pos_of_active
    (canonicalBPRelativeMinMaxArgSummaryTableActive_of_large hlarge)

theorem canonicalBPRelativeSummaryBlockSize_pos_of_size_ge
    {shape : Cartesian.CartesianShape}
    (hsize : 2 ^ 128 <= shape.size) :
    0 < canonicalBPRelativeSummaryBlockSize shape :=
  canonicalBPRelativeSummaryBlockSize_pos_of_large
    (canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize)

theorem canonicalBPRelativeSummaryBlocksPerSuperRaw_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape := by
  simp [canonicalBPRelativeSummaryBlocksPerSuperRaw,
    canonicalBPRelativeSummaryBase]

theorem canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape *
        canonicalBPRelativeSummaryBlockSizeRaw shape <=
      shape.bpCode.length :=
  canonicalBPRelativeSummary_raw_cover shape

theorem canonicalBPRelativeSummaryBlockCountRaw_pos_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    0 < canonicalBPRelativeSummaryBlockCountRaw shape := by
  rcases canonicalBPRelativeSummary_large_parts
      (shape := shape) hlarge with
    ⟨hbase_le_count, _hsuperWidth, _hspan, _harg, _hmachine⟩
  have hbase_pos : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  omega

theorem canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCountRaw shape <= shape.bpCode.length := by
  have hcover :=
    canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
      shape
  have hsize : 1 <= canonicalBPRelativeSummaryBlockSizeRaw shape :=
    Nat.succ_le_of_lt (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
  have hcount_le_mul :
      canonicalBPRelativeSummaryBlockCountRaw shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape := by
    calc
      canonicalBPRelativeSummaryBlockCountRaw shape =
          canonicalBPRelativeSummaryBlockCountRaw shape * 1 := by
        rw [Nat.mul_one]
      _ <=
          canonicalBPRelativeSummaryBlockCountRaw shape *
            canonicalBPRelativeSummaryBlockSizeRaw shape :=
        Nat.mul_le_mul_left
          (canonicalBPRelativeSummaryBlockCountRaw shape) hsize
  exact Nat.le_trans hcount_le_mul hcover

theorem canonicalBPRelativeSummaryBlockCount_le_bpCode_length
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCount shape <= shape.bpCode.length := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · simpa [canonicalBPRelativeSummaryBlockCount, hactive] using
      canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape
  · simp [canonicalBPRelativeSummaryBlockCount, hactive]

theorem canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    canonicalBPRelativeSummaryRelativeWidthRaw shape <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  rcases canonicalBPRelativeSummary_large_parts
      (shape := shape) hlarge with
    ⟨_hbase_le_count, _hsuperWidth, _hspan, _harg, hmachine⟩
  simpa [canonicalBPRelativeSummarySuperWidth] using hmachine

def concreteBPRelativeRmmInteriorLocalOffsetSlots : Nat := 64

def concreteBPRelativeRmmInteriorGlobalMacroSlots : Nat := 32

def concreteBPRelativeRmmInteriorNodeSlots : Nat :=
  concreteBPRelativeRmmInteriorLocalOffsetSlots

def concreteBPRelativeRmmInteriorTopSlots : Nat := 16

def concreteBPRelativeRmmInteriorQueryCost : Nat := 30

def concreteBPRelativeRmmInteriorMacroSize
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBase shape *
    canonicalBPRelativeSummaryBase shape

def concreteBPRelativeRmmInteriorMacroCount
    (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBlockCount shape /
      concreteBPRelativeRmmInteriorMacroSize shape + 1

def concreteBPRelativeRmmInteriorOffsetWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (concreteBPRelativeRmmInteriorMacroSize shape)

def concreteBPRelativeRmmInteriorLevelCount
    (shape : Cartesian.CartesianShape) : Nat :=
  concreteBPRelativeRmmInteriorOffsetWidth shape

def concreteBPRelativeRmmInteriorGlobalLevelCount
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (concreteBPRelativeRmmInteriorMacroCount shape)

def concreteBPRelativeRmmInteriorBlockWidth
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (canonicalBPRelativeSummaryBlockCount shape)

theorem concreteBPRelativeRmmInteriorMacroSize_pos
    (shape : Cartesian.CartesianShape) :
    0 < concreteBPRelativeRmmInteriorMacroSize shape := by
  unfold concreteBPRelativeRmmInteriorMacroSize
  have hbase : 0 < canonicalBPRelativeSummaryBase shape := by
    simp [canonicalBPRelativeSummaryBase]
  exact Nat.mul_pos hbase hbase

theorem concreteBPRelativeRmmInteriorOffsetWidth_capacity
    (shape : Cartesian.CartesianShape) :
    concreteBPRelativeRmmInteriorMacroSize shape <
      2 ^ concreteBPRelativeRmmInteriorOffsetWidth shape := by
  unfold concreteBPRelativeRmmInteriorOffsetWidth
  unfold SuccinctRank.machineWordBits
  exact Nat.lt_log2_self
    (n := concreteBPRelativeRmmInteriorMacroSize shape)

theorem concreteBPRelativeRmmInteriorBlockWidth_capacity
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockCount shape <
      2 ^ concreteBPRelativeRmmInteriorBlockWidth shape := by
  unfold concreteBPRelativeRmmInteriorBlockWidth
  unfold SuccinctRank.machineWordBits
  exact Nat.lt_log2_self
    (n := canonicalBPRelativeSummaryBlockCount shape)

theorem concreteBPRelativeRmmInteriorGlobalLevelCount_capacity
    (shape : Cartesian.CartesianShape) :
    concreteBPRelativeRmmInteriorMacroCount shape <
      2 ^ concreteBPRelativeRmmInteriorGlobalLevelCount shape := by
  unfold concreteBPRelativeRmmInteriorGlobalLevelCount
  unfold SuccinctRank.machineWordBits
  exact Nat.lt_log2_self
    (n := concreteBPRelativeRmmInteriorMacroCount shape)

theorem nat_succ_cube_le_two_pow_of_128_le
    (q : Nat) (hq : 128 <= q) :
    (q + 1) * ((q + 1) * (q + 1)) <= 2 ^ q := by
  exact Nat.strongRecOn q (fun q ih => by
    intro hq
    by_cases hstep : 131 <= q
    · have hprevLarge : 128 <= q - 3 := by
        omega
      have hprevLt : q - 3 < q := by
        omega
      have ihprev := ih (q - 3) hprevLt hprevLarge
      have hlin : q + 1 <= 2 * ((q - 3) + 1) := by
        omega
      have hcube :
          (q + 1) * ((q + 1) * (q + 1)) <=
            (2 * ((q - 3) + 1)) *
              ((2 * ((q - 3) + 1)) *
                (2 * ((q - 3) + 1))) := by
        exact Nat.mul_le_mul hlin (Nat.mul_le_mul hlin hlin)
      have hscaled :
          (2 * ((q - 3) + 1)) *
              ((2 * ((q - 3) + 1)) *
                (2 * ((q - 3) + 1))) =
            2 * (2 * (2 *
              (((q - 3) + 1) *
                (((q - 3) + 1) * ((q - 3) + 1))))) := by
        simp [Nat.mul_left_comm, Nat.mul_comm]
      have hpowMul :
          2 * (2 * (2 * 2 ^ (q - 3))) = 2 ^ q := by
        have hqeq : q = (q - 3) + 3 := by
          omega
        calc
          2 * (2 * (2 * 2 ^ (q - 3))) =
              2 ^ ((q - 3) + 3) := by
            simp [Nat.pow_succ, Nat.mul_comm]
          _ = 2 ^ q := by
            rw [← hqeq]
      have hprevScaled :
          2 * (2 * (2 *
              (((q - 3) + 1) *
                (((q - 3) + 1) * ((q - 3) + 1))))) <=
            2 * (2 * (2 * 2 ^ (q - 3))) := by
        exact Nat.mul_le_mul_left 2
          (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left 2 ihprev))
      exact Nat.le_trans hcube
        (by simpa [hscaled, hpowMul] using hprevScaled)
    · have hupper : q <= 130 := by
        omega
      have hq131 : q + 1 <= 131 := by
        omega
      have hcubeLe :
          (q + 1) * ((q + 1) * (q + 1)) <=
            131 * (131 * 131) := by
        exact Nat.mul_le_mul hq131 (Nat.mul_le_mul hq131 hq131)
      have hsmall : 131 * (131 * 131) <= 2 ^ 22 := by
        decide
      have hpow : 2 ^ 22 <= 2 ^ q :=
        Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
      exact Nat.le_trans hcubeLe (Nat.le_trans hsmall hpow)) hq

theorem concreteBPRelativeRmmInteriorMacroSize_le_blockCount_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    concreteBPRelativeRmmInteriorMacroSize shape <=
      canonicalBPRelativeSummaryBlockCount shape := by
  let base := canonicalBPRelativeSummaryBase shape
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlog128 : 128 <= Nat.log2 shape.size :=
    natLog2_ge_of_pow_le hsize
  have hcubePow :
      (Nat.log2 shape.size + 1) *
          ((Nat.log2 shape.size + 1) *
            (Nat.log2 shape.size + 1)) <=
        2 ^ Nat.log2 shape.size :=
    nat_succ_cube_le_two_pow_of_128_le
      (Nat.log2 shape.size) hlog128
  have hsizePos : shape.size ≠ 0 := by
    have hpow : 0 < 2 ^ 128 := Nat.pow_pos (by omega)
    exact Nat.ne_of_gt (Nat.lt_of_lt_of_le hpow hsize)
  have hcubeSize :
      base * (base * base) <= shape.size := by
    exact Nat.le_trans
      (by
        simpa [base, canonicalBPRelativeSummaryBase] using hcubePow)
      (Nat.log2_self_le hsizePos)
  have hraw :
      base * base <= canonicalBPRelativeSummaryBlockCountRaw shape := by
    unfold canonicalBPRelativeSummaryBlockCountRaw
    exact (Nat.le_div_iff_mul_le hbasePos).2
      (by
        simpa [base, canonicalBPRelativeSummaryBase, Nat.mul_assoc,
          Nat.mul_left_comm, Nat.mul_comm] using hcubeSize)
  simpa [concreteBPRelativeRmmInteriorMacroSize,
    canonicalBPRelativeSummaryBlockCount, canonicalBPRelativeSummaryBase,
    base, hactive, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
    hraw

theorem concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    concreteBPRelativeRmmInteriorMacroCount shape *
        concreteBPRelativeRmmInteriorMacroSize shape <=
      2 * canonicalBPRelativeSummaryBlockCount shape := by
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  have hmacroPos : 0 < macroSize := by
    simpa [macroSize] using
      concreteBPRelativeRmmInteriorMacroSize_pos shape
  have hmacroLe :
      macroSize <= blockCount := by
    simpa [blockCount, macroSize] using
      concreteBPRelativeRmmInteriorMacroSize_le_blockCount_of_size_ge
        shape hsize
  have hdivPos : 1 <= blockCount / macroSize :=
    (Nat.le_div_iff_mul_le hmacroPos).2
      (by simpa [Nat.mul_comm] using hmacroLe)
  have hsuccLe :
      blockCount / macroSize + 1 <= 2 * (blockCount / macroSize) := by
    omega
  have hmul :=
    Nat.mul_le_mul_right macroSize hsuccLe
  have hdiv :
      (blockCount / macroSize) * macroSize <= blockCount :=
    Nat.div_mul_le_self blockCount macroSize
  have htwice :=
    Nat.mul_le_mul_left 2 hdiv
  calc
    concreteBPRelativeRmmInteriorMacroCount shape *
        concreteBPRelativeRmmInteriorMacroSize shape =
        (blockCount / macroSize + 1) * macroSize := by
      simp [blockCount, macroSize,
        concreteBPRelativeRmmInteriorMacroCount]
    _ <= (2 * (blockCount / macroSize)) * macroSize := hmul
    _ = 2 * ((blockCount / macroSize) * macroSize) := by
      simp [Nat.mul_assoc]
    _ <= 2 * blockCount := htwice

theorem concreteBPRelativeRmmInteriorOffsetWidth_le_five_logBase
    (shape : Cartesian.CartesianShape) :
    concreteBPRelativeRmmInteriorOffsetWidth shape <=
      5 * (Nat.log2 (canonicalBPRelativeSummaryBase shape) + 1) := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hfour :=
    four_mul_square_lt_two_pow_two_log_succ_add_three base
  have hsqLeFour : base * base <= 2 * (2 * (base * base)) := by
    have hmul := Nat.mul_le_mul_right (base * base)
      (by decide : 1 <= 4)
    calc
      base * base <= 4 * (base * base) := by
        simpa using hmul
      _ = 2 * (2 * (base * base)) := by
        omega
  have hmacroRel :
      concreteBPRelativeRmmInteriorMacroSize shape <
        2 ^ (2 * logBase + 3) := by
    have hfour' :
        2 * (2 * (base * base)) < 2 ^ (2 * logBase + 3) := by
      simpa [logBase] using hfour
    have hmacroEq :
        concreteBPRelativeRmmInteriorMacroSize shape = base * base := by
      simp [concreteBPRelativeRmmInteriorMacroSize, base,
        canonicalBPRelativeSummaryBase]
    rw [hmacroEq]
    exact Nat.lt_of_le_of_lt hsqLeFour hfour'
  have hoffsetRel :
      concreteBPRelativeRmmInteriorOffsetWidth shape <=
        2 * logBase + 3 := by
    unfold concreteBPRelativeRmmInteriorOffsetWidth
    exact natLog2_succ_le_of_pos_lt_pow
      (concreteBPRelativeRmmInteriorMacroSize_pos shape)
      (by
        simpa [concreteBPRelativeRmmInteriorMacroSize, base,
          canonicalBPRelativeSummaryBase, logBase] using hmacroRel)
  have hlogPos : 1 <= logBase := by
    simp [logBase]
  have hrelFive : 2 * logBase + 3 <= 5 * logBase := by
    omega
  exact Nat.le_trans hoffsetRel hrelFive

theorem concreteBPRelativeRmmInteriorBlockWidth_le_base_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    concreteBPRelativeRmmInteriorBlockWidth shape <=
      canonicalBPRelativeSummaryBase shape := by
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hcountPos :
      0 < canonicalBPRelativeSummaryBlockCount shape := by
    exact Nat.lt_of_lt_of_le
      (concreteBPRelativeRmmInteriorMacroSize_pos shape)
      (concreteBPRelativeRmmInteriorMacroSize_le_blockCount_of_size_ge
        shape hsize)
  have hcountLeSize :
      canonicalBPRelativeSummaryBlockCount shape <= shape.size := by
    have hraw :
        canonicalBPRelativeSummaryBlockCountRaw shape <= shape.size := by
      unfold canonicalBPRelativeSummaryBlockCountRaw
      exact Nat.div_le_self _ _
    simpa [canonicalBPRelativeSummaryBlockCount, hactive] using hraw
  have hsizeLt :
      shape.size < 2 ^ canonicalBPRelativeSummaryBase shape := by
    unfold canonicalBPRelativeSummaryBase
    exact Nat.lt_log2_self (n := shape.size)
  have hcountLt :
      canonicalBPRelativeSummaryBlockCount shape <
        2 ^ canonicalBPRelativeSummaryBase shape :=
    Nat.lt_of_le_of_lt hcountLeSize hsizeLt
  unfold concreteBPRelativeRmmInteriorBlockWidth
  exact natLog2_succ_le_of_pos_lt_pow hcountPos hcountLt

theorem concreteBPRelativeRmmInteriorGlobalLevelCount_le_base_succ_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    concreteBPRelativeRmmInteriorGlobalLevelCount shape <=
      canonicalBPRelativeSummaryBase shape + 1 := by
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  have hmacroPos : 0 < macroSize := by
    simpa [macroSize] using
      concreteBPRelativeRmmInteriorMacroSize_pos shape
  have hmacroCountPos :
      0 < concreteBPRelativeRmmInteriorMacroCount shape := by
    simp [concreteBPRelativeRmmInteriorMacroCount]
  have hmacroLeBlockSucc :
      concreteBPRelativeRmmInteriorMacroCount shape <=
        blockCount + 1 := by
    have hdiv :
        canonicalBPRelativeSummaryBlockCount shape /
            concreteBPRelativeRmmInteriorMacroSize shape <=
          canonicalBPRelativeSummaryBlockCount shape := by
      exact Nat.div_le_self blockCount macroSize
    simpa [blockCount, macroSize,
      concreteBPRelativeRmmInteriorMacroCount] using
      Nat.succ_le_succ hdiv
  have hblockWidth :=
    concreteBPRelativeRmmInteriorBlockWidth_le_base_of_size_ge shape hsize
  have hblockLt :
      blockCount < 2 ^ canonicalBPRelativeSummaryBase shape := by
    unfold concreteBPRelativeRmmInteriorBlockWidth at hblockWidth
    have hcap :=
      concreteBPRelativeRmmInteriorBlockWidth_capacity shape
    exact Nat.lt_of_lt_of_le hcap
      (Nat.pow_le_pow_right (by omega : 0 < 2) hblockWidth)
  have hmacroLt :
      concreteBPRelativeRmmInteriorMacroCount shape <
        2 ^ (canonicalBPRelativeSummaryBase shape + 1) := by
    have hsuccLePow :
        blockCount + 1 <= 2 ^ canonicalBPRelativeSummaryBase shape := by
      omega
    have hpowStep :
        2 ^ canonicalBPRelativeSummaryBase shape <
          2 ^ (canonicalBPRelativeSummaryBase shape + 1) := by
      have hpos :
          0 < 2 ^ canonicalBPRelativeSummaryBase shape :=
        Nat.pow_pos (by omega)
      simp [Nat.pow_succ, hpos]
    exact Nat.lt_of_le_of_lt
      (Nat.le_trans hmacroLeBlockSucc hsuccLePow) hpowStep
  unfold concreteBPRelativeRmmInteriorGlobalLevelCount
  exact natLog2_succ_le_of_pos_lt_pow hmacroCountPos hmacroLt

/--
Canonical compact overhead envelope for the intended relative-rmM interior
navigator.

The first summand is the charged relative min/max/arg block summary table.  The
second summand reserves local-offset sparse tables over macroblocks, with
`log log n`-bit offsets across `log log n` levels.  The last two summands pay for
the global macroblock sparse table and top routing layer.  There is intentionally
no dense `interiorBlockPairRanges` or all-pairs range payload in this budget.
-/
def concreteBPRelativeRmmInteriorOverhead (n : Nat) : Nat :=
  compactBPCloseSummaryPayloadOverhead
      canonicalBPRelativeSummaryBlockSlots 0 0
      canonicalBPRelativeSummarySuperSlots n +
    logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots n +
      logLogSampledDirectoryOverhead
          concreteBPRelativeRmmInteriorGlobalMacroSlots n +
        sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots n

theorem concreteBPRelativeRmmInteriorOverhead_littleO :
    LittleOLinear concreteBPRelativeRmmInteriorOverhead := by
  unfold concreteBPRelativeRmmInteriorOverhead
  exact
    (((compactBPCloseSummaryPayloadOverhead_littleO
      canonicalBPRelativeSummaryBlockSlots 0 0
      canonicalBPRelativeSummarySuperSlots).add
      (logLogSquaredSampledDirectoryOverhead_littleO
        concreteBPRelativeRmmInteriorLocalOffsetSlots)).add
      (logLogSampledDirectoryOverhead_littleO
        concreteBPRelativeRmmInteriorGlobalMacroSlots)).add
      (sampledDirectoryOverhead_littleO
        concreteBPRelativeRmmInteriorTopSlots)

theorem concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large
    (shape : Cartesian.CartesianShape)
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    canonicalBPRelativeSummaryBlockSize shape =
        canonicalBPRelativeSummaryBlockSizeRaw shape /\
      canonicalBPRelativeSummaryBlocksPerSuper shape =
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      canonicalBPRelativeSummaryBlockCount shape =
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperCount shape =
        canonicalBPRelativeSummarySuperCountRaw shape /\
      canonicalBPRelativeSummaryRelativeWidth shape =
        canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      canonicalBPRelativeMinMaxArgSummaryTableActive shape /\
      0 < canonicalBPRelativeSummaryBlockSizeRaw shape /\
      0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      0 < canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryBlockCountRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      table.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  have hsummary :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large
      shape hlarge
  rcases hsummary with
    ⟨hblockSize, hblocksPerSuper, hblockCount, hsuperCount,
      hrelativeWidth, _hsummaryLittleO, hsummaryPayload, hsummaryExact,
      hbaselineRead, hminRead, hmaxRead, hargRead⟩
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hrelativeMachine :=
    canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large
      (shape := shape) hlarge
  have hpayloadLe :
      compactBPCloseSummaryPayloadOverhead
          canonicalBPRelativeSummaryBlockSlots 0 0
          canonicalBPRelativeSummarySuperSlots shape.size <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    unfold concreteBPRelativeRmmInteriorOverhead
    omega
  exact ⟨hblockSize, hblocksPerSuper, hblockCount, hsuperCount,
    hrelativeWidth, concreteBPRelativeRmmInteriorOverhead_littleO,
    hactive, canonicalBPRelativeSummaryBlockSizeRaw_pos shape,
    canonicalBPRelativeSummaryBlocksPerSuperRaw_pos shape,
    canonicalBPRelativeSummaryBlockCountRaw_pos_of_large
      (shape := shape) hlarge,
    canonicalBPRelativeSummaryBlockCountRaw_mul_blockSizeRaw_le_bpCode_length
      shape,
    canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape,
    hrelativeMachine, Nat.le_trans hsummaryPayload hpayloadLe,
    hsummaryExact, hbaselineRead, hminRead, hmaxRead, hargRead⟩

theorem concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    canonicalBPRelativeSummaryBlockSize shape =
        canonicalBPRelativeSummaryBlockSizeRaw shape /\
      canonicalBPRelativeSummaryBlocksPerSuper shape =
        canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      canonicalBPRelativeSummaryBlockCount shape =
        canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummarySuperCount shape =
        canonicalBPRelativeSummarySuperCountRaw shape /\
      canonicalBPRelativeSummaryRelativeWidth shape =
        canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      canonicalBPRelativeMinMaxArgSummaryTableActive shape /\
      0 < canonicalBPRelativeSummaryBlockSizeRaw shape /\
      0 < canonicalBPRelativeSummaryBlocksPerSuperRaw shape /\
      0 < canonicalBPRelativeSummaryBlockCountRaw shape /\
      canonicalBPRelativeSummaryBlockCountRaw shape *
          canonicalBPRelativeSummaryBlockSizeRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryBlockCountRaw shape <=
        shape.bpCode.length /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      table.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large
      shape
      (canonicalBPRelativeSummaryLargeRegime_of_size_ge
        (shape := shape) hsize)

/--
Two-level interior-navigator budget package for the canonical large regime.

This is the arithmetic surface the concrete rmM navigator should consume: it
charges the relative summary table, the local offset sparse tables, the global
macroblock sparse table, and the top routing reserve inside one `o(n)` envelope,
while also exposing the fixed-width read bounds needed by the charged summary
queries.
-/
theorem concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    let relativeSummaryBudget :=
      compactBPCloseSummaryPayloadOverhead
        canonicalBPRelativeSummaryBlockSlots 0 0
        canonicalBPRelativeSummarySuperSlots shape.size
    let localOffsetBudget :=
      logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size
    let globalMacroBudget :=
      logLogSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size
    let topRoutingBudget :=
      sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots shape.size
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      relativeSummaryBudget + localOffsetBudget +
          globalMacroBudget + topRoutingBudget =
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      table.payload.length + localOffsetBudget +
          globalMacroBudget + topRoutingBudget <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      canonicalBPRelativeMinMaxArgSummaryTableActive shape /\
      canonicalBPRelativeSummaryBlockSizeRaw shape <
        2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape /\
      canonicalBPRelativeSummaryRelativeWidthRaw shape <=
        SuccinctRank.machineWordBits shape.bpCode.length /\
      canonicalBPRelativeSummaryBlockCountRaw shape <
        2 ^ SuccinctRank.machineWordBits shape.bpCode.length /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            match
              (bpSuperblockBaselineEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummarySuperCountRaw shape))[
                  block /
                    canonicalBPRelativeSummaryBlocksPerSuperRaw shape]?,
              (bpBlockRelativeMinExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockRelativeMaxExcessEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlocksPerSuperRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?,
              (bpBlockArgMinLocalOffsetEntries shape
                (canonicalBPRelativeSummaryBlockSizeRaw shape)
                (canonicalBPRelativeSummaryBlockCountRaw shape))[block]?
            with
            | some baseline, some minRel, some maxRel, some argOffset =>
                some (baseline, minRel, maxRel, argOffset)
            | _, _, _, _ => none) /\
      (forall {index : Nat} {word : List Bool},
        table.baselineTable.store.words[index]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.minRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.maxRelTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argOffsetTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let relativeSummaryBudget :=
    compactBPCloseSummaryPayloadOverhead
      canonicalBPRelativeSummaryBlockSlots 0 0
      canonicalBPRelativeSummarySuperSlots shape.size
  let localOffsetBudget :=
    logLogSquaredSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size
  let globalMacroBudget :=
    logLogSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size
  let topRoutingBudget :=
    sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots shape.size
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hsummary :=
    concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large
      shape hlarge
  rcases hsummary with
    ⟨_hblockSize, _hblocksPerSuper, _hblockCount, _hsuperCount,
      _hrelativeWidth, _hsummaryLittleO, hsummaryPayload, hsummaryExact,
      hbaselineRead, hminRead, hmaxRead, hargRead⟩
  rcases canonicalBPRelativeSummary_large_parts
      (shape := shape) hlarge with
    ⟨_hbase_le_count, _hsuperWidth, _hspan, hargWidth,
      _hrelative_le_super⟩
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hrelativeMachine :=
    canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large
      (shape := shape) hlarge
  have hblockCountMachine :
      canonicalBPRelativeSummaryBlockCountRaw shape <
        2 ^ SuccinctRank.machineWordBits shape.bpCode.length := by
    have hcount :=
      canonicalBPRelativeSummaryBlockCountRaw_le_bpCode_length shape
    have hcapacity :
        shape.bpCode.length <
          2 ^ SuccinctRank.machineWordBits shape.bpCode.length := by
      unfold SuccinctRank.machineWordBits
      exact Nat.lt_log2_self (n := shape.bpCode.length)
    exact Nat.lt_of_le_of_lt hcount hcapacity
  have hbudgetEq :
      relativeSummaryBudget + localOffsetBudget +
          globalMacroBudget + topRoutingBudget =
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    rfl
  have hpayloadBudget :
      table.payload.length + localOffsetBudget +
          globalMacroBudget + topRoutingBudget <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    have hpayloadLeRelative :
        table.payload.length <= relativeSummaryBudget := by
      simpa [table, relativeSummaryBudget] using hsummaryPayload
    have hsum :
        table.payload.length + localOffsetBudget +
            globalMacroBudget + topRoutingBudget <=
          relativeSummaryBudget + localOffsetBudget +
            globalMacroBudget + topRoutingBudget := by
      omega
    simpa [hbudgetEq] using hsum
  exact ⟨concreteBPRelativeRmmInteriorOverhead_littleO, hbudgetEq,
    hpayloadBudget, hactive, hargWidth, hrelativeMachine,
    hblockCountMachine, hsummaryExact, hbaselineRead, hminRead, hmaxRead,
    hargRead⟩


end SuccinctCloseProposal
end RMQ
