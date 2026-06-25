import RMQ.Core.SuccinctClose.RangeWitness

/-!
# Endpoint-fringe BP range repair

Charged prefix-range witnesses, local/global sparse span helpers, and compact
endpoint-fringe repair components. The historical `RMQ.SuccinctCloseProposal`
namespace is preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

/-!
## Charged endpoint-fringe range repair

The block-pair macro above reads a real position-bearing payload entry, but it
ranges over whole endpoint blocks.  A close/LCA answer needs the exact prefix
interval from `leftClose + 1` through `rightClose + 1`.  The next layer stores
charged prefix-range witnesses for endpoint fringes and combines them with the
existing full-block range witness.
-/

def bpPrefixRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape) :
    Nat -> Nat -> Nat -> Nat
  | _pos, 0, best => best
  | pos, steps + 1, best =>
      let sample := Nat.min pos shape.bpCode.length
      let best' := bpBetterArgMinPrefixPos shape best sample
      bpPrefixRangeArgMinPrefixPosFrom shape (pos + 1) steps best'

theorem bpPrefixRangeArgMinPrefixPosFrom_le_length
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat)
    (hbest : best <= shape.bpCode.length) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best <=
      shape.bpCode.length := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpPrefixRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      exact ih (pos + 1)
        (bpBetterArgMinPrefixPos shape best
          (Nat.min pos shape.bpCode.length))
        (bpBetterArgMinPrefixPos_le_length shape hbest
          (Nat.min_le_right pos shape.bpCode.length))

theorem bpPrefixRangeArgMinPrefixPosFrom_excess_le_best
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat) :
    bpExcessAt shape
        (bpPrefixRangeArgMinPrefixPosFrom shape pos steps best) <=
      bpExcessAt shape best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      exact Nat.le_trans
        (ih (pos + 1)
          (bpBetterArgMinPrefixPos shape best
            (Nat.min pos shape.bpCode.length)))
        (bpExcessAt_bpBetterArgMinPrefixPos_le_left shape best
          (Nat.min pos shape.bpCode.length))

theorem bpPrefixRangeArgMinPrefixPosFrom_excess_le_pos_add
    (shape : Cartesian.CartesianShape)
    (pos steps best offset : Nat)
    (hoffset : offset < steps) :
    bpExcessAt shape
        (bpPrefixRangeArgMinPrefixPosFrom shape pos steps best) <=
      bpExcessAt shape (Nat.min (pos + offset) shape.bpCode.length) := by
  induction steps generalizing pos best offset with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      by_cases hzero : offset = 0
      · subst offset
        exact Nat.le_trans
          (bpPrefixRangeArgMinPrefixPosFrom_excess_le_best shape
            (pos + 1) steps
            (bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length)))
          (bpExcessAt_bpBetterArgMinPrefixPos_le_right shape best
            (Nat.min pos shape.bpCode.length))
      · have hoffsetTail : offset - 1 < steps := by
          omega
        have htail :=
          ih (pos + 1)
            (bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length))
            (offset - 1) hoffsetTail
        have hpos : pos + 1 + (offset - 1) = pos + offset := by
          omega
        simpa [hpos] using htail

theorem bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat)
    (hall :
      forall {offset : Nat},
        offset < steps ->
          bpExcessAt shape best <=
            bpExcessAt shape
              (Nat.min (pos + offset) shape.bpCode.length)) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best = best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hhead :
          bpBetterArgMinPrefixPos shape best
              (Nat.min pos shape.bpCode.length) = best := by
        exact bpBetterArgMinPrefixPos_eq_left_of_excess_le
          shape (hall (offset := 0) (by omega))
      simp [hhead]
      apply ih
      intro offset hoffset
      have htail := hall (offset := offset + 1) (by omega)
      have hpos :
          pos + (offset + 1) = pos + 1 + offset := by
        omega
      simpa [hpos] using htail

theorem bpPrefixRangeArgMinPrefixPosFrom_eq_of_leftmost_min_excess
    (shape : Cartesian.CartesianShape)
    {pos steps best target : Nat}
    (hbest :
      bpExcessAt shape target < bpExcessAt shape best)
    (hlo : pos <= target)
    (hhi : target < pos + steps)
    (hbound : pos + steps <= shape.bpCode.length + 1)
    (hmin :
      forall {sample : Nat},
        pos <= sample ->
          sample < pos + steps ->
            bpExcessAt shape target <= bpExcessAt shape sample)
    (hleft :
      forall {sample : Nat},
        pos <= sample ->
          sample < target ->
            bpExcessAt shape target < bpExcessAt shape sample) :
    bpPrefixRangeArgMinPrefixPosFrom shape pos steps best = target := by
  induction steps generalizing pos best with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hposLeLen : pos <= shape.bpCode.length := by
        omega
      have hsample :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLeLen
      by_cases hposEq : pos = target
      · subst target
        have hchoose :
            bpBetterArgMinPrefixPos shape best
                (Nat.min pos shape.bpCode.length) = pos := by
          rw [hsample]
          exact bpBetterArgMinPrefixPos_eq_right_of_excess_lt
            shape hbest
        simp [hchoose]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape (pos + 1) steps pos (by
              intro offset hoffset
              have hsampleLe :
                  pos + 1 + offset <= shape.bpCode.length := by
                omega
              have hsampleMin :
                  Nat.min (pos + 1 + offset)
                      shape.bpCode.length =
                    pos + 1 + offset :=
                Nat.min_eq_left hsampleLe
              rw [hsampleMin]
              exact hmin (by omega) (by omega))
      · have hposLt : pos < target := by
          omega
        have hsampleGt :
            bpExcessAt shape target <
              bpExcessAt shape
                (Nat.min pos shape.bpCode.length) := by
          rw [hsample]
          exact hleft (by omega) hposLt
        have hnextBest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (Nat.min pos shape.bpCode.length)) := by
          unfold bpBetterArgMinPrefixPos
          by_cases hlt :
              bpExcessAt shape
                  (Nat.min pos shape.bpCode.length) <
                bpExcessAt shape best
          · simp [hlt, hsampleGt]
          · simp [hlt, hbest]
        exact ih hnextBest
          (by omega)
          (by omega)
          (by omega)
          (by
            intro sample hslo hshi
            exact hmin (by omega) (by omega))
          (by
            intro sample hslo hshi
            exact hleft (by omega) hshi)

def bpPrefixRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (start count : Nat) : Nat :=
  match count with
  | 0 => Nat.min start shape.bpCode.length
  | steps + 1 =>
      bpPrefixRangeArgMinPrefixPosFrom shape (start + 1) steps
        (Nat.min start shape.bpCode.length)

theorem bpPrefixRangeArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape)
    (start count : Nat) :
    bpPrefixRangeArgMinPrefixPos shape start count <=
      shape.bpCode.length := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      exact Nat.min_le_right start shape.bpCode.length
  | succ steps =>
      exact bpPrefixRangeArgMinPrefixPosFrom_le_length shape
        (start + 1) steps (Nat.min start shape.bpCode.length)
        (Nat.min_le_right start shape.bpCode.length)

theorem bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpPrefixRangeArgMinPrefixPos shape start count = target := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartLeLen : start <= shape.bpCode.length := by
        omega
      have hstartMin :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLeLen
      by_cases htargetStart : target = start
      · subst target
        simp [hstartMin]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape (start + 1) steps start (by
              intro offset hoffset
              have hposLeLen :
                  start + 1 + offset <= shape.bpCode.length := by
                omega
              have hposMin :
                  Nat.min (start + 1 + offset)
                      shape.bpCode.length =
                    start + 1 + offset :=
                Nat.min_eq_left hposLeLen
              rw [hposMin]
              exact hmin (by omega) (by omega))
      · have hstartLt : start < target := by
          omega
        have hbest :
            bpExcessAt shape target < bpExcessAt shape start :=
          hleft (by omega) hstartLt
        simp [hstartMin]
        exact
          bpPrefixRangeArgMinPrefixPosFrom_eq_of_leftmost_min_excess
            shape hbest
            (by omega)
            (by omega)
            (by omega)
            (by
              intro pos hposLo hposHi
              exact hmin (by omega) (by omega))
          (by
            intro pos hposLo hposHi
            exact hleft (by omega) hposHi)

theorem bpPrefixRangeArgMinPrefixPosFrom_mem_range
    (shape : Cartesian.CartesianShape)
    {start pos steps best : Nat}
    (hbest : start <= best /\ best < pos + steps)
    (hpos : start <= pos)
    (hbound : pos + steps <= shape.bpCode.length + 1) :
    start <= bpPrefixRangeArgMinPrefixPosFrom shape pos steps best /\
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best <
        pos + steps := by
  induction steps generalizing pos best with
  | zero =>
      simpa [bpPrefixRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpPrefixRangeArgMinPrefixPosFrom
      have hposLeLen : pos <= shape.bpCode.length := by
        omega
      have hsample :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLeLen
      let next :=
        bpBetterArgMinPrefixPos shape best
          (Nat.min pos shape.bpCode.length)
      have hnext :
          start <= next /\ next < pos + 1 + steps := by
        unfold next bpBetterArgMinPrefixPos
        rw [hsample]
        by_cases hlt :
            bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt]
          omega
        · simp [hlt]
          omega
      have hrec :=
        ih (pos := pos + 1) (best := next)
          hnext (by omega) (by omega)
      simpa [next, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
        using hrec

theorem bpPrefixRangeArgMinPrefixPos_mem_range
    {shape : Cartesian.CartesianShape}
    {start count : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1) :
    start <= bpPrefixRangeArgMinPrefixPos shape start count /\
      bpPrefixRangeArgMinPrefixPos shape start count < start + count := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartLeLen : start <= shape.bpCode.length := by
        omega
      have hstartMin :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLeLen
      simp [hstartMin]
      have hmem :=
        bpPrefixRangeArgMinPrefixPosFrom_mem_range
          shape
          (start := start)
          (pos := start + 1)
          (steps := steps)
          (best := start)
          (by omega) (by omega) (by omega)
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hmem

theorem bpPrefixRangeArgMinPrefixPos_excess_le_offset
    (shape : Cartesian.CartesianShape)
    (start count offset : Nat)
    (hoffset : offset < count) :
    bpExcessAt shape (bpPrefixRangeArgMinPrefixPos shape start count) <=
      bpExcessAt shape (Nat.min (start + offset) shape.bpCode.length) := by
  unfold bpPrefixRangeArgMinPrefixPos
  cases count with
  | zero =>
      omega
  | succ steps =>
      cases offset with
      | zero =>
          simpa using
            (bpPrefixRangeArgMinPrefixPosFrom_excess_le_best shape
              (start + 1) steps
              (Nat.min start shape.bpCode.length))
      | succ offset =>
          have hoffsetTail : offset < steps := by
            omega
          have htail :=
            bpPrefixRangeArgMinPrefixPosFrom_excess_le_pos_add shape
              (start + 1) steps (Nat.min start shape.bpCode.length)
              offset hoffsetTail
          have hpos : start + 1 + offset = start + Nat.succ offset := by
            omega
          simpa [hpos] using htail

def bpPrefixRangeMinExcess
    (shape : Cartesian.CartesianShape)
    (start count : Nat) : Nat :=
  bpExcessAt shape (bpPrefixRangeArgMinPrefixPos shape start count)

theorem bpPrefixRangeMinExcess_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpPrefixRangeMinExcess shape start count =
      bpExcessAt shape target := by
  unfold bpPrefixRangeMinExcess
  rw [bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
    hmem hbound hmin hleft]

theorem bpPrefixRangeWitness_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {start count target : Nat}
    (hmem : start <= target /\ target < start + count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        start <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    (bpPrefixRangeMinExcess shape start count,
        bpPrefixRangeArgMinPrefixPos shape start count) =
      (bpExcessAt shape target, target) := by
  apply Prod.ext
  · exact
      bpPrefixRangeMinExcess_eq_of_leftmost_min_excess
        hmem hbound hmin hleft
  · exact
      bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
        hmem hbound hmin hleft

theorem bpBlockArgMinPrefixPosFrom_eq_prefixRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape)
    (pos steps best : Nat) :
    bpBlockArgMinPrefixPosFrom shape pos steps best =
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simp [bpBlockArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpBlockArgMinPrefixPosFrom
      unfold bpPrefixRangeArgMinPrefixPosFrom
      unfold bpBetterArgMinPrefixPos
      by_cases hlt :
          bpExcessAt shape (Nat.min pos shape.bpCode.length) <
            bpExcessAt shape best
      · simp [hlt, ih]
      · simp [hlt, ih]

theorem bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (blockSize block : Nat) :
    bpBlockArgMinPrefixPos shape blockSize block =
      bpPrefixRangeArgMinPrefixPos shape
        (blockStartOf blockSize block) (blockSize + 1) := by
  unfold bpBlockArgMinPrefixPos
  unfold bpPrefixRangeArgMinPrefixPos
  have hfirst :
      (if bpExcessAt shape
            (Nat.min (blockStartOf blockSize block)
              shape.bpCode.length) <
          bpExcessAt shape
            (Nat.min (blockStartOf blockSize block)
              shape.bpCode.length)
        then
          Nat.min (blockStartOf blockSize block) shape.bpCode.length
        else
          Nat.min (blockStartOf blockSize block)
            shape.bpCode.length) =
        Nat.min (blockStartOf blockSize block) shape.bpCode.length := by
    simp
  simp [bpBlockArgMinPrefixPosFrom,
    bpBlockArgMinPrefixPosFrom_eq_prefixRangeArgMinPrefixPosFrom]

theorem bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
    {shape : Cartesian.CartesianShape}
    {blockSize block target : Nat}
    (hmem :
      blockStartOf blockSize block <= target /\
        target < blockStartOf blockSize block + (blockSize + 1))
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1)
    (hmin :
      forall {pos : Nat},
        blockStartOf blockSize block <= pos ->
          pos < blockStartOf blockSize block + (blockSize + 1) ->
            bpExcessAt shape target <= bpExcessAt shape pos)
    (hleft :
      forall {pos : Nat},
        blockStartOf blockSize block <= pos ->
          pos < target ->
            bpExcessAt shape target < bpExcessAt shape pos) :
    bpBlockArgMinPrefixPos shape blockSize block = target := by
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  exact
    bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess
      hmem hbound hmin hleft

theorem bpBlockArgMinPrefixPos_mem_range
    {shape : Cartesian.CartesianShape}
    {blockSize block : Nat}
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize block <=
        bpBlockArgMinPrefixPos shape blockSize block /\
      bpBlockArgMinPrefixPos shape blockSize block <
        blockStartOf blockSize block + (blockSize + 1) := by
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  exact bpPrefixRangeArgMinPrefixPos_mem_range
    (shape := shape) (start := blockStartOf blockSize block)
    (count := blockSize + 1) (by omega) hbound

def bpRelativeSummaryMinCandidate
    (blockSize blocksPerSuper block : Nat)
    (summary : Nat × Nat × Nat × Nat) : Nat × Nat :=
  let baseline := summary.1
  let minRel := summary.2.1
  let argOffset := summary.2.2.2
  (baseline + minRel - bpSuperblockSpan blockSize blocksPerSuper,
    blockStartOf blockSize block + argOffset)

theorem bpRelativeExcessEntry_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper block value : Nat}
    (hlower :
      bpExcessAt shape
          (bpSuperblockStartPos blockSize blocksPerSuper block) <=
        value + bpSuperblockSpan blockSize blocksPerSuper) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpRelativeExcessEntry shape blockSize blocksPerSuper block value -
      bpSuperblockSpan blockSize blocksPerSuper =
        value := by
  unfold bpRelativeExcessEntry
  omega

theorem bpBlockRelativeMinExcess_decode
    (shape : Cartesian.CartesianShape)
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpExcessAt shape
        (bpSuperblockStartPos blockSize blocksPerSuper block) +
        bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
      bpSuperblockSpan blockSize blocksPerSuper =
        bpBlockMinExcess shape blockSize block := by
  exact bpRelativeExcessEntry_decode shape
    (bpBlockMinExcess_baseline_le_add_span
      shape hblocks hblock hcover)

theorem bpBlockArgMinLocalOffset_decode
    {shape : Cartesian.CartesianShape}
    {blockSize block : Nat}
    (hbound :
      blockStartOf blockSize block + (blockSize + 1) <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize block +
        bpBlockArgMinLocalOffset shape blockSize block =
      bpBlockArgMinPrefixPos shape blockSize block := by
  have hmem :=
    bpBlockArgMinPrefixPos_mem_range
      (shape := shape) (blockSize := blockSize) (block := block) hbound
  unfold bpBlockArgMinLocalOffset
  omega

theorem bpBlockArgMinPrefixPos_excess_le_offset
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block offset : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hoffset : offset <= blockSize) :
    bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
      bpExcessAt shape (blockStartOf blockSize block + offset) := by
  have hsampleLe :
      blockStartOf blockSize block + offset <= shape.bpCode.length := by
    have hblockLe :
        blockStartOf blockSize block + offset <= blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := offset) hblock hoffset
    exact Nat.le_trans hblockLe hcover
  rw [bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos]
  have hle :=
    bpPrefixRangeArgMinPrefixPos_excess_le_offset
      shape (blockStartOf blockSize block) (blockSize + 1) offset
      (by omega)
  simpa [Nat.min_eq_left hsampleLe] using hle

theorem bpBlockMinExcess_eq_excess_argMin
    (shape : Cartesian.CartesianShape)
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length) :
    bpBlockMinExcess shape blockSize block =
      bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) := by
  apply Nat.le_antisymm
  · have hbound :
        blockStartOf blockSize block + (blockSize + 1) <=
          shape.bpCode.length + 1 := by
      have hend :
          blockStartOf blockSize block + blockSize <=
            shape.bpCode.length := by
        have hblockEnd :
            blockStartOf blockSize block + blockSize <=
              blockCount * blockSize :=
          blockStart_add_offset_le_blockCount_mul
            (blockSize := blockSize) (blockCount := blockCount)
            (block := block) (offset := blockSize) hblock (by omega)
        exact Nat.le_trans hblockEnd hcover
      omega
    have hmem :=
      bpBlockArgMinPrefixPos_mem_range
        (shape := shape) (blockSize := blockSize) (block := block)
        hbound
    let offset := bpBlockArgMinPrefixPos shape blockSize block -
      blockStartOf blockSize block
    have hoffset : offset <= blockSize := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      have hlt :
          bpBlockArgMinPrefixPos shape blockSize block <
            blockStartOf blockSize block + (blockSize + 1) := hmem.2
      omega
    have hsample :
        blockStartOf blockSize block + offset =
          bpBlockArgMinPrefixPos shape blockSize block := by
      have hstart :
          blockStartOf blockSize block <=
            bpBlockArgMinPrefixPos shape blockSize block := hmem.1
      omega
    have hvalueMem :
        List.Mem
          (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize block))
          (bpBlockExcessSamples shape blockSize block) := by
      have hmemOffset :=
        bpBlockExcessSamples_offset_mem
          shape (blockSize := blockSize) (block := block)
          (offset := offset) hoffset
      simpa [hsample] using hmemOffset
    exact
      natListMinFrom_le_of_mem
        (seed := shape.bpCode.length) hvalueMem
  · unfold bpBlockMinExcess
    have hle :
        bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block) <=
          natListMinFrom shape.bpCode.length
            (bpBlockExcessSamples shape blockSize block) + 0 :=
      le_natListMinFrom_add_of_forall_mem
        (span := 0)
        (by
          exact bpExcessAt_le_length shape
            (bpBlockArgMinPrefixPos shape blockSize block))
        (by
          intro value hmem
          unfold bpBlockExcessSamples at hmem
          rcases List.mem_map.mp hmem with ⟨offset, hoffsetMem, hvalue⟩
          have hoffset : offset <= blockSize := by
            simp at hoffsetMem
            omega
          have harg :=
            bpBlockArgMinPrefixPos_excess_le_offset
              shape hblock hcover hoffset
          rw [← hvalue]
          omega)
    omega

theorem bpSuperblockBaselineEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper superCount super : Nat}
    (hsuper : super < superCount) :
    (bpSuperblockBaselineEntries shape blockSize blocksPerSuper
        superCount)[super]? =
      some
        (bpExcessAt shape
          (blockStartOf blockSize (super * blocksPerSuper))) := by
  have hget :
      (List.range superCount)[super]? = some super :=
    List.getElem?_range hsuper
  simp [bpSuperblockBaselineEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMinExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMinExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMinExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMinExcessEntries, List.getElem?_map, hget]

theorem bpBlockRelativeMaxExcessEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockRelativeMaxExcessEntries shape blockSize blocksPerSuper
        blockCount)[block]? =
      some
        (bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockRelativeMaxExcessEntries, List.getElem?_map, hget]

theorem bpBlockArgMinLocalOffsetEntries_get?_of_lt
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount block : Nat}
    (hblock : block < blockCount) :
    (bpBlockArgMinLocalOffsetEntries shape blockSize blockCount)[block]? =
      some (bpBlockArgMinLocalOffset shape blockSize block) := by
  have hget :
      (List.range blockCount)[block]? = some block :=
    List.getElem?_range hblock
  simp [bpBlockArgMinLocalOffsetEntries, List.getElem?_map, hget]

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def minCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.map
    (fun summary? =>
      summary?.map
        (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block))
    (table.summaryCosted block)

theorem minCandidateCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost <= 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_le_four block

theorem summaryCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.summaryCosted block).cost = 4 := by
  unfold summaryCosted
  cases (table.baselineTable.readCosted (block / blocksPerSuper)).value
  <;> cases (table.minRelTable.readCosted block).value
  <;> cases (table.maxRelTable.readCosted block).value
  <;> simp [Costed.bind, Costed.map]

theorem minCandidateCosted_cost_eq_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) :
    (table.minCandidateCosted block).cost = 4 := by
  simpa [minCandidateCosted, Costed.map_cost] using
    table.summaryCosted_cost_eq_four block

theorem summaryCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblock : block < blockCount)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.summaryCosted block).erase =
      some
        (bpExcessAt shape
            (blockStartOf blockSize
              ((block / blocksPerSuper) * blocksPerSuper)),
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block,
          bpBlockRelativeMaxExcess shape blockSize blocksPerSuper block,
          bpBlockArgMinLocalOffset shape blockSize block) := by
  rw [table.summaryCosted_erase]
  simp [bpSuperblockBaselineEntries_get?_of_lt hsuper,
    bpBlockRelativeMinExcessEntries_get?_of_lt hblock,
    bpBlockRelativeMaxExcessEntries_get?_of_lt hblock,
    bpBlockArgMinLocalOffsetEntries_get?_of_lt hblock]

theorem minCandidateCosted_erase_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpBlockMinExcess shape blockSize block,
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hsummary :=
    table.summaryCosted_erase_of_bounds hblock hsuper
  have hmin :=
    bpBlockRelativeMinExcess_decode
      shape hblocks hblock hcover
  have hmin' :
      bpExcessAt shape
          (blockStartOf blockSize
            (block / blocksPerSuper * blocksPerSuper)) +
          bpBlockRelativeMinExcess shape blockSize blocksPerSuper block -
        bpSuperblockSpan blockSize blocksPerSuper =
          bpBlockMinExcess shape blockSize block := by
    simpa [bpSuperblockStartPos, bpSuperblockStartBlock] using hmin
  have hblockEnd :
      blockStartOf blockSize block + blockSize <=
        shape.bpCode.length := by
    have hend :
        blockStartOf blockSize block + blockSize <=
          blockCount * blockSize :=
      blockStart_add_offset_le_blockCount_mul
        (blockSize := blockSize) (blockCount := blockCount)
        (block := block) (offset := blockSize) hblock (by omega)
    exact Nat.le_trans hend hcover
  have harg :=
    bpBlockArgMinLocalOffset_decode
      (shape := shape) (blockSize := blockSize) (block := block)
      (by omega)
  unfold minCandidateCosted
  simp [Costed.erase_map, hsummary, bpRelativeSummaryMinCandidate,
    hmin', harg]

theorem minCandidateCosted_erase_arg_excess_of_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hblock : block < blockCount)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuper : block / blocksPerSuper < superCount) :
    (table.minCandidateCosted block).erase =
      some
        (bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block),
          bpBlockArgMinPrefixPos shape blockSize block) := by
  have hread :=
    table.minCandidateCosted_erase_of_bounds
      hblocks hblock hcover hsuper
  have hmin :=
    bpBlockMinExcess_eq_excess_argMin
      shape hblock hcover
  simpa [hmin] using hread

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best : Nat)
    (hall :
      forall {offset : Nat},
        offset < steps ->
          bpExcessAt shape best <=
            bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize
                (block + offset))) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best = best := by
  induction steps generalizing block best with
  | zero =>
      simp [bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      have hhead :
          bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block) = best := by
        exact bpBetterArgMinPrefixPos_eq_left_of_excess_le
          shape (hall (offset := 0) (by omega))
      simp [hhead]
      apply ih
      intro offset hoffset
      have htail := hall (offset := offset + 1) (by omega)
      have hblock :
          block + (offset + 1) = block + 1 + offset := by
        omega
      simpa [hblock] using htail

theorem bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
    (shape : Cartesian.CartesianShape)
    {blockSize block steps best targetBlock target : Nat}
    (hbest :
      bpExcessAt shape target < bpExcessAt shape best)
    (hlo : block <= targetBlock)
    (hhi : targetBlock < block + steps)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < block + steps ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        block <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best =
      target := by
  induction steps generalizing block best with
  | zero =>
      omega
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      by_cases hblockEq : block = targetBlock
      · subst targetBlock
        have hchoose :
            bpBetterArgMinPrefixPos shape best
                (bpBlockArgMinPrefixPos shape blockSize block) =
              target := by
          rw [htarget]
          exact bpBetterArgMinPrefixPos_eq_right_of_excess_lt
            shape hbest
        simp [hchoose]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (block + 1) steps target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hblockLt : block < targetBlock := by
          omega
        have hcandidateGt :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block) :=
          hleft (by omega) hblockLt
        have hnextBest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
          by_cases hlt :
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block) <
                bpExcessAt shape best
          · rw [bpBetterArgMinPrefixPos_eq_right_of_excess_lt
              shape hlt]
            exact hcandidateGt
          · have hle :
                bpExcessAt shape best <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize block) :=
              Nat.le_of_not_gt hlt
            rw [bpBetterArgMinPrefixPos_eq_left_of_excess_le
              shape hle]
            exact hbest
        exact ih
          (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          hnextBest
          (by omega)
          (by omega)
          (by
            intro candidateBlock hlo' hhi'
            exact hmin (by omega) (by omega))
          (by
            intro candidateBlock hlo' hlt'
            exact hleft (by omega) hlt')

theorem bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeArgMinPrefixPos shape blockSize startBlock blockCount =
      target := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      by_cases htargetStart : targetBlock = startBlock
      · subst targetBlock
        rw [htarget]
        exact
          bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all
            shape blockSize (startBlock + 1) count target (by
              intro offset hoffset
              exact hmin (by omega) (by omega))
      · have hstartLt : startBlock < targetBlock := by
          omega
        have hbest :
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock) :=
          hleft (by omega) hstartLt
        exact
          bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate
            shape hbest
            (by omega)
            (by omega)
            htarget
            (by
              intro candidateBlock hlo hhi
              exact hmin (by omega) (by omega))
            (by
              intro candidateBlock hlo hlt
              exact hleft (by omega) hlt)

theorem bpRangeMinExcess_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    bpRangeMinExcess shape blockSize startBlock blockCount =
      bpExcessAt shape target := by
  unfold bpRangeMinExcess
  rw [bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
    hblock htarget hmin hleft]

theorem bpRangeWitness_eq_of_leftmost_block_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount targetBlock target : Nat}
    (hblock : startBlock <= targetBlock /\
      targetBlock < startBlock + blockCount)
    (htarget :
      bpBlockArgMinPrefixPos shape blockSize targetBlock = target)
    (hmin :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape target <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock))
    (hleft :
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < targetBlock ->
            bpExcessAt shape target <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize
                  candidateBlock)) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape target, target) := by
  apply Prod.ext
  · exact
      bpRangeMinExcess_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft
  · exact
      bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate
        hblock htarget hmin hleft

/--
Choose the better block-minimum candidate by comparing the excess attained at
each block's stored argmin prefix.  Ties keep the left block, matching the
leftmost policy used by `bpBetterArgMinPrefixPos`.
-/
def bpBetterArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) : Nat :=
  if bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock) then
    rightBlock
  else
    leftBlock

theorem bpBetterArgMinBlock_eq_left_of_excess_le
    (shape : Cartesian.CartesianShape)
    {blockSize leftBlock rightBlock : Nat}
    (hle :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock)) :
    bpBetterArgMinBlock shape blockSize leftBlock rightBlock = leftBlock := by
  unfold bpBetterArgMinBlock
  have hnot :
      ¬ bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
    omega
  simp [hnot]

theorem bpBetterArgMinBlock_eq_right_of_excess_lt
    (shape : Cartesian.CartesianShape)
    {blockSize leftBlock rightBlock : Nat}
    (hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)) :
    bpBetterArgMinBlock shape blockSize leftBlock rightBlock = rightBlock := by
  simp [bpBetterArgMinBlock, hlt]

theorem bpExcessAt_bpBetterArgMinBlock_le_left
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize
          (bpBetterArgMinBlock shape blockSize leftBlock rightBlock)) <=
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
  unfold bpBetterArgMinBlock
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt, Nat.le_of_lt hlt]
  · simp [hlt]

theorem bpExcessAt_bpBetterArgMinBlock_le_right
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize
          (bpBetterArgMinBlock shape blockSize leftBlock rightBlock)) <=
      bpExcessAt shape
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
  unfold bpBetterArgMinBlock
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt]
  · have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt hlt
    simp [hlt, hle]

def bpRangeArgMinBlockFrom
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock : Nat) : Nat :=
  match steps with
  | 0 => bestBlock
  | steps + 1 =>
      let best' :=
        bpBetterArgMinBlock shape blockSize bestBlock block
      bpRangeArgMinBlockFrom shape blockSize (block + 1) steps best'

def bpRangeArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  match blockCount with
  | 0 => startBlock
  | count + 1 =>
      bpRangeArgMinBlockFrom shape blockSize (startBlock + 1) count
        startBlock

theorem bpBlockArgMinPrefixPos_bpBetterArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize leftBlock rightBlock : Nat) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpBetterArgMinBlock shape blockSize leftBlock rightBlock) =
      bpBetterArgMinPrefixPos shape
        (bpBlockArgMinPrefixPos shape blockSize leftBlock)
        (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
  unfold bpBetterArgMinBlock bpBetterArgMinPrefixPos
  by_cases hlt :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · simp [hlt]
  · simp [hlt]

theorem bpBlockArgMinPrefixPos_bpRangeArgMinBlockFrom
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock : Nat) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpRangeArgMinBlockFrom shape blockSize block steps bestBlock) =
      bpRangeArgMinPrefixPosFrom shape blockSize block steps
        (bpBlockArgMinPrefixPos shape blockSize bestBlock) := by
  induction steps generalizing block bestBlock with
  | zero =>
      simp [bpRangeArgMinBlockFrom, bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom bpRangeArgMinPrefixPosFrom
      simpa [bpBlockArgMinPrefixPos_bpBetterArgMinBlock] using
        ih (block + 1)
          (bpBetterArgMinBlock shape blockSize bestBlock block)

theorem bpBlockArgMinPrefixPos_bpRangeArgMinBlock_of_pos
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    bpBlockArgMinPrefixPos shape blockSize
        (bpRangeArgMinBlock shape blockSize startBlock blockCount) =
      bpRangeArgMinPrefixPos shape blockSize startBlock blockCount := by
  unfold bpRangeArgMinBlock bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      exact
        bpBlockArgMinPrefixPos_bpRangeArgMinBlockFrom
          shape blockSize (startBlock + 1) count startBlock

theorem bpRangeArgMinBlockFrom_mem
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock lo hi : Nat)
    (hbest : lo <= bestBlock /\ bestBlock < hi)
    (hcandidate :
      forall {offset : Nat}, offset < steps ->
        lo <= block + offset /\ block + offset < hi) :
    lo <= bpRangeArgMinBlockFrom shape blockSize block steps bestBlock /\
      bpRangeArgMinBlockFrom shape blockSize block steps bestBlock < hi := by
  induction steps generalizing block bestBlock with
  | zero =>
      simpa [bpRangeArgMinBlockFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom
      let next := bpBetterArgMinBlock shape blockSize bestBlock block
      have hcandidate0 : lo <= block /\ block < hi := by
        simpa using hcandidate (offset := 0) (by omega)
      have hnext : lo <= next /\ next < hi := by
        unfold next bpBetterArgMinBlock
        by_cases hlt :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [hlt, hcandidate0]
        · simp [hlt, hbest]
      exact
        ih (block := block + 1)
          (bestBlock := next)
          hnext
          (by
            intro offset hoffset
            have htail := hcandidate (offset := offset + 1) (by omega)
            have hblock :
                block + (offset + 1) = block + 1 + offset := by
              omega
            simpa [hblock] using htail)

theorem bpRangeArgMinBlock_mem
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    startBlock <=
        bpRangeArgMinBlock shape blockSize startBlock blockCount /\
      bpRangeArgMinBlock shape blockSize startBlock blockCount <
        startBlock + blockCount := by
  unfold bpRangeArgMinBlock
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      exact
        bpRangeArgMinBlockFrom_mem shape blockSize (startBlock + 1)
          count startBlock startBlock (startBlock + (count + 1))
          (by omega)
          (by
            intro offset hoffset
            omega)

theorem bpRangeArgMinBlockFrom_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize block steps bestBlock lo hi : Nat)
    (hbestMem : lo <= bestBlock /\ bestBlock < hi)
    (hbestBefore : bestBlock < block)
    (hbestLe :
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < block ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock))
    (hbestLeft :
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < bestBlock ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock))
    (hcandidate :
      forall {offset : Nat},
        offset < steps -> lo <= block + offset /\ block + offset < hi) :
    let target :=
      bpRangeArgMinBlockFrom shape blockSize block steps bestBlock
    lo <= target /\ target < hi /\ target < block + steps /\
      (forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < block + steps ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        lo <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  induction steps generalizing block bestBlock with
  | zero =>
      simp [bpRangeArgMinBlockFrom]
      exact
        ⟨hbestMem.1, hbestMem.2, hbestBefore,
          (by
            intro candidateBlock hlo hlt
            exact hbestLe hlo hlt),
          hbestLeft⟩
  | succ steps ih =>
      unfold bpRangeArgMinBlockFrom
      let current := block
      let best' := bpBetterArgMinBlock shape blockSize bestBlock current
      have hcurrentMem : lo <= current /\ current < hi := by
        simpa [current] using hcandidate (offset := 0) (by omega)
      have htailCandidate :
          forall {offset : Nat},
            offset < steps ->
              lo <= block + 1 + offset /\
                block + 1 + offset < hi := by
        intro offset hoffset
        have htail := hcandidate (offset := offset + 1) (by omega)
        have hpos : block + (offset + 1) = block + 1 + offset := by
          omega
        simpa [hpos] using htail
      have hbest'Mem : lo <= best' /\ best' < hi := by
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake, hcurrentMem]
        · simp [htake, hbestMem]
      have hbest'Before : best' < block + 1 := by
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake, current]
        · simp [htake]
          omega
      have hbest'Le :
          forall {candidateBlock : Nat},
            lo <= candidateBlock ->
              candidateBlock < block + 1 ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize best') <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
        intro candidateBlock hlo hltBlock
        unfold best' bpBetterArgMinBlock
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake]
          by_cases hcandidateCurrent : candidateBlock = current
          · subst candidateBlock
            exact Nat.le_refl _
          · have hcandidateBefore : candidateBlock < block := by
              omega
            exact Nat.le_trans (Nat.le_of_lt htake)
              (hbestLe hlo hcandidateBefore)
        · simp [htake]
          by_cases hcandidateCurrent : candidateBlock = current
          · subst candidateBlock
            exact Nat.le_of_not_gt htake
          · have hcandidateBefore : candidateBlock < block := by
              omega
            exact hbestLe hlo hcandidateBefore
      have hbest'Left :
          forall {candidateBlock : Nat},
            lo <= candidateBlock ->
              candidateBlock < best' ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize best') <
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
        intro candidateBlock hlo hltBest
        unfold best' bpBetterArgMinBlock at hltBest ⊢
        by_cases htake :
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize current) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize bestBlock)
        · simp [htake] at hltBest ⊢
          have hcandidateBefore : candidateBlock < block := by
            omega
          exact Nat.lt_of_lt_of_le htake
            (hbestLe hlo hcandidateBefore)
        · simp [htake] at hltBest ⊢
          exact hbestLeft hlo hltBest
      have hrec :=
        ih (block := block + 1) (bestBlock := best')
          hbest'Mem hbest'Before hbest'Le hbest'Left htailCandidate
      have hsteps : 1 + steps = steps + 1 := by omega
      simpa [best', current, hsteps, Nat.add_assoc] using hrec

theorem bpRangeArgMinBlock_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    let target := bpRangeArgMinBlock shape blockSize startBlock blockCount
    startBlock <= target /\ target < startBlock + blockCount /\
      (forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  unfold bpRangeArgMinBlock
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      have hfrom :=
        bpRangeArgMinBlockFrom_leftmost
          shape blockSize (startBlock + 1) count startBlock
          startBlock (startBlock + (count + 1))
          (by omega)
          (by omega)
          (by
            intro candidateBlock hlo hlt
            have hcandidate : candidateBlock = startBlock := by omega
            subst candidateBlock
            exact Nat.le_refl _)
          (by
            intro candidateBlock hlo hlt
            omega)
          (by
            intro offset hoffset
            omega)
      rcases hfrom with ⟨hlo, hhi, _htargetLt, hle, hleft⟩
      have hle' :
          forall {candidateBlock : Nat},
            startBlock <= candidateBlock ->
              candidateBlock < startBlock + (count + 1) ->
                bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize
                      (bpRangeArgMinBlockFrom shape blockSize
                        (startBlock + 1) count startBlock)) <=
                  bpExcessAt shape
                    (bpBlockArgMinPrefixPos shape blockSize
                      candidateBlock) := by
        intro candidateBlock hloCandidate hltCandidate
        exact hle hloCandidate (by omega)
      exact ⟨hlo, hhi, hle', hleft⟩

def bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat) : Nat :=
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightStart := startBlock + blockCount - span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  bpBetterArgMinBlock shape blockSize leftBlock rightBlock

theorem bpSparseTwoSpanArgMinBlock_leftmost
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span)
    (hspanLe : span <= blockCount)
    (hcover : blockCount <= 2 * span) :
    let target :=
      bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span
    startBlock <= target /\ target < startBlock + blockCount /\
      (forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < startBlock + blockCount ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <=
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock)) /\
      forall {candidateBlock : Nat},
        startBlock <= candidateBlock ->
          candidateBlock < target ->
            bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize target) <
              bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightStart := startBlock + blockCount - span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  have hleft :=
    bpRangeArgMinBlock_leftmost shape blockSize startBlock span hspan
  have hright :=
    bpRangeArgMinBlock_leftmost shape blockSize rightStart span hspan
  have hrightStart_ge : startBlock <= rightStart := by
    omega
  have hrightStart_le_leftEnd : rightStart <= startBlock + span := by
    omega
  have hrightEnd : rightStart + span = startBlock + blockCount := by
    omega
  by_cases htake :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          rightBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hmem :
        startBlock <= rightBlock /\ rightBlock < startBlock + blockCount := by
      constructor
      · exact Nat.le_trans hrightStart_ge hright.1
      · simpa [hrightEnd] using hright.2.1
    have hle :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < startBlock + blockCount ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize rightBlock) <=
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hhi
      by_cases hrightSide : rightStart <= candidateBlock
      · exact hright.2.2.1 hrightSide (by simpa [hrightEnd] using hhi)
      · have hcandidateLeft : candidateBlock < startBlock + span := by
          omega
        exact Nat.le_trans (Nat.le_of_lt htake)
          (hleft.2.2.1 hlo hcandidateLeft)
    have hleftmost :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < rightBlock ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hltTarget
      by_cases hrightSide : rightStart <= candidateBlock
      · exact hright.2.2.2 hrightSide hltTarget
      · have hcandidateLeft : candidateBlock < startBlock + span := by
          omega
        exact Nat.lt_of_lt_of_le htake
          (hleft.2.2.1 hlo hcandidateLeft)
    simpa [htarget] using ⟨hmem.1, hmem.2, hle, hleftmost⟩
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          leftBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hrightNotLt :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt htake
    have hmem :
        startBlock <= leftBlock /\ leftBlock < startBlock + blockCount := by
      constructor
      · exact hleft.1
      · have hleftHi := hleft.2.1
        omega
    have hle :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < startBlock + blockCount ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hhi
      by_cases hleftSide : candidateBlock < startBlock + span
      · exact hleft.2.2.1 hlo hleftSide
      · have hrightSide : rightStart <= candidateBlock := by omega
        exact Nat.le_trans hrightNotLt
          (hright.2.2.1 hrightSide (by simpa [hrightEnd] using hhi))
    have hleftmost :
        forall {candidateBlock : Nat},
          startBlock <= candidateBlock ->
            candidateBlock < leftBlock ->
              bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize leftBlock) <
                bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize candidateBlock) := by
      intro candidateBlock hlo hltTarget
      exact hleft.2.2.2 hlo hltTarget
    simpa [htarget] using ⟨hmem.1, hmem.2, hle, hleftmost⟩

theorem bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span)
    (hspanLe : span <= blockCount)
    (hcover : blockCount <= 2 * span) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
            blockCount span)) := by
  have hleftmost :=
    bpSparseTwoSpanArgMinBlock_leftmost
      shape blockSize startBlock blockCount span hspan hspanLe hcover
  exact
    bpRangeWitness_eq_of_leftmost_block_candidate
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      (targetBlock :=
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span)
      (target :=
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
            blockCount span))
      ⟨hleftmost.1, hleftmost.2.1⟩
      rfl
      hleftmost.2.2.1
      hleftmost.2.2.2

def bpSparseLogSpan (blockCount : Nat) : Nat :=
  2 ^ Nat.log2 blockCount

theorem bpSparseLogSpan_pos (blockCount : Nat) :
    0 < bpSparseLogSpan blockCount := by
  unfold bpSparseLogSpan
  exact Nat.pow_pos (by omega)

theorem bpSparseLogSpan_le_self
    {blockCount : Nat} (hcount : 0 < blockCount) :
    bpSparseLogSpan blockCount <= blockCount := by
  unfold bpSparseLogSpan
  exact Nat.log2_self_le (by omega)

theorem self_le_two_mul_bpSparseLogSpan
    {blockCount : Nat} (_hcount : 0 < blockCount) :
    blockCount <= 2 * bpSparseLogSpan blockCount := by
  unfold bpSparseLogSpan
  have hlt :
      blockCount < 2 ^ (Nat.log2 blockCount + 1) :=
    Nat.lt_log2_self (n := blockCount)
  have hpow :
      2 ^ (Nat.log2 blockCount + 1) =
        2 * 2 ^ Nat.log2 blockCount := by
    rw [Nat.pow_succ]
    omega
  omega

def bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount
    (bpSparseLogSpan blockCount)

theorem bpRangeWitness_eq_of_bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpSparseLogSpanArgMinBlock shape blockSize startBlock
            blockCount)) := by
  unfold bpSparseLogSpanArgMinBlock
  exact
    bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
      shape blockSize startBlock blockCount
      (bpSparseLogSpan blockCount)
      (bpSparseLogSpan_pos blockCount)
      (bpSparseLogSpan_le_self hcount)
      (self_le_two_mul_bpSparseLogSpan hcount)

def bpLocalSparseCellSlot
    (macroSize levelCount macroIdx localStart level : Nat) : Nat :=
  macroIdx * (levelCount * macroSize) + level * macroSize + localStart

def bpLocalSparseCellOffset
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroIdx localStart level : Nat) :
    Nat :=
  let span := 2 ^ level
  let macroStart := macroIdx * macroSize
  let startBlock := macroStart + localStart
  if localStart + span <= macroSize ∧ startBlock + span <= blockCount then
    bpRangeArgMinBlock shape blockSize startBlock span - macroStart
  else
    0

def bpLocalSparseOffsetEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    List Nat :=
  (List.range (macroCount * (levelCount * macroSize))).map fun slot =>
    let perMacro := levelCount * macroSize
    let macroIdx := slot / perMacro
    let rem := slot % perMacro
    let level := rem / macroSize
    let localStart := rem % macroSize
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level

theorem bpLocalSparseCellSlot_lt
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level <
      macroCount * (levelCount * macroSize) := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  have hslot :
      macroIdx * (levelCount * macroSize) +
          (level * macroSize + localStart) <
        macroIdx * (levelCount * macroSize) +
          (levelCount * macroSize) :=
    Nat.add_lt_add_left hcell (macroIdx * (levelCount * macroSize))
  have hsucc :
      macroIdx * (levelCount * macroSize) +
          levelCount * macroSize =
        (macroIdx + 1) * (levelCount * macroSize) := by
    simpa using
      (Nat.succ_mul macroIdx (levelCount * macroSize)).symm
  have hmul :
      (macroIdx + 1) * (levelCount * macroSize) <=
        macroCount * (levelCount * macroSize) :=
    Nat.mul_le_mul_right (levelCount * macroSize)
      (Nat.succ_le_of_lt hmacro)
  exact Nat.lt_of_lt_of_le (by simpa [Nat.add_assoc, hsucc] using hslot) hmul

theorem bpLocalSparseCellSlot_div_perMacro
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (_hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level /
        (levelCount * macroSize) =
      macroIdx := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  have hpos : 0 < levelCount * macroSize := by omega
  rw [Nat.mul_comm macroIdx (levelCount * macroSize)]
  rw [Nat.add_assoc]
  rw [Nat.mul_add_div hpos]
  rw [Nat.div_eq_of_lt hcell]
  omega

theorem bpLocalSparseCellSlot_mod_perMacro
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (_hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize) =
      level * macroSize + localStart := by
  unfold bpLocalSparseCellSlot
  have hcell :
      level * macroSize + localStart < levelCount * macroSize := by
    have hstep :
        level * macroSize + localStart <
          level * macroSize + macroSize :=
      Nat.add_lt_add_left hlocal (level * macroSize)
    have hsucc :
        level * macroSize + macroSize =
          (level + 1) * macroSize := by
      simpa using (Nat.succ_mul level macroSize).symm
    have hmul :
        (level + 1) * macroSize <= levelCount * macroSize :=
      Nat.mul_le_mul_right macroSize (Nat.succ_le_of_lt hlevel)
    exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul
  rw [Nat.mul_comm macroIdx (levelCount * macroSize)]
  rw [Nat.add_assoc]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hcell

theorem bpLocalSparseCellSlot_rem_div
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize)) / macroSize =
      level := by
  have hrem :=
    bpLocalSparseCellSlot_mod_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hdiv :
      (level * macroSize + localStart) / macroSize = level := by
    have hpos : 0 < macroSize := by omega
    rw [Nat.mul_comm level macroSize]
    rw [Nat.mul_add_div hpos]
    rw [Nat.div_eq_of_lt hlocal]
    omega
  simpa [hrem] using hdiv

theorem bpLocalSparseCellSlot_rem_mod
    {macroSize levelCount macroCount macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level %
        (levelCount * macroSize)) % macroSize =
      localStart := by
  have hrem :=
    bpLocalSparseCellSlot_mod_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hmod :
      (level * macroSize + localStart) % macroSize = localStart := by
    rw [Nat.mul_comm level macroSize]
    rw [Nat.mul_add_mod]
    exact Nat.mod_eq_of_lt hlocal
  simpa [hrem] using hmod

theorem bpLocalSparseOffsetEntries_get?_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      macroIdx localStart level : Nat}
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount)[
          bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]? =
      some
        (bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level) := by
  have hslot :
      bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level <
        macroCount * (levelCount * macroSize) :=
    bpLocalSparseCellSlot_lt hmacro hlevel hlocal
  have hget :
      (List.range (macroCount * (levelCount * macroSize)))[
          bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]? =
        some
          (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level) :=
    List.getElem?_range hslot
  have hdiv :=
    bpLocalSparseCellSlot_div_perMacro
      (macroCount := macroCount) hmacro hlevel hlocal
  have hremDiv :=
    bpLocalSparseCellSlot_rem_div
      (macroCount := macroCount) hmacro hlevel hlocal
  have hremMod :=
    bpLocalSparseCellSlot_rem_mod
      (macroCount := macroCount) hmacro hlevel hlocal
  let slot :=
    bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level
  have hgetSlot :
      (List.range (macroCount * (levelCount * macroSize)))[slot]? =
        some slot := by
    simpa [slot] using hget
  have hmap :
      ((List.range (macroCount * (levelCount * macroSize))).map
          (fun slot =>
            bpLocalSparseCellOffset shape blockSize blockCount macroSize
              (slot / (levelCount * macroSize))
              (slot % (levelCount * macroSize) % macroSize)
              (slot % (levelCount * macroSize) / macroSize)))[slot]? =
        some
          (bpLocalSparseCellOffset shape blockSize blockCount macroSize
            (slot / (levelCount * macroSize))
            (slot % (levelCount * macroSize) % macroSize)
            (slot % (levelCount * macroSize) / macroSize)) := by
    rw [List.getElem?_map]
    simp [hgetSlot]
  simpa [bpLocalSparseOffsetEntries, slot, hdiv, hremDiv, hremMod] using hmap

theorem bpLocalSparseCellOffset_valid_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level : Nat}
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount) :
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
        localStart level =
      bpRangeArgMinBlock shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level) -
        macroIdx * macroSize := by
  simp [bpLocalSparseCellOffset, hlocalSpan, hblockSpan]

theorem bpLocalSparseCellOffset_valid_add
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level : Nat}
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount) :
    macroIdx * macroSize +
        bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level =
      bpRangeArgMinBlock shape blockSize
        (macroIdx * macroSize + localStart) (2 ^ level) := by
  have hoffset :=
    bpLocalSparseCellOffset_valid_eq
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroIdx := macroIdx) (localStart := localStart) (level := level)
      hlocalSpan hblockSpan
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroIdx * macroSize + localStart) (2 ^ level)
      (Nat.pow_pos (by omega : 0 < 2))
  rw [hoffset]
  omega

theorem bpLocalSparseCellOffset_lt_width
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroIdx localStart level
      offsetWidth : Nat}
    (hwidth : macroSize < 2 ^ offsetWidth) :
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
        localStart level <
      2 ^ offsetWidth := by
  unfold bpLocalSparseCellOffset
  by_cases hvalid :
      localStart + 2 ^ level <= macroSize /\
        macroIdx * macroSize + localStart + 2 ^ level <= blockCount
  · simp [hvalid]
    let startBlock := macroIdx * macroSize + localStart
    let span := 2 ^ level
    have hspan : 0 < span := by
      exact Nat.pow_pos (by omega : 0 < 2)
    have hmem :=
      bpRangeArgMinBlock_mem shape blockSize startBlock span hspan
    have hoff :
        bpRangeArgMinBlock shape blockSize startBlock span -
            macroIdx * macroSize <
          macroSize := by
      omega
    exact Nat.lt_trans hoff hwidth
  · have hpow : 0 < 2 ^ offsetWidth := by
      exact Nat.pow_pos (by omega : 0 < 2)
    simp [hvalid, hpow]

theorem bpLocalSparseOffsetEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth entry : Nat}
    (hwidth : macroSize < 2 ^ offsetWidth)
    (hmem :
      entry ∈
        bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount) :
    entry < 2 ^ offsetWidth := by
  unfold bpLocalSparseOffsetEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, hentry⟩
  rw [← hentry]
  exact
    bpLocalSparseCellOffset_lt_width
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroIdx := slot / (levelCount * macroSize))
      (localStart := slot % (levelCount * macroSize) % macroSize)
      (level := slot % (levelCount * macroSize) / macroSize)
      (offsetWidth := offsetWidth) hwidth

structure PayloadLiveBPLocalSparseOffsetTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat) where
  table :
    FixedWidthNatTable
      (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount) offsetWidth
  payload_length_eq : table.payload.length = overhead

namespace PayloadLiveBPLocalSparseOffsetTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead) :
    List Bool :=
  offsetTable.table.payload

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead) :
    offsetTable.payload.length = overhead := by
  exact offsetTable.payload_length_eq

def readOffsetCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : Costed (Option Nat) :=
  offsetTable.table.readCosted
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) :
    (offsetTable.readOffsetCosted macroIdx localStart level).cost <= 1 := by
  unfold readOffsetCosted
  exact offsetTable.table.readCosted_cost_le_one
    (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level)

theorem readOffsetCosted_erase_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize) :
    (offsetTable.readOffsetCosted macroIdx localStart level).erase =
      some
        (bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
          localStart level) := by
  have hentry :=
    bpLocalSparseOffsetEntries_get?_of_valid
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (levelCount := levelCount)
      (macroIdx := macroIdx) (localStart := localStart)
      (level := level) hmacro hlevel hlocal
  unfold readOffsetCosted
  simpa using
    (show
      (offsetTable.table.readCosted
          (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
            level)).erase =
        (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount)[
            bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
              level]? from
      offsetTable.table.readCosted_erase
        (bpLocalSparseCellSlot macroSize levelCount macroIdx localStart
          level)).trans hentry

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead index : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hword : offsetTable.table.store.words[index]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := offsetTable.table.read_word_length_of_some hword
  omega

def spanCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart level : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (offsetTable.readOffsetCosted macroIdx localStart level) fun offset? =>
    match offset? with
    | some offset =>
        summary.minCandidateCosted (macroIdx * macroSize + offset)
    | none => Costed.pure none

theorem spanCandidateCosted_cost_le_five
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart level : Nat) :
    (offsetTable.spanCandidateCosted summary macroIdx localStart level).cost <=
      5 := by
  unfold spanCandidateCosted
  cases hoff :
      (offsetTable.readOffsetCosted macroIdx localStart level).value with
  | none =>
      have hread :=
        offsetTable.readOffsetCosted_cost_le_one macroIdx localStart level
      simp [Costed.bind, Costed.pure, hoff] at hread ⊢
      omega
  | some offset =>
      have hread :=
        offsetTable.readOffsetCosted_cost_le_one macroIdx localStart level
      have hsummary :=
        summary.minCandidateCosted_cost_le_four
          (macroIdx * macroSize + offset)
      simp [Costed.bind, hoff] at hread hsummary ⊢
      omega

end PayloadLiveBPLocalSparseOffsetTable

theorem bpRangeWitness_eq_of_bpRangeArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (hcount : 0 < blockCount) :
    (bpRangeMinExcess shape blockSize startBlock blockCount,
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount) =
      (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpRangeArgMinBlock shape blockSize startBlock blockCount)),
        bpBlockArgMinPrefixPos shape blockSize
          (bpRangeArgMinBlock shape blockSize startBlock blockCount)) := by
  have hprefix :=
    bpBlockArgMinPrefixPos_bpRangeArgMinBlock_of_pos
      shape blockSize startBlock blockCount hcount
  simp [bpRangeMinExcess, hprefix]

namespace PayloadLiveBPLocalSparseOffsetTable

theorem spanCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacro : macroIdx < macroCount)
    (hlevel : level < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalSpan : localStart + 2 ^ level <= macroSize)
    (hblockSpan :
      macroIdx * macroSize + localStart + 2 ^ level <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.spanCandidateCosted summary macroIdx localStart level).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level),
          bpRangeArgMinPrefixPos shape blockSize
            (macroIdx * macroSize + localStart) (2 ^ level)) := by
  let offset :=
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level
  have hoffRead :
      (offsetTable.readOffsetCosted macroIdx localStart level).erase =
        some offset := by
    simpa [offset] using
      offsetTable.readOffsetCosted_erase_of_valid hmacro hlevel hlocal
  have hoffAdd :
      macroIdx * macroSize + offset =
        bpRangeArgMinBlock shape blockSize
          (macroIdx * macroSize + localStart) (2 ^ level) := by
    simpa [offset] using
      bpLocalSparseCellOffset_valid_add
        (shape := shape) (blockSize := blockSize)
        (blockCount := blockCount) (macroSize := macroSize)
        (macroIdx := macroIdx) (localStart := localStart)
        (level := level) hlocalSpan hblockSpan
  have hspan : 0 < 2 ^ level := by
    exact Nat.pow_pos (by omega : 0 < 2)
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroIdx * macroSize + localStart) (2 ^ level) hspan
  have hblock : macroIdx * macroSize + offset < blockCount := by
    rw [hoffAdd]
    omega
  have hsummary :=
    summary.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblock hcover (hsuperCount hblock)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize (macroIdx * macroSize + localStart) (2 ^ level)
      hspan
  unfold spanCandidateCosted
  rw [Costed.erase_bind]
  simp [hoffRead]
  simpa [hoffAdd, hwitness] using hsummary

end PayloadLiveBPLocalSparseOffsetTable

theorem bpRangeArgMinPrefixPosFrom_mem_of_best_and_candidates
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best lo hi : Nat)
    (hbest : lo <= best /\ best < hi)
    (hcandidate :
      forall {offset : Nat},
        offset < steps ->
          lo <= bpBlockArgMinPrefixPos shape blockSize (block + offset) /\
            bpBlockArgMinPrefixPos shape blockSize (block + offset) < hi) :
    lo <= bpRangeArgMinPrefixPosFrom shape blockSize block steps best /\
      bpRangeArgMinPrefixPosFrom shape blockSize block steps best < hi := by
  induction steps generalizing block best with
  | zero =>
      simpa [bpRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      let candidate := bpBlockArgMinPrefixPos shape blockSize block
      let next := bpBetterArgMinPrefixPos shape best candidate
      have hcand0 : lo <= candidate /\ candidate < hi := by
        simpa [candidate] using hcandidate (offset := 0) (by omega)
      have hnext : lo <= next /\ next < hi := by
        unfold next bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape candidate < bpExcessAt shape best
        · simp [hlt, hcand0]
        · simp [hlt, hbest]
      have hrec :=
        ih (block := block + 1) (best := next)
          hnext
          (by
            intro offset hoffset
            have htail := hcandidate (offset := offset + 1) (by omega)
            have hblock :
                block + (offset + 1) = block + 1 + offset := by
              omega
            simpa [hblock] using htail)
      simpa [candidate, next] using hrec

theorem bpRangeArgMinPrefixPos_mem_prefix_range
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1) :
    blockStartOf blockSize startBlock <=
        bpRangeArgMinPrefixPos shape blockSize startBlock blockCount /\
      bpRangeArgMinPrefixPos shape blockSize startBlock blockCount <
        blockStartOf blockSize (startBlock + blockCount) + 1 := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      omega
  | succ count =>
      have hstartBlockBound :
          blockStartOf blockSize startBlock + (blockSize + 1) <=
            shape.bpCode.length + 1 := by
        have hlocal :
            blockStartOf blockSize startBlock + (blockSize + 1) <=
              blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
          have hstep :
              blockStartOf blockSize startBlock + (blockSize + 1) =
                blockStartOf blockSize (startBlock + 1) + 1 := by
            rw [← blockStartOf_succ blockSize startBlock]
            omega
          have hmono :
              blockStartOf blockSize (startBlock + 1) <=
                blockStartOf blockSize (startBlock + (count + 1)) :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          omega
        omega
      have hbestLocal :=
        bpBlockArgMinPrefixPos_mem_range
          (shape := shape) (blockSize := blockSize)
          (block := startBlock) hstartBlockBound
      have hbest :
          blockStartOf blockSize startBlock <=
              bpBlockArgMinPrefixPos shape blockSize startBlock /\
            bpBlockArgMinPrefixPos shape blockSize startBlock <
              blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
        constructor
        · exact hbestLocal.1
        · have hlocal :
              blockStartOf blockSize startBlock + (blockSize + 1) <=
                blockStartOf blockSize (startBlock + (count + 1)) + 1 := by
            have hstep :
                blockStartOf blockSize startBlock + (blockSize + 1) =
                  blockStartOf blockSize (startBlock + 1) + 1 := by
              rw [← blockStartOf_succ blockSize startBlock]
              omega
            have hmono :
                blockStartOf blockSize (startBlock + 1) <=
                  blockStartOf blockSize (startBlock + (count + 1)) :=
              blockStartOf_mono (blockSize := blockSize) (by omega)
            omega
          omega
      exact
        bpRangeArgMinPrefixPosFrom_mem_of_best_and_candidates
          shape blockSize (startBlock + 1) count
          (bpBlockArgMinPrefixPos shape blockSize startBlock)
          (blockStartOf blockSize startBlock)
          (blockStartOf blockSize (startBlock + (count + 1)) + 1)
          hbest
          (by
            intro offset hoffset
            have hcandidateBound :
                blockStartOf blockSize (startBlock + 1 + offset) +
                    (blockSize + 1) <=
                  shape.bpCode.length + 1 := by
              have hlocal :
                  blockStartOf blockSize (startBlock + 1 + offset) +
                      (blockSize + 1) <=
                    blockStartOf blockSize (startBlock + (count + 1)) +
                      1 := by
                have hstep :
                    blockStartOf blockSize (startBlock + 1 + offset) +
                        (blockSize + 1) =
                      blockStartOf blockSize
                          (startBlock + 1 + offset + 1) + 1 := by
                  rw [← blockStartOf_succ
                    blockSize (startBlock + 1 + offset)]
                  omega
                have hmono :
                    blockStartOf blockSize
                        (startBlock + 1 + offset + 1) <=
                      blockStartOf blockSize
                        (startBlock + (count + 1)) :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                omega
              omega
            have hcand :=
              bpBlockArgMinPrefixPos_mem_range
                (shape := shape) (blockSize := blockSize)
                (block := startBlock + 1 + offset)
                hcandidateBound
            constructor
            · have hlo :
                  blockStartOf blockSize startBlock <=
                    blockStartOf blockSize (startBlock + 1 + offset) := by
                exact blockStartOf_mono (blockSize := blockSize) (by omega)
              omega
            · have hhi :
                  blockStartOf blockSize (startBlock + 1 + offset) +
                      (blockSize + 1) <=
                    blockStartOf blockSize (startBlock + (count + 1)) +
                      1 := by
                have hstep :
                    blockStartOf blockSize (startBlock + 1 + offset) +
                        (blockSize + 1) =
                      blockStartOf blockSize
                          (startBlock + 1 + offset + 1) + 1 := by
                  rw [← blockStartOf_succ
                    blockSize (startBlock + 1 + offset)]
                  omega
                have hmono :
                    blockStartOf blockSize
                        (startBlock + 1 + offset + 1) <=
                      blockStartOf blockSize
                        (startBlock + (count + 1)) :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                omega
              omega)

theorem bpPrefixRangeMinExcess_ge_of_all_prefix_ge
    {shape : Cartesian.CartesianShape}
    {start count lower : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hge :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            lower <= bpExcessAt shape pos) :
    lower <= bpPrefixRangeMinExcess shape start count := by
  have hmem :=
    bpPrefixRangeArgMinPrefixPos_mem_range
      (shape := shape) (start := start) (count := count)
      hcount hbound
  exact hge hmem.1 hmem.2

theorem bpPrefixRangeMinExcess_gt_of_all_prefix_gt
    {shape : Cartesian.CartesianShape}
    {start count lower : Nat}
    (hcount : 0 < count)
    (hbound : start + count <= shape.bpCode.length + 1)
    (hgt :
      forall {pos : Nat},
        start <= pos ->
          pos < start + count ->
            lower < bpExcessAt shape pos) :
    lower < bpPrefixRangeMinExcess shape start count := by
  have hmem :=
    bpPrefixRangeArgMinPrefixPos_mem_range
      (shape := shape) (start := start) (count := count)
      hcount hbound
  exact hgt hmem.1 hmem.2

theorem bpRangeMinExcess_ge_of_all_prefix_ge
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount lower : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1)
    (hge :
      forall {pos : Nat},
        blockStartOf blockSize startBlock <= pos ->
          pos < blockStartOf blockSize (startBlock + blockCount) + 1 ->
            lower <= bpExcessAt shape pos) :
    lower <=
      bpRangeMinExcess shape blockSize startBlock blockCount := by
  have hmem :=
    bpRangeArgMinPrefixPos_mem_prefix_range
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      hcount hbound
  exact hge hmem.1 hmem.2

theorem bpRangeMinExcess_gt_of_all_prefix_gt
    {shape : Cartesian.CartesianShape}
    {blockSize startBlock blockCount lower : Nat}
    (hcount : 0 < blockCount)
    (hbound :
      blockStartOf blockSize (startBlock + blockCount) + 1 <=
        shape.bpCode.length + 1)
    (hgt :
      forall {pos : Nat},
        blockStartOf blockSize startBlock <= pos ->
          pos < blockStartOf blockSize (startBlock + blockCount) + 1 ->
            lower < bpExcessAt shape pos) :
    lower <
      bpRangeMinExcess shape blockSize startBlock blockCount := by
  have hmem :=
    bpRangeArgMinPrefixPos_mem_prefix_range
      (shape := shape) (blockSize := blockSize)
      (startBlock := startBlock) (blockCount := blockCount)
      hcount hbound
  exact hgt hmem.1 hmem.2

theorem bpPrefixRangeMinExcess_le_length
    (shape : Cartesian.CartesianShape)
    (start count : Nat) :
    bpPrefixRangeMinExcess shape start count <= shape.bpCode.length := by
  exact bpExcessAt_le_length shape
    (bpPrefixRangeArgMinPrefixPos shape start count)

theorem bpPrefixRangeMinExcess_le_prefix_of_mem
    {shape : Cartesian.CartesianShape}
    {start count prefixPos : Nat}
    (hmem : start <= prefixPos /\ prefixPos < start + count)
    (hprefix : prefixPos <= shape.bpCode.length) :
    bpPrefixRangeMinExcess shape start count <=
      bpExcessAt shape prefixPos := by
  have hoffset : prefixPos - start < count := by
    omega
  have hmin :=
    bpPrefixRangeArgMinPrefixPos_excess_le_offset shape
      start count (prefixPos - start) hoffset
  have hpos : start + (prefixPos - start) = prefixPos := by
    omega
  simpa [bpPrefixRangeMinExcess, hpos, Nat.min_eq_left hprefix]
    using hmin

theorem bpEndpointPrefixRangeMinExcess_le_answerClose
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    bpPrefixRangeMinExcess shape (leftClose + 1)
        (rightClose - leftClose + 1) <=
      bpExcessAt shape (answerClose + 1) := by
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose) hlen hleft hright hanswer
  have hanswerBound := bpCloseOfInorder?_bounds shape hanswer
  have hprefixBound : answerClose + 1 <= shape.bpCode.length := by
    omega
  exact
    bpPrefixRangeMinExcess_le_prefix_of_mem
      (shape := shape)
      (start := leftClose + 1)
      (count := rightClose - leftClose + 1)
      (prefixPos := answerClose + 1)
      hmem hprefixBound

theorem scanWindow_node_representative_spanning_root
    (leftShape rightShape : Cartesian.CartesianShape)
    {start len : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len) :
    scanWindow
        (Cartesian.CartesianShape.node
          leftShape rightShape).representative start len =
      leftShape.size := by
  let xs :=
    (Cartesian.CartesianShape.node
      leftShape rightShape).representative
  let leftValues := Cartesian.addConst 1 leftShape.representative
  let rightValues := Cartesian.addConst 1 rightShape.representative
  have hxs :
      xs = leftValues ++ (0 :: rightValues) := by
    simp [xs, leftValues, rightValues,
      Cartesian.CartesianShape.representative]
  have hleftValuesLen : leftValues.length = leftShape.size := by
    simp [leftValues, Cartesian.addConst_length,
      Cartesian.CartesianShape.representative_length]
  have hrootGet : xs[leftShape.size]? = some 0 := by
    rw [hxs]
    have hidx : leftShape.size = leftValues.length := by
      omega
    simp [hidx]
  have harg :
      LeftmostArgMin xs start (start + len) leftShape.size := by
    refine ⟨by omega, ?_, hrootLo, hrootHi, 0, hrootGet, ?_, ?_⟩
    · simpa [xs, Cartesian.CartesianShape.representative_length] using hbound
    · intro j w _hjLo _hjHi hget
      have hmem : w ∈ xs := List.mem_of_getElem? hget
      have hnonneg :=
        Cartesian.CartesianShape.representative_nonnegative
          (Cartesian.CartesianShape.node leftShape rightShape) w
          (by simpa [xs] using hmem)
      omega
    · intro j w _hjLo hjRoot hget
      have hgetLeft :
          leftValues[j]? = some w := by
        rw [hxs] at hget
        have hjLeftValues : j < leftValues.length := by
          omega
        simpa [List.getElem?_append, hjLeftValues] using hget
      have hpos :=
        Cartesian.CartesianShape.representative_shift_positive
          leftShape w (List.mem_of_getElem? hgetLeft)
      omega
  have hscan :
      LeftmostArgMin xs start (start + len)
        (scanWindow xs start len) := by
    exact scanWindow_leftmost xs start len hlen (by
      simpa [xs, Cartesian.CartesianShape.representative_length] using hbound)
  have huniq :=
    leftmostArgMin_unique xs start (start + len)
      (scanWindow xs start len) leftShape.size hscan harg
  simpa [xs] using huniq

theorem answerClose_eq_root_close_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    answerClose = leftShape.bpCode.length + 1 := by
  have hscan :=
    scanWindow_node_representative_spanning_root
      leftShape rightShape hlen hbound hrootLo hrootHi
  rw [hscan] at hanswer
  simp [bpCloseOfInorder?] at hanswer
  exact hanswer.symm

theorem answerClose_prefix_leftmost_min_excess_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (_hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (_hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    (forall {pos : Nat},
      leftClose + 1 <= pos ->
        pos < rightClose + 2 ->
          bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1) <=
            bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape) pos) /\
      (forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt
                (Cartesian.CartesianShape.node leftShape rightShape)
                (answerClose + 1) <
              bpExcessAt
                (Cartesian.CartesianShape.node leftShape rightShape) pos) := by
  have hanswerEq :=
    answerClose_eq_root_close_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len) (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hanswer
  constructor
  · intro pos _hlo _hhi
    subst answerClose
    exact bpExcessAt_node_root_close_succ_le_prefix
      leftShape rightShape pos
  · intro pos hlo hlt
    subst answerClose
    have hpos : 0 < pos := by
      omega
    exact bpExcessAt_node_root_close_succ_lt_before
      leftShape rightShape hpos hlt

theorem answerClose_prefix_leftmost_min_excess_of_query
    {shape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : start + len <= shape.size)
    (hleft : bpCloseOfInorder? shape start = some leftClose)
    (hright :
      bpCloseOfInorder? shape (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative start len) =
        some answerClose) :
    (forall {pos : Nat},
      leftClose + 1 <= pos ->
        pos < rightClose + 2 ->
          bpExcessAt shape (answerClose + 1) <=
            bpExcessAt shape pos) /\
      (forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) := by
  induction shape generalizing start len leftClose rightClose answerClose with
  | empty =>
      simp [Cartesian.CartesianShape.size] at hbound
      omega
  | node leftShape rightShape ihLeft ihRight =>
      by_cases hrootLo : start <= leftShape.size
      · by_cases hrootHi : leftShape.size < start + len
        · exact
            answerClose_prefix_leftmost_min_excess_of_spanning_root
              (leftShape := leftShape) (rightShape := rightShape)
              (start := start) (len := len)
              (leftClose := leftClose) (rightClose := rightClose)
              (answerClose := answerClose)
              hlen hbound hrootLo hrootHi hleft hright hanswer
        · have hleftWindow : start + len <= leftShape.size :=
            Nat.le_of_not_gt hrootHi
          have hstartLeft : start < leftShape.size := by
            omega
          have hendLeft : start + len - 1 < leftShape.size := by
            omega
          let leftValues := Cartesian.addConst 1 leftShape.representative
          let rightValues := Cartesian.addConst 1 rightShape.representative
          have hleftValuesBound :
              start + len <= leftValues.length := by
            simp [leftValues, Cartesian.addConst_length,
              Cartesian.CartesianShape.representative_length]
            exact hleftWindow
          have hscanParent :
              scanWindow
                  (Cartesian.CartesianShape.node
                    leftShape rightShape).representative start len =
                scanWindow leftShape.representative start len := by
            have happ :=
              Cartesian.scanWindow_append_left leftValues
                (0 :: rightValues) (left := start) (len := len)
                hleftValuesBound
            calc
              scanWindow
                  (Cartesian.CartesianShape.node
                    leftShape rightShape).representative start len =
                scanWindow (leftValues ++ (0 :: rightValues)) start len := by
                  simp [leftValues, rightValues,
                    Cartesian.CartesianShape.representative]
              _ = scanWindow leftValues start len := happ
              _ = scanWindow leftShape.representative start len := by
                  exact Cartesian.scanWindow_addConst 1
                    leftShape.representative start len
          cases hleftRec :
              bpCloseOfInorder? leftShape start with
          | none =>
              simp [bpCloseOfInorder?, hstartLeft, hleftRec] at hleft
          | some childLeftClose =>
              simp [bpCloseOfInorder?, hstartLeft, hleftRec] at hleft
              subst leftClose
              cases hrightRec :
                  bpCloseOfInorder? leftShape (start + len - 1) with
              | none =>
                  simp [bpCloseOfInorder?, hendLeft, hrightRec] at hright
              | some childRightClose =>
                  simp [bpCloseOfInorder?, hendLeft, hrightRec] at hright
                  subst rightClose
                  have hscanBounds :=
                    Cartesian.scanWindow_bounds leftShape.representative
                      start len hlen
                  have hscanLeft :
                      scanWindow leftShape.representative start len <
                        leftShape.size := by
                    omega
                  cases hanswerRec :
                      bpCloseOfInorder? leftShape
                        (scanWindow leftShape.representative start len) with
                  | none =>
                      simp [bpCloseOfInorder?, hscanParent, hscanLeft,
                        hanswerRec] at hanswer
                  | some childAnswerClose =>
                      simp [bpCloseOfInorder?, hscanParent, hscanLeft,
                        hanswerRec] at hanswer
                      subst answerClose
                      have hchild :=
                        ihLeft hlen hleftWindow hleftRec hrightRec
                          hanswerRec
                      have hanswerBound :
                          childAnswerClose + 1 <= leftShape.bpCode.length := by
                        have hcloseBound :=
                          bpCloseOfInorder?_bounds leftShape hanswerRec
                        omega
                      have hrightBound :
                          childRightClose + 1 <= leftShape.bpCode.length := by
                        have hcloseBound :=
                          bpCloseOfInorder?_bounds leftShape hrightRec
                        omega
                      constructor
                      · intro pos hlo hhi
                        have hchildLo :
                            childLeftClose + 1 <= pos - 1 := by
                          omega
                        have hchildHi :
                            pos - 1 < childRightClose + 2 := by
                          omega
                        have hposBound :
                            pos - 1 <= leftShape.bpCode.length := by
                          omega
                        have hanswerShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := childAnswerClose + 1) hanswerBound
                        have hposShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := pos - 1) hposBound
                        have hposEq : pos = (pos - 1) + 1 := by
                          omega
                        rw [show childAnswerClose + 1 + 1 =
                            (childAnswerClose + 1) + 1 by omega]
                        rw [hanswerShift]
                        rw [hposEq, hposShift]
                        have hcmp := hchild.1 hchildLo hchildHi
                        omega
                      · intro pos hlo hhi
                        have hchildLo :
                            childLeftClose + 1 <= pos - 1 := by
                          omega
                        have hchildHi :
                            pos - 1 < childAnswerClose + 1 := by
                          omega
                        have hposBound :
                            pos - 1 <= leftShape.bpCode.length := by
                          omega
                        have hanswerShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := childAnswerClose + 1) hanswerBound
                        have hposShift :=
                          bpExcessAt_node_left_prefix_succ
                            leftShape rightShape
                            (pos := pos - 1) hposBound
                        have hposEq : pos = (pos - 1) + 1 := by
                          omega
                        rw [show childAnswerClose + 1 + 1 =
                            (childAnswerClose + 1) + 1 by omega]
                        rw [hanswerShift]
                        rw [hposEq, hposShift]
                        have hcmp := hchild.2 hchildLo hchildHi
                        omega
      · have hstartRight : leftShape.size < start := Nat.lt_of_not_ge hrootLo
        let localStart := start - leftShape.size - 1
        have hstartEq : start = leftShape.size + 1 + localStart := by
          simp [localStart]
          omega
        have hrightWindow : localStart + len <= rightShape.size := by
          simp [Cartesian.CartesianShape.size] at hbound
          omega
        have hendLocalEq :
            start + len - 1 - leftShape.size - 1 =
              localStart + len - 1 := by
          simp [localStart]
          omega
        let leftValues := Cartesian.addConst 1 leftShape.representative
        let rightValues := Cartesian.addConst 1 rightShape.representative
        let pre := leftValues ++ [0]
        have hpreLen : pre.length = leftShape.size + 1 := by
          simp [pre, leftValues, Cartesian.addConst_length,
            Cartesian.CartesianShape.representative_length]
        have hrightValuesBound :
            localStart + len <= rightValues.length := by
          simp [rightValues, Cartesian.addConst_length,
            Cartesian.CartesianShape.representative_length]
          exact hrightWindow
        have hscanParent :
            scanWindow
                (Cartesian.CartesianShape.node
                  leftShape rightShape).representative start len =
              leftShape.size + 1 +
                scanWindow rightShape.representative localStart len := by
          have happ :=
            Cartesian.scanWindow_append_right pre rightValues
              (left := localStart) (len := len) hrightValuesBound
          calc
            scanWindow
                (Cartesian.CartesianShape.node
                  leftShape rightShape).representative start len =
              scanWindow (pre ++ rightValues) (pre.length + localStart)
                len := by
                have hstartPre : start = pre.length + localStart := by
                  omega
                simp [pre, leftValues, rightValues,
                  Cartesian.CartesianShape.representative, hstartPre,
                  List.append_assoc]
            _ = pre.length + scanWindow rightValues localStart len := happ
            _ = leftShape.size + 1 +
                scanWindow rightShape.representative localStart len := by
                rw [hpreLen]
                rw [Cartesian.scanWindow_addConst]
        have hnotStartLeft : ¬ start < leftShape.size := by
          omega
        have hnotStartRoot : ¬ start = leftShape.size := by
          omega
        cases hleftRec :
            bpCloseOfInorder? rightShape localStart with
        | none =>
            simp [bpCloseOfInorder?, hnotStartLeft, hnotStartRoot,
              localStart, hleftRec] at hleft
        | some childLeftClose =>
            simp [bpCloseOfInorder?, hnotStartLeft, hnotStartRoot,
              localStart, hleftRec] at hleft
            subst leftClose
            have hnotEndLeft : ¬ start + len - 1 < leftShape.size := by
              omega
            have hnotEndRoot : ¬ start + len - 1 = leftShape.size := by
              omega
            cases hrightRec :
                bpCloseOfInorder? rightShape
                  (localStart + len - 1) with
            | none =>
                simp [bpCloseOfInorder?, hnotEndLeft, hnotEndRoot,
                  localStart, hendLocalEq, hrightRec] at hright
            | some childRightClose =>
                simp [bpCloseOfInorder?, hnotEndLeft, hnotEndRoot,
                  localStart, hendLocalEq, hrightRec] at hright
                subst rightClose
                have hscanBounds :=
                  Cartesian.scanWindow_bounds rightShape.representative
                    localStart len hlen
                have hscanRight :
                    scanWindow rightShape.representative localStart len <
                      rightShape.size := by
                  omega
                have hnotAnswerLeft :
                    ¬ scanWindow
                        (Cartesian.CartesianShape.node
                          leftShape rightShape).representative start len <
                      leftShape.size := by
                  rw [hscanParent]
                  omega
                have hnotAnswerRoot :
                    ¬ scanWindow
                        (Cartesian.CartesianShape.node
                          leftShape rightShape).representative start len =
                      leftShape.size := by
                  rw [hscanParent]
                  omega
                have hanswerLocalEq :
                    scanWindow
                          (Cartesian.CartesianShape.node
                            leftShape rightShape).representative start len -
                        leftShape.size - 1 =
                      scanWindow rightShape.representative localStart len := by
                  rw [hscanParent]
                  omega
                cases hanswerRec :
                    bpCloseOfInorder? rightShape
                      (scanWindow rightShape.representative
                        localStart len) with
                | none =>
                    simp [bpCloseOfInorder?, hnotAnswerLeft,
                      hnotAnswerRoot, hanswerLocalEq, hanswerRec] at hanswer
                | some childAnswerClose =>
                    simp [bpCloseOfInorder?, hnotAnswerLeft,
                      hnotAnswerRoot, hanswerLocalEq, hanswerRec] at hanswer
                    subst answerClose
                    have hchild :=
                      ihRight hlen hrightWindow hleftRec hrightRec hanswerRec
                    have hanswerBound :
                        childAnswerClose + 1 <= rightShape.bpCode.length := by
                      have hcloseBound :=
                        bpCloseOfInorder?_bounds rightShape hanswerRec
                      omega
                    have hrightBound :
                        childRightClose + 1 <= rightShape.bpCode.length := by
                      have hcloseBound :=
                        bpCloseOfInorder?_bounds rightShape hrightRec
                      omega
                    constructor
                    · intro pos hlo hhi
                      have hchildLo :
                          childLeftClose + 1 <=
                            pos - (leftShape.bpCode.length + 2) := by
                        omega
                      have hchildHi :
                          pos - (leftShape.bpCode.length + 2) <
                            childRightClose + 2 := by
                        omega
                      have hposBound :
                          pos - (leftShape.bpCode.length + 2) <=
                            rightShape.bpCode.length := by
                        omega
                      have hanswerShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := childAnswerClose + 1) hanswerBound
                      have hposShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := pos - (leftShape.bpCode.length + 2))
                          hposBound
                      have hposEq :
                          pos =
                            leftShape.bpCode.length + 2 +
                              (pos - (leftShape.bpCode.length + 2)) := by
                        omega
                      rw [show leftShape.bpCode.length + 2 +
                          childAnswerClose + 1 =
                        leftShape.bpCode.length + 2 +
                          (childAnswerClose + 1) by omega]
                      rw [hanswerShift]
                      rw [hposEq, hposShift]
                      exact hchild.1 hchildLo hchildHi
                    · intro pos hlo hhi
                      have hchildLo :
                          childLeftClose + 1 <=
                            pos - (leftShape.bpCode.length + 2) := by
                        omega
                      have hchildHi :
                          pos - (leftShape.bpCode.length + 2) <
                            childAnswerClose + 1 := by
                        omega
                      have hposBound :
                          pos - (leftShape.bpCode.length + 2) <=
                            rightShape.bpCode.length := by
                        omega
                      have hanswerShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := childAnswerClose + 1) hanswerBound
                      have hposShift :=
                        bpExcessAt_node_right_prefix_shift
                          leftShape rightShape
                          (pos := pos - (leftShape.bpCode.length + 2))
                          hposBound
                      have hposEq :
                          pos =
                            leftShape.bpCode.length + 2 +
                              (pos - (leftShape.bpCode.length + 2)) := by
                        omega
                      rw [show leftShape.bpCode.length + 2 +
                          childAnswerClose + 1 =
                        leftShape.bpCode.length + 2 +
                          (childAnswerClose + 1) by omega]
                      rw [hanswerShift]
                      rw [hposEq, hposShift]
                      exact hchild.2 hchildLo hchildHi

theorem endpointPrefixRangeWitness_eq_answerClose_of_spanning_root
    {leftShape rightShape : Cartesian.CartesianShape}
    {start len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose) :
    (bpPrefixRangeMinExcess
        (Cartesian.CartesianShape.node leftShape rightShape)
        (leftClose + 1) (rightClose - leftClose + 1),
      bpPrefixRangeArgMinPrefixPos
        (Cartesian.CartesianShape.node leftShape rightShape)
        (leftClose + 1) (rightClose - leftClose + 1)) =
      (bpExcessAt
          (Cartesian.CartesianShape.node leftShape rightShape)
          (answerClose + 1),
        answerClose + 1) := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := Cartesian.CartesianShape.node leftShape rightShape)
      (left := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := Cartesian.CartesianShape.node leftShape rightShape)
      (left := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hrightBound :=
    bpCloseOfInorder?_bounds
      (Cartesian.CartesianShape.node leftShape rightShape) hright
  have hrangeBound :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1 := by
    omega
  exact
    bpPrefixRangeWitness_eq_of_leftmost_min_excess
      hmem hrangeBound
      (by
        intro pos hlo hhi
        exact hsemantic.1 hlo (by omega))
      (by
        intro pos hlo hhi
        exact hsemantic.2 hlo hhi)

def bpPrefixRangeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range => bpPrefixRangeMinExcess shape range.1 range.2

def bpPrefixRangeArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpPrefixRangeArgMinPrefixPos shape range.1 range.2

theorem bpPrefixRangeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeMinExcessEntries shape ranges).length = ranges.length := by
  simp [bpPrefixRangeMinExcessEntries]

theorem bpPrefixRangeArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges).length =
      ranges.length := by
  simp [bpPrefixRangeArgMinPrefixPosEntries]

theorem bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeMinExcess shape range.1 range.2) := by
  simp [bpPrefixRangeMinExcessEntries, List.getElem?_map, hget]

theorem bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeArgMinPrefixPos shape range.1 range.2) := by
  simp [bpPrefixRangeArgMinPrefixPosEntries, List.getElem?_map, hget]

theorem bpPrefixRangeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeMinExcessEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeMinExcess_le_length shape range.1 range.2) hwidth

theorem bpPrefixRangeArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeArgMinPrefixPosEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeArgMinPrefixPos_le_length shape range.1 range.2)
    hwidth

structure PayloadLiveBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth overhead : Nat)
    (ranges : List (Nat × Nat)) where
  minTable :
    FixedWidthNatTable
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
  argTable :
    FixedWidthNatTable
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
  payload_length_eq :
    minTable.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPPrefixRangeArgMinWitnessTable

def payload
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) : List Bool :=
  table.minTable.payload ++ table.argTable.payload

def rangeWitnessCosted
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minTable.readCosted rangeIndex) fun min? =>
    Costed.map
      (fun arg? =>
        match min?, arg? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none)
      (table.argTable.readCosted rangeIndex)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem rangeWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).cost <= 2 := by
  unfold rangeWitnessCosted
  cases hread :
      (table.minTable.readCosted rangeIndex).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
  | some minExcess =>
      simp [Costed.bind, Costed.map, hread]

theorem rangeWitnessCosted_erase
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).erase =
      match
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? with
      | some minExcess, some prefixPos => some (minExcess, prefixPos)
      | _, _ => none := by
  unfold rangeWitnessCosted
  have hmin :
      (table.minTable.readCosted rangeIndex).value =
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? := by
    exact table.minTable.readCosted_erase rangeIndex
  have harg :
      (table.argTable.readCosted rangeIndex).value =
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? := by
    exact table.argTable.readCosted_erase rangeIndex
  cases hminEntry :
      (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hmin, harg,
    hminEntry, hargEntry]

theorem min_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.minTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.minTable.read_word_length_of_some hword
  omega

theorem arg_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.argTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := table.argTable.read_word_length_of_some hword
  omega

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  constructor
  · intro rangeIndex word hword
    exact table.min_read_word_length_le_machine hmachine hword
  · intro rangeIndex word hword
    exact table.arg_read_word_length_le_machine hmachine hword

theorem profile
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead /\
      forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
              (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
            with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none := by
  constructor
  · exact table.payload_length
  intro rangeIndex
  exact ⟨table.rangeWitnessCosted_cost_le_two rangeIndex,
    table.rangeWitnessCosted_erase rangeIndex⟩

end PayloadLiveBPPrefixRangeArgMinWitnessTable

def concreteBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (2 * (ranges.length * fieldWidth)) ranges where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
      (bpPrefixRangeMinExcessEntries_mem_bound hwidth)
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
      (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload_length
    omega

def bpCandidateBetter (left right : Nat × Nat) : Nat × Nat :=
  if right.1 < left.1 then right else left

def bpCandidateMerge? :
    Option (Nat × Nat) -> Option (Nat × Nat) -> Option (Nat × Nat)
  | none, candidate => candidate
  | candidate, none => candidate
  | some left, some right => some (bpCandidateBetter left right)

def bpCandidateMerge3?
    (left middle right : Option (Nat × Nat)) : Option (Nat × Nat) :=
  bpCandidateMerge? (bpCandidateMerge? left middle) right

def bpCandidateClose? (candidate? : Option (Nat × Nat)) : Option Nat :=
  candidate?.map fun candidate => candidate.2 - 1

theorem bpCandidateBetter_eq_left_of_fst_le
    {left right : Nat × Nat}
    (hle : left.1 <= right.1) :
    bpCandidateBetter left right = left := by
  unfold bpCandidateBetter
  have hnot : ¬ right.1 < left.1 := by
    omega
  simp [hnot]

theorem bpCandidateBetter_eq_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateBetter left right = right := by
  simp [bpCandidateBetter, hlt]

theorem bpCandidateMerge?_some_left_of_fst_le
    {left : Nat × Nat} {right? : Option (Nat × Nat)}
    (hright :
      forall {right : Nat × Nat}, right? = some right -> left.1 <= right.1) :
    bpCandidateMerge? (some left) right? = some left := by
  cases right? with
  | none =>
      simp [bpCandidateMerge?]
  | some right =>
      have hle : left.1 <= right.1 := hright rfl
      simp [bpCandidateMerge?, bpCandidateBetter_eq_left_of_fst_le hle]

theorem bpCandidateMerge?_some_right_of_fst_lt
    {left right : Nat × Nat}
    (hlt : right.1 < left.1) :
    bpCandidateMerge? (some left) (some right) = some right := by
  simp [bpCandidateMerge?, bpCandidateBetter_eq_right_of_fst_lt hlt]

theorem bpCandidateMerge3?_eq_some_left_of_fst_le
    {left : Nat × Nat}
    {middle? right? : Option (Nat × Nat)}
    (hmiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> left.1 <= middle.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> left.1 <= right.1) :
    bpCandidateMerge3? (some left) middle? right? = some left := by
  have hfirst :
      bpCandidateMerge? (some left) middle? = some left :=
    bpCandidateMerge?_some_left_of_fst_le hmiddle
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
    {left middle : Nat × Nat}
    {right? : Option (Nat × Nat)}
    (hmiddleLeft : middle.1 < left.1)
    (hright :
      forall {right : Nat × Nat},
        right? = some right -> middle.1 <= right.1) :
    bpCandidateMerge3? (some left) (some middle) right? =
      some middle := by
  have hfirst :
      bpCandidateMerge? (some left) (some middle) = some middle :=
    bpCandidateMerge?_some_right_of_fst_lt hmiddleLeft
  unfold bpCandidateMerge3?
  rw [hfirst]
  exact bpCandidateMerge?_some_left_of_fst_le hright

theorem bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
    {left right : Nat × Nat}
    {middle? : Option (Nat × Nat)}
    (hrightLeft : right.1 < left.1)
    (hrightMiddle :
      forall {middle : Nat × Nat},
        middle? = some middle -> right.1 < middle.1) :
    bpCandidateMerge3? (some left) middle? (some right) =
      some right := by
  cases middle? with
  | none =>
      unfold bpCandidateMerge3?
      simp [bpCandidateMerge?,
        bpCandidateBetter_eq_right_of_fst_lt hrightLeft]
  | some middle =>
      have hmiddle : right.1 < middle.1 := hrightMiddle rfl
      have hfirst :
          bpCandidateMerge? (some left) (some middle) =
            some (bpCandidateBetter left middle) := by
        simp [bpCandidateMerge?]
      unfold bpCandidateMerge3?
      rw [hfirst]
      by_cases hmiddleLeft : middle.1 < left.1
      · have hbest :
            bpCandidateBetter left middle = middle :=
          bpCandidateBetter_eq_right_of_fst_lt hmiddleLeft
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hmiddle
      · have hle : left.1 <= middle.1 := Nat.le_of_not_gt hmiddleLeft
        have hbest :
            bpCandidateBetter left middle = left :=
          bpCandidateBetter_eq_left_of_fst_le hle
        rw [hbest]
        exact bpCandidateMerge?_some_right_of_fst_lt hrightLeft

theorem bpCandidateMerge?_argmin_pair
    (shape : Cartesian.CartesianShape)
    (left right : Nat) :
    bpCandidateMerge?
        (some (bpExcessAt shape left, left))
        (some (bpExcessAt shape right, right)) =
      some
        (bpExcessAt shape (bpBetterArgMinPrefixPos shape left right),
          bpBetterArgMinPrefixPos shape left right) := by
  unfold bpCandidateMerge? bpCandidateBetter bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt]
  · simp [hlt]

theorem bpCandidateMerge?_adjacentRangeWitness
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock leftCount rightCount : Nat)
    (hleftCount : 0 < leftCount)
    (hrightCount : 0 < rightCount) :
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock leftCount,
            bpRangeArgMinPrefixPos shape blockSize startBlock leftCount))
        (some
          (bpRangeMinExcess shape blockSize (startBlock + leftCount)
            rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount) rightCount)) =
      some
        (bpRangeMinExcess shape blockSize startBlock
          (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) := by
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock leftCount
  let rightStart := startBlock + leftCount
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart rightCount
  have hleft :=
    bpRangeArgMinBlock_leftmost shape blockSize startBlock leftCount
      hleftCount
  have hright :=
    bpRangeArgMinBlock_leftmost shape blockSize rightStart rightCount
      hrightCount
  have hleftWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock leftCount hleftCount
  have hrightWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize rightStart rightCount hrightCount
  by_cases htake :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize rightBlock),
              bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact bpCandidateMerge?_some_right_of_fst_lt htake
    have hglobal :
        (bpRangeMinExcess shape blockSize startBlock
            (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) =
        (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock),
          bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact
        bpRangeWitness_eq_of_leftmost_block_candidate
          (shape := shape) (blockSize := blockSize)
          (startBlock := startBlock)
          (blockCount := leftCount + rightCount)
          (targetBlock := rightBlock)
          (target :=
            bpBlockArgMinPrefixPos shape blockSize rightBlock)
          (by
            constructor
            · exact Nat.le_trans (by omega : startBlock <= rightStart)
                hright.1
            · have hhi := hright.2.1
              omega)
          rfl
          (by
            intro candidateBlock hlo hhi
            by_cases hrightSide : rightStart <= candidateBlock
            · exact hright.2.2.1 hrightSide (by omega)
            · have hleftSide : candidateBlock < startBlock + leftCount := by
                omega
              exact Nat.le_trans (Nat.le_of_lt htake)
                (hleft.2.2.1 hlo hleftSide))
          (by
            intro candidateBlock hlo hlt
            by_cases hrightSide : rightStart <= candidateBlock
            · exact hright.2.2.2 hrightSide hlt
            · have hleftSide : candidateBlock < startBlock + leftCount := by
                omega
              exact Nat.lt_of_lt_of_le htake
                (hleft.2.2.1 hlo hleftSide))
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, hglobal] using hmerge
  · have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) :=
      Nat.le_of_not_gt htake
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize leftBlock),
              bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpCandidateMerge?_some_left_of_fst_le
          (by
            intro right hrightSome
            cases hrightSome
            exact hle)
    have hglobal :
        (bpRangeMinExcess shape blockSize startBlock
            (leftCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + rightCount)) =
        (bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock),
          bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpRangeWitness_eq_of_leftmost_block_candidate
          (shape := shape) (blockSize := blockSize)
          (startBlock := startBlock)
          (blockCount := leftCount + rightCount)
          (targetBlock := leftBlock)
          (target :=
            bpBlockArgMinPrefixPos shape blockSize leftBlock)
          (by
            constructor
            · exact hleft.1
            · have hhi := hleft.2.1
              omega)
          rfl
          (by
            intro candidateBlock hlo hhi
            by_cases hleftSide : candidateBlock < startBlock + leftCount
            · exact hleft.2.2.1 hlo hleftSide
            · have hrightSide : rightStart <= candidateBlock := by
                omega
              exact Nat.le_trans hle (hright.2.2.1 hrightSide (by omega)))
          (by
            intro candidateBlock hlo hlt
            exact hleft.2.2.2 hlo hlt)
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, hglobal] using hmerge

theorem bpCandidateMerge3?_threeAdjacentRangeWitness
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock leftCount middleCount rightCount : Nat)
    (hleftCount : 0 < leftCount)
    (hmiddleCount : 0 < middleCount)
    (hrightCount : 0 < rightCount) :
    bpCandidateMerge3?
        (some
          (bpRangeMinExcess shape blockSize startBlock leftCount,
            bpRangeArgMinPrefixPos shape blockSize startBlock leftCount))
        (some
          (bpRangeMinExcess shape blockSize (startBlock + leftCount)
            middleCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount) middleCount))
        (some
          (bpRangeMinExcess shape blockSize
            (startBlock + leftCount + middleCount) rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              (startBlock + leftCount + middleCount) rightCount)) =
      some
        (bpRangeMinExcess shape blockSize startBlock
          (leftCount + middleCount + rightCount),
          bpRangeArgMinPrefixPos shape blockSize startBlock
            (leftCount + middleCount + rightCount)) := by
  have hfirst :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount middleCount
      hleftCount hmiddleCount
  have hsecond :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock (leftCount + middleCount) rightCount
      (by omega) hrightCount
  unfold bpCandidateMerge3?
  rw [hfirst]
  simpa [Nat.add_assoc] using hsecond

theorem bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount span : Nat)
    (hspan : 0 < span) :
    let rightStart := startBlock + blockCount - span
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock span,
            bpRangeArgMinPrefixPos shape blockSize startBlock span))
        (some
          (bpRangeMinExcess shape blockSize rightStart span,
            bpRangeArgMinPrefixPos shape blockSize rightStart span)) =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize startBlock
              blockCount span)) := by
  let rightStart := startBlock + blockCount - span
  let leftBlock :=
    bpRangeArgMinBlock shape blockSize startBlock span
  let rightBlock :=
    bpRangeArgMinBlock shape blockSize rightStart span
  have hleftWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock span hspan
  have hrightWitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize rightStart span hspan
  by_cases htake :
      bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize rightBlock) <
        bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize leftBlock)
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          rightBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize rightBlock),
              bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact bpCandidateMerge?_some_right_of_fst_lt htake
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, htarget] using hmerge
  · have htarget :
        bpSparseTwoSpanArgMinBlock shape blockSize startBlock blockCount span =
          leftBlock := by
      simp [bpSparseTwoSpanArgMinBlock, leftBlock, rightStart, rightBlock,
        bpBetterArgMinBlock, htake]
    have hle :
        bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize leftBlock) <=
          bpExcessAt shape
            (bpBlockArgMinPrefixPos shape blockSize rightBlock) := by
      exact Nat.le_of_not_gt htake
    have hmerge :
        bpCandidateMerge?
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize leftBlock),
                bpBlockArgMinPrefixPos shape blockSize leftBlock))
            (some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize rightBlock),
                bpBlockArgMinPrefixPos shape blockSize rightBlock)) =
          some
            (bpExcessAt shape
              (bpBlockArgMinPrefixPos shape blockSize leftBlock),
              bpBlockArgMinPrefixPos shape blockSize leftBlock) := by
      exact
        bpCandidateMerge?_some_left_of_fst_le
          (by
            intro right hright
            cases hright
            exact hle)
    simpa [rightStart, leftBlock, rightBlock, hleftWitness,
      hrightWitness, htarget] using hmerge

theorem bpCandidateMerge?_bpSparseLogSpanArgMinBlock
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat)
    (_hcount : 0 < blockCount) :
    let span := bpSparseLogSpan blockCount
    let rightStart := startBlock + blockCount - span
    bpCandidateMerge?
        (some
          (bpRangeMinExcess shape blockSize startBlock span,
            bpRangeArgMinPrefixPos shape blockSize startBlock span))
        (some
          (bpRangeMinExcess shape blockSize rightStart span,
            bpRangeArgMinPrefixPos shape blockSize rightStart span)) =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize startBlock
              blockCount)) := by
  unfold bpSparseLogSpanArgMinBlock
  exact
    bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
      shape blockSize startBlock blockCount
      (bpSparseLogSpan blockCount)
      (bpSparseLogSpan_pos blockCount)

namespace PayloadLiveBPLocalSparseOffsetTable

def twoSpanCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart count : Nat) : Costed (Option (Nat × Nat)) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  let rightLocalStart := localStart + count - span
  Costed.bind
    (offsetTable.spanCandidateCosted summary macroIdx localStart level)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (offsetTable.spanCandidateCosted summary macroIdx rightLocalStart
          level)

theorem twoSpanCandidateCosted_cost_le_ten
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart count : Nat) :
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).cost <=
      10 := by
  unfold twoSpanCandidateCosted
  have hleft :=
    offsetTable.spanCandidateCosted_cost_le_five summary macroIdx localStart
      (Nat.log2 count)
  have hright :=
    offsetTable.spanCandidateCosted_cost_le_five summary macroIdx
      (localStart + count - bpSparseLogSpan count) (Nat.log2 count)
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem twoSpanCandidateCosted_erase_sparseLog_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < count)
    (hmacro : macroIdx < macroCount)
    (hlevel : Nat.log2 count < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalCount : localStart + count <= macroSize)
    (hblockCount :
      macroIdx * macroSize + localStart + count <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).erase =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize
              (macroIdx * macroSize + localStart) count)),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseLogSpanArgMinBlock shape blockSize
              (macroIdx * macroSize + localStart) count)) := by
  let span := bpSparseLogSpan count
  let level := Nat.log2 count
  let startBlock := macroIdx * macroSize + localStart
  let rightLocalStart := localStart + count - span
  have hspanEq : span = 2 ^ level := by
    simp [span, level, bpSparseLogSpan]
  have hspanPos : 0 < span := by
    simpa [span] using bpSparseLogSpan_pos count
  have hspanLe : span <= count := by
    simpa [span] using bpSparseLogSpan_le_self hcount
  have hleftSpan : localStart + 2 ^ level <= macroSize := by
    omega
  have hleftBlock : macroIdx * macroSize + localStart + 2 ^ level <= blockCount := by
    omega
  have hrightLocal : rightLocalStart < macroSize := by
    have hrightSpan : rightLocalStart + span <= macroSize := by
      omega
    omega
  have hrightSpan : rightLocalStart + 2 ^ level <= macroSize := by
    omega
  have hrightBlock :
      macroIdx * macroSize + rightLocalStart + 2 ^ level <= blockCount := by
    omega
  have hrightStart :
      macroIdx * macroSize + rightLocalStart =
        startBlock + count - span := by
    omega
  have hleftExact :=
    offsetTable.spanCandidateCosted_erase_exact
      summary hmacro hlevel hlocal hleftSpan hleftBlock hblocks hcover
      hsuperCount
  have hrightExact :=
    offsetTable.spanCandidateCosted_erase_exact
      summary hmacro hlevel hrightLocal hrightSpan hrightBlock hblocks
      hcover hsuperCount
  have hrightErase :
      (offsetTable.spanCandidateCosted summary macroIdx
          (localStart + count - bpSparseLogSpan count)
          (Nat.log2 count)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroIdx * macroSize +
              (localStart + count - bpSparseLogSpan count))
            (2 ^ Nat.log2 count),
            bpRangeArgMinPrefixPos shape blockSize
              (macroIdx * macroSize +
                (localStart + count - bpSparseLogSpan count))
              (2 ^ Nat.log2 count)) := by
    simpa [span, level, rightLocalStart] using hrightExact
  have hmerge :=
    bpCandidateMerge?_bpSparseLogSpanArgMinBlock
      shape blockSize startBlock count hcount
  unfold twoSpanCandidateCosted
  rw [Costed.erase_bind]
  simp [hleftExact]
  simp [Costed.map, hrightErase]
  simpa [span, level, startBlock, rightLocalStart, hrightStart] using hmerge

theorem twoSpanCandidateCosted_erase_rangeWitness_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < count)
    (hmacro : macroIdx < macroCount)
    (hlevel : Nat.log2 count < levelCount)
    (hlocal : localStart < macroSize)
    (hlocalCount : localStart + count <= macroSize)
    (hblockCount :
      macroIdx * macroSize + localStart + count <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (offsetTable.twoSpanCandidateCosted summary macroIdx localStart count).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroIdx * macroSize + localStart) count,
          bpRangeArgMinPrefixPos shape blockSize
            (macroIdx * macroSize + localStart) count) := by
  have hselector :=
    offsetTable.twoSpanCandidateCosted_erase_sparseLog_exact
      summary hcount hmacro hlevel hlocal hlocalCount hblockCount
      hblocks hcover hsuperCount
  have hwitness :=
    bpRangeWitness_eq_of_bpSparseLogSpanArgMinBlock
      shape blockSize (macroIdx * macroSize + localStart) count hcount
  simpa [hwitness] using hselector

end PayloadLiveBPLocalSparseOffsetTable

def bpGlobalSparseCellSlot
    (macroCount macroStart level : Nat) : Nat :=
  level * macroCount + macroStart

def bpGlobalSparseCellBlock
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount macroStart level : Nat) :
    Nat :=
  let spanMacros := 2 ^ level
  let startBlock := macroStart * macroSize
  let spanBlocks := spanMacros * macroSize
  if macroStart + spanMacros <= macroCount ∧ startBlock + spanBlocks <= blockCount then
    bpRangeArgMinBlock shape blockSize startBlock spanBlocks
  else
    0

def bpGlobalSparseBlockEntries
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    List Nat :=
  (List.range (levelCount * macroCount)).map fun slot =>
    let level := slot / macroCount
    let macroStart := slot % macroCount
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level

theorem bpGlobalSparseCellSlot_lt
    {macroCount levelCount macroStart level : Nat}
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level <
      levelCount * macroCount := by
  unfold bpGlobalSparseCellSlot
  have hstep :
      level * macroCount + macroStart <
        level * macroCount + macroCount :=
    Nat.add_lt_add_left hmacro (level * macroCount)
  have hsucc :
      level * macroCount + macroCount =
        (level + 1) * macroCount := by
    simpa using (Nat.succ_mul level macroCount).symm
  have hmul :
      (level + 1) * macroCount <= levelCount * macroCount :=
    Nat.mul_le_mul_right macroCount (Nat.succ_le_of_lt hlevel)
  exact Nat.lt_of_lt_of_le (by simpa [hsucc] using hstep) hmul

theorem bpGlobalSparseCellSlot_div
    {macroCount levelCount macroStart level : Nat}
    (_hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level / macroCount =
      level := by
  have hpos : 0 < macroCount := by omega
  unfold bpGlobalSparseCellSlot
  rw [Nat.mul_comm level macroCount]
  rw [Nat.mul_add_div hpos]
  rw [Nat.div_eq_of_lt hmacro]
  omega

theorem bpGlobalSparseCellSlot_mod
    {macroCount levelCount macroStart level : Nat}
    (_hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    bpGlobalSparseCellSlot macroCount macroStart level % macroCount =
      macroStart := by
  unfold bpGlobalSparseCellSlot
  rw [Nat.mul_comm level macroCount]
  rw [Nat.mul_add_mod]
  exact Nat.mod_eq_of_lt hmacro

theorem bpGlobalSparseBlockEntries_get?_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      macroStart level : Nat}
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount)[
          bpGlobalSparseCellSlot macroCount macroStart level]? =
      some
        (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
          macroCount macroStart level) := by
  have hslot :
      bpGlobalSparseCellSlot macroCount macroStart level <
        levelCount * macroCount :=
    bpGlobalSparseCellSlot_lt hlevel hmacro
  have hget :
      (List.range (levelCount * macroCount))[
          bpGlobalSparseCellSlot macroCount macroStart level]? =
        some (bpGlobalSparseCellSlot macroCount macroStart level) :=
    List.getElem?_range hslot
  have hdiv :=
    bpGlobalSparseCellSlot_div
      (levelCount := levelCount) hlevel hmacro
  have hmod :=
    bpGlobalSparseCellSlot_mod
      (levelCount := levelCount) hlevel hmacro
  let slot := bpGlobalSparseCellSlot macroCount macroStart level
  have hgetSlot :
      (List.range (levelCount * macroCount))[slot]? = some slot := by
    simpa [slot] using hget
  have hmap :
      ((List.range (levelCount * macroCount)).map
          (fun slot =>
            bpGlobalSparseCellBlock shape blockSize blockCount macroSize
              macroCount (slot % macroCount) (slot / macroCount)))[slot]? =
        some
          (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
            macroCount (slot % macroCount) (slot / macroCount)) := by
    rw [List.getElem?_map]
    simp [hgetSlot]
  simpa [bpGlobalSparseBlockEntries, slot, hdiv, hmod] using hmap

theorem bpGlobalSparseCellBlock_valid_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount macroStart level : Nat}
    (hmacroSpan : macroStart + 2 ^ level <= macroCount)
    (hblockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount) :
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
        macroStart level =
      bpRangeArgMinBlock shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) := by
  simp [bpGlobalSparseCellBlock, hmacroSpan, hblockSpan]

theorem bpGlobalSparseCellBlock_lt_width
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount macroStart level
      blockWidth : Nat}
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth) :
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
        macroStart level <
      2 ^ blockWidth := by
  unfold bpGlobalSparseCellBlock
  by_cases hvalid :
      macroStart + 2 ^ level <= macroCount /\
        macroStart * macroSize + 2 ^ level * macroSize <= blockCount
  · simp [hvalid]
    have hspan : 0 < 2 ^ level * macroSize := by
      exact Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) hmacroSize
    have hmem :=
      bpRangeArgMinBlock_mem shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) hspan
    exact Nat.lt_trans (by omega : bpRangeArgMinBlock shape blockSize
        (macroStart * macroSize) (2 ^ level * macroSize) < blockCount)
      hwidth
  · have hpow : 0 < 2 ^ blockWidth := by
      exact Nat.pow_pos (by omega : 0 < 2)
    simp [hvalid, hpow]

theorem bpGlobalSparseBlockEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth entry : Nat}
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth)
    (hmem :
      entry ∈
        bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount) :
    entry < 2 ^ blockWidth := by
  unfold bpGlobalSparseBlockEntries at hmem
  rcases List.mem_map.mp hmem with ⟨slot, _hslot, hentry⟩
  rw [← hentry]
  exact
    bpGlobalSparseCellBlock_lt_width
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (macroStart := slot % macroCount)
      (level := slot / macroCount) (blockWidth := blockWidth)
      hmacroSize hwidth

structure PayloadLiveBPGlobalSparseBlockTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat) where
  table :
    FixedWidthNatTable
      (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount) blockWidth
  payload_length_eq : table.payload.length = overhead

namespace PayloadLiveBPGlobalSparseBlockTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead) :
    List Bool :=
  globalTable.table.payload

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead) :
    globalTable.payload.length = overhead := by
  exact globalTable.payload_length_eq

def readBlockCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : Costed (Option Nat) :=
  globalTable.table.readCosted
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) :
    (globalTable.readBlockCosted macroStart level).cost <= 1 := by
  unfold readBlockCosted
  exact globalTable.table.readCosted_cost_le_one
    (bpGlobalSparseCellSlot macroCount macroStart level)

theorem readBlockCosted_erase_of_valid
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount) :
    (globalTable.readBlockCosted macroStart level).erase =
      some
        (bpGlobalSparseCellBlock shape blockSize blockCount macroSize
          macroCount macroStart level) := by
  have hentry :=
    bpGlobalSparseBlockEntries_get?_of_valid
      (shape := shape) (blockSize := blockSize)
      (blockCount := blockCount) (macroSize := macroSize)
      (macroCount := macroCount) (levelCount := levelCount)
      (macroStart := macroStart) (level := level) hlevel hmacro
  unfold readBlockCosted
  simpa using
    (show
      (globalTable.table.readCosted
          (bpGlobalSparseCellSlot macroCount macroStart level)).erase =
        (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount)[
            bpGlobalSparseCellSlot macroCount macroStart level]? from
      globalTable.table.readCosted_erase
        (bpGlobalSparseCellSlot macroCount macroStart level)).trans hentry

theorem read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead index : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hmachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hword : globalTable.table.store.words[index]? = some word) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hlen := globalTable.table.read_word_length_of_some hword
  omega

def spanCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart level : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (globalTable.readBlockCosted macroStart level) fun block? =>
    match block? with
    | some block => summary.minCandidateCosted block
    | none => Costed.pure none

theorem spanCandidateCosted_cost_le_five
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart level : Nat) :
    (globalTable.spanCandidateCosted summary macroStart level).cost <= 5 := by
  unfold spanCandidateCosted
  cases hblock :
      (globalTable.readBlockCosted macroStart level).value with
  | none =>
      have hread :=
        globalTable.readBlockCosted_cost_le_one macroStart level
      simp [Costed.bind, Costed.pure, hblock] at hread ⊢
      omega
  | some block =>
      have hread :=
        globalTable.readBlockCosted_cost_le_one macroStart level
      have hsummary := summary.minCandidateCosted_cost_le_four block
      simp [Costed.bind, hblock] at hread hsummary ⊢
      omega

theorem spanCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hlevel : level < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroSize : 0 < macroSize)
    (hmacroSpan : macroStart + 2 ^ level <= macroCount)
    (hblockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.spanCandidateCosted summary macroStart level).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize) (2 ^ level * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize) (2 ^ level * macroSize)) := by
  let block :=
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level
  have hblockRead :
      (globalTable.readBlockCosted macroStart level).erase =
        some block := by
    simpa [block] using
      globalTable.readBlockCosted_erase_of_valid hlevel hmacro
  have hblockEq :
      block =
        bpRangeArgMinBlock shape blockSize
          (macroStart * macroSize) (2 ^ level * macroSize) := by
    simpa [block] using
      bpGlobalSparseCellBlock_valid_eq
        (shape := shape) (blockSize := blockSize)
        (blockCount := blockCount) (macroSize := macroSize)
        (macroCount := macroCount) (macroStart := macroStart)
        (level := level) hmacroSpan hblockSpan
  have hspan : 0 < 2 ^ level * macroSize := by
    exact Nat.mul_pos (Nat.pow_pos (by omega : 0 < 2)) hmacroSize
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize
      (macroStart * macroSize) (2 ^ level * macroSize) hspan
  have hblockLt : block < blockCount := by
    rw [hblockEq]
    omega
  have hsummary :=
    summary.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblockLt hcover (hsuperCount hblockLt)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize (macroStart * macroSize)
      (2 ^ level * macroSize) hspan
  unfold spanCandidateCosted
  rw [Costed.erase_bind]
  simp [hblockRead]
  simpa [hblockEq, hwitness] using hsummary

def twoSpanCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart macroSpanCount : Nat) : Costed (Option (Nat × Nat)) :=
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  Costed.bind
    (globalTable.spanCandidateCosted summary macroStart level)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (globalTable.spanCandidateCosted summary rightMacroStart level)

theorem twoSpanCandidateCosted_cost_le_ten
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart macroSpanCount : Nat) :
    (globalTable.twoSpanCandidateCosted summary macroStart
      macroSpanCount).cost <= 10 := by
  unfold twoSpanCandidateCosted
  have hleft :=
    globalTable.spanCandidateCosted_cost_le_five summary macroStart
      (Nat.log2 macroSpanCount)
  have hright :=
    globalTable.spanCandidateCosted_cost_le_five summary
      (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
      (Nat.log2 macroSpanCount)
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem twoSpanCandidateCosted_erase_sparse_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < macroSpanCount)
    (hmacroSize : 0 < macroSize)
    (hlevel : Nat.log2 macroSpanCount < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroCount : macroStart + macroSpanCount <= macroCount)
    (hblockCount : macroStart * macroSize + macroSpanCount * macroSize <=
      blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount).erase =
      some
        (bpExcessAt shape
          (bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize
              (macroStart * macroSize) (macroSpanCount * macroSize)
              (bpSparseLogSpan macroSpanCount * macroSize))),
          bpBlockArgMinPrefixPos shape blockSize
            (bpSparseTwoSpanArgMinBlock shape blockSize
              (macroStart * macroSize) (macroSpanCount * macroSize)
              (bpSparseLogSpan macroSpanCount * macroSize))) := by
  let level := Nat.log2 macroSpanCount
  let spanMacros := bpSparseLogSpan macroSpanCount
  let rightMacroStart := macroStart + macroSpanCount - spanMacros
  have hspanMacrosPos : 0 < spanMacros := by
    simpa [spanMacros] using bpSparseLogSpan_pos macroSpanCount
  have hspanMacrosLe : spanMacros <= macroSpanCount := by
    simpa [spanMacros] using bpSparseLogSpan_le_self hcount
  have hspanBlocksPos : 0 < spanMacros * macroSize := by
    exact Nat.mul_pos hspanMacrosPos hmacroSize
  have hspanEq : spanMacros = 2 ^ level := by
    simp [spanMacros, level, bpSparseLogSpan]
  have hleftMacroSpan : macroStart + 2 ^ level <= macroCount := by
    rw [← hspanEq]
    omega
  have hleftBlockSpan :
      macroStart * macroSize + 2 ^ level * macroSize <= blockCount := by
    rw [← hspanEq]
    have hspanBlocksLe :
        spanMacros * macroSize <= macroSpanCount * macroSize :=
      Nat.mul_le_mul_right macroSize hspanMacrosLe
    omega
  have hrightMacro : rightMacroStart < macroCount := by
    have hrightSpan : rightMacroStart + spanMacros <= macroCount := by
      omega
    omega
  have hrightMacroSpan :
      rightMacroStart + 2 ^ level <= macroCount := by
    rw [← hspanEq]
    omega
  have hrightBlockSpan :
      rightMacroStart * macroSize + 2 ^ level * macroSize <=
        blockCount := by
    rw [← hspanEq]
    have hrightEnd :
        rightMacroStart * macroSize + spanMacros * macroSize =
          macroStart * macroSize + macroSpanCount * macroSize := by
      have hrightAdd : rightMacroStart + spanMacros =
          macroStart + macroSpanCount := by
        omega
      calc
        rightMacroStart * macroSize + spanMacros * macroSize =
            (rightMacroStart + spanMacros) * macroSize := by
          rw [Nat.add_mul]
        _ = (macroStart + macroSpanCount) * macroSize := by
          rw [hrightAdd]
        _ = macroStart * macroSize + macroSpanCount * macroSize := by
          rw [Nat.add_mul]
    simpa [hrightEnd] using hblockCount
  have hrightStart :
      rightMacroStart * macroSize =
        macroStart * macroSize + macroSpanCount * macroSize -
          spanMacros * macroSize := by
    have hrightEnd :
        rightMacroStart * macroSize + spanMacros * macroSize =
          macroStart * macroSize + macroSpanCount * macroSize := by
      have hrightAdd : rightMacroStart + spanMacros =
          macroStart + macroSpanCount := by
        omega
      calc
        rightMacroStart * macroSize + spanMacros * macroSize =
            (rightMacroStart + spanMacros) * macroSize := by
          rw [Nat.add_mul]
        _ = (macroStart + macroSpanCount) * macroSize := by
          rw [hrightAdd]
        _ = macroStart * macroSize + macroSpanCount * macroSize := by
          rw [Nat.add_mul]
    omega
  have hleftExact :=
    globalTable.spanCandidateCosted_erase_exact
      summary hlevel hmacro hmacroSize hleftMacroSpan hleftBlockSpan
      hblocks hcover hsuperCount
  have hrightExact :=
    globalTable.spanCandidateCosted_erase_exact
      summary hlevel hrightMacro hmacroSize hrightMacroSpan
      hrightBlockSpan hblocks hcover hsuperCount
  have hrightErase :
      (globalTable.spanCandidateCosted summary
          (macroStart + macroSpanCount - bpSparseLogSpan macroSpanCount)
          (Nat.log2 macroSpanCount)).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + macroSpanCount -
              bpSparseLogSpan macroSpanCount) * macroSize)
            (2 ^ Nat.log2 macroSpanCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + macroSpanCount -
                bpSparseLogSpan macroSpanCount) * macroSize)
              (2 ^ Nat.log2 macroSpanCount * macroSize)) := by
    simpa [rightMacroStart, spanMacros, level] using hrightExact
  have hmerge :=
    bpCandidateMerge?_bpSparseTwoSpanArgMinBlock
      shape blockSize (macroStart * macroSize)
      (macroSpanCount * macroSize) (spanMacros * macroSize)
      hspanBlocksPos
  unfold twoSpanCandidateCosted
  rw [Costed.erase_bind]
  simp [hleftExact]
  simp [Costed.map, hrightErase]
  simpa [spanMacros, level, rightMacroStart, hrightStart,
    Nat.mul_assoc] using hmerge

theorem twoSpanCandidateCosted_erase_rangeWitness_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hcount : 0 < macroSpanCount)
    (hmacroSize : 0 < macroSize)
    (hlevel : Nat.log2 macroSpanCount < levelCount)
    (hmacro : macroStart < macroCount)
    (hmacroCount : macroStart + macroSpanCount <= macroCount)
    (hblockCount : macroStart * macroSize + macroSpanCount * macroSize <=
      blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (globalTable.twoSpanCandidateCosted summary macroStart
        macroSpanCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize) (macroSpanCount * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize) (macroSpanCount * macroSize)) := by
  let spanMacros := bpSparseLogSpan macroSpanCount
  have hselector :=
    globalTable.twoSpanCandidateCosted_erase_sparse_exact
      summary hcount hmacroSize hlevel hmacro hmacroCount hblockCount
      hblocks hcover hsuperCount
  have hspanPos : 0 < spanMacros * macroSize := by
    exact Nat.mul_pos
      (by simpa [spanMacros] using bpSparseLogSpan_pos macroSpanCount)
      hmacroSize
  have hspanLe : spanMacros * macroSize <= macroSpanCount * macroSize :=
    Nat.mul_le_mul_right macroSize
      (by simpa [spanMacros] using bpSparseLogSpan_le_self hcount)
  have hcoverSpan :
      macroSpanCount * macroSize <= 2 * (spanMacros * macroSize) := by
    have hmacroCover :
        macroSpanCount <= 2 * spanMacros := by
      simpa [spanMacros] using self_le_two_mul_bpSparseLogSpan hcount
    have hmul :=
      Nat.mul_le_mul_right macroSize hmacroCover
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hwitness :=
    bpRangeWitness_eq_of_bpSparseTwoSpanArgMinBlock
      shape blockSize (macroStart * macroSize)
      (macroSpanCount * macroSize) (spanMacros * macroSize)
      hspanPos hspanLe hcoverSpan
  simpa [spanMacros, hwitness] using hselector

end PayloadLiveBPGlobalSparseBlockTable

theorem bpLocalSparseOffsetEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
      macroCount levelCount).length =
      macroCount * (levelCount * macroSize) := by
  simp [bpLocalSparseOffsetEntries]

def concreteBPLocalSparseOffsetTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      offsetWidth : Nat)
    (hwidth : macroSize < 2 ^ offsetWidth) :
    PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
      macroSize macroCount levelCount offsetWidth
      ((macroCount * (levelCount * macroSize)) * offsetWidth) where
  table :=
    FixedWidthNatTable.ofEntries
      (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
        macroCount levelCount) offsetWidth
      (bpLocalSparseOffsetEntries_mem_bound hwidth)
  payload_length_eq := by
    simpa [bpLocalSparseOffsetEntries_length] using
      (FixedWidthNatTable.ofEntries
        (bpLocalSparseOffsetEntries shape blockSize blockCount macroSize
          macroCount levelCount) offsetWidth
        (bpLocalSparseOffsetEntries_mem_bound hwidth)).payload_length

theorem bpGlobalSparseBlockEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount : Nat) :
    (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
      macroCount levelCount).length =
      levelCount * macroCount := by
  simp [bpGlobalSparseBlockEntries]

def concreteBPGlobalSparseBlockTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount macroSize macroCount levelCount
      blockWidth : Nat)
    (hmacroSize : 0 < macroSize)
    (hwidth : blockCount < 2 ^ blockWidth) :
    PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
      macroSize macroCount levelCount blockWidth
      ((levelCount * macroCount) * blockWidth) where
  table :=
    FixedWidthNatTable.ofEntries
      (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
        macroCount levelCount) blockWidth
      (bpGlobalSparseBlockEntries_mem_bound hmacroSize hwidth)
  payload_length_eq := by
    simpa [bpGlobalSparseBlockEntries_length] using
      (FixedWidthNatTable.ofEntries
        (bpGlobalSparseBlockEntries shape blockSize blockCount macroSize
          macroCount levelCount) blockWidth
        (bpGlobalSparseBlockEntries_mem_bound hmacroSize hwidth)).payload_length

def bpTwoLevelCrossMacroCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.bind
        (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount)
        fun middle? =>
          Costed.map
            (fun right? => bpCandidateMerge3? left? middle? right?)
            (localTable.twoSpanCandidateCosted summary rightMacroStart 0
              rightCount)

def bpTwoLevelAdjacentMacroCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart rightCount : Nat) : Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.map
        (fun right? => bpCandidateMerge? left? right?)
        (localTable.twoSpanCandidateCosted summary (macroStart + 1) 0
          rightCount)

theorem bpTwoLevelAdjacentMacroCandidateCosted_cost_le_twenty
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart rightCount : Nat) :
    (bpTwoLevelAdjacentMacroCandidateCosted localTable summary macroStart
      localStart rightCount).cost <= 20 := by
  unfold bpTwoLevelAdjacentMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hright :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      0 rightCount
  simp [Costed.bind, Costed.map] at hleft hright ⊢
  omega

theorem bpTwoLevelAdjacentMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead macroStart localStart
      rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hrightCount : 0 < rightCount)
    (hrightLe : rightCount <= macroSize)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hrightLevel : Nat.log2 rightCount < localLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hrightMacro : macroStart + 1 < macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          rightCount <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelAdjacentMacroCandidateCosted localTable summary macroStart
        localStart rightCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) + rightCount),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) + rightCount)) := by
  let leftCount := macroSize - localStart
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hrightBlockCount :
      (macroStart + 1) * macroSize + rightCount <= blockCount := by
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hrightExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hrightCount hrightMacro hrightLevel
      (by omega : 0 < macroSize)
      (by simpa using hrightLe)
      hrightBlockCount hblocks hcover hsuperCount
  have hrightErase :
      (localTable.twoSpanCandidateCosted summary (macroStart + 1) 0
          rightCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize) rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize) rightCount) := by
    simpa using hrightExact
  have hmerge :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount rightCount
      hleftCount hrightCount
  unfold bpTwoLevelAdjacentMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hrightErase]
  simpa [startBlock, leftCount, hleftEnd, Nat.add_assoc] using hmerge

def bpTwoLevelLeftMiddleMacroCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount : Nat) :
    Costed (Option (Nat × Nat)) :=
  let leftCount := macroSize - localStart
  Costed.bind
    (localTable.twoSpanCandidateCosted summary macroStart localStart
      leftCount)
    fun left? =>
      Costed.map
        (fun middle? => bpCandidateMerge? left? middle?)
        (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount)

theorem bpTwoLevelLeftMiddleMacroCandidateCosted_cost_le_twenty
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount : Nat) :
    (bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
      summary macroStart localStart middleMacroCount).cost <= 20 := by
  unfold bpTwoLevelLeftMiddleMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hmiddle :=
    globalTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      middleMacroCount
  simp [Costed.bind, Costed.map] at hleft hmiddle ⊢
  omega

theorem bpTwoLevelLeftMiddleMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hmiddleCount : 0 < middleMacroCount)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hmiddleLevel : Nat.log2 middleMacroCount < globalLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hmiddleEnd : macroStart + 1 + middleMacroCount <= macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          middleMacroCount * macroSize <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
        summary macroStart localStart middleMacroCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) + middleMacroCount * macroSize),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) + middleMacroCount * macroSize)) := by
  let leftCount := macroSize - localStart
  let middleCount := middleMacroCount * macroSize
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hmiddleBlocks : 0 < middleCount := by
    exact Nat.mul_pos hmiddleCount hmacroSize
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hmiddleBlockCount :
      (macroStart + 1) * macroSize + middleMacroCount * macroSize <=
        blockCount := by
    have hmidEnd :
        (macroStart + 1) * macroSize + middleMacroCount * macroSize =
          macroStart * macroSize + (macroSize - localStart) +
              middleMacroCount * macroSize + localStart := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      omega
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hmiddleExact :=
    globalTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hmiddleCount hmacroSize hmiddleLevel
      (by omega : macroStart + 1 < macroCount)
      hmiddleEnd hmiddleBlockCount hblocks hcover hsuperCount
  have hmiddleErase :
      (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize)
            (middleMacroCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize)
              (middleMacroCount * macroSize)) := by
    simpa [middleCount] using hmiddleExact
  have hmerge :=
    bpCandidateMerge?_adjacentRangeWitness
      shape blockSize startBlock leftCount middleCount
      hleftCount hmiddleBlocks
  unfold bpTwoLevelLeftMiddleMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hmiddleErase]
  simpa [startBlock, leftCount, middleCount, hleftEnd, Nat.add_assoc] using
    hmerge

theorem bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
      macroStart localStart middleMacroCount rightCount).cost <= 30 := by
  unfold bpTwoLevelCrossMacroCandidateCosted
  have hleft :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary macroStart
      localStart (macroSize - localStart)
  have hmiddle :=
    globalTable.twoSpanCandidateCosted_cost_le_ten summary (macroStart + 1)
      middleMacroCount
  have hright :=
    localTable.twoSpanCandidateCosted_cost_le_ten summary
      (macroStart + 1 + middleMacroCount) 0 rightCount
  simp [Costed.bind, Costed.map] at hleft hmiddle hright ⊢
  omega

theorem bpTwoLevelCrossMacroCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount
      rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacroSize : 0 < macroSize)
    (hlocalStart : localStart < macroSize)
    (hmiddleCount : 0 < middleMacroCount)
    (hrightCount : 0 < rightCount)
    (hrightLe : rightCount <= macroSize)
    (hleftLevel : Nat.log2 (macroSize - localStart) < localLevelCount)
    (hmiddleLevel : Nat.log2 middleMacroCount < globalLevelCount)
    (hrightLevel : Nat.log2 rightCount < localLevelCount)
    (hmacroStart : macroStart < macroCount)
    (hrightMacro : macroStart + 1 + middleMacroCount < macroCount)
    (hblockCount :
      macroStart * macroSize + localStart + (macroSize - localStart) +
          middleMacroCount * macroSize + rightCount <= blockCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
        macroStart localStart middleMacroCount rightCount).erase =
      some
        (bpRangeMinExcess shape blockSize
          (macroStart * macroSize + localStart)
          ((macroSize - localStart) +
            middleMacroCount * macroSize + rightCount),
          bpRangeArgMinPrefixPos shape blockSize
            (macroStart * macroSize + localStart)
            ((macroSize - localStart) +
              middleMacroCount * macroSize + rightCount)) := by
  let leftCount := macroSize - localStart
  let middleCount := middleMacroCount * macroSize
  let rightMacroStart := macroStart + 1 + middleMacroCount
  let startBlock := macroStart * macroSize + localStart
  have hleftCount : 0 < leftCount := by
    omega
  have hmiddleBlocks : 0 < middleCount := by
    exact Nat.mul_pos hmiddleCount hmacroSize
  have hleftEnd :
      startBlock + leftCount = (macroStart + 1) * macroSize := by
    have hsucc :
        macroStart * macroSize + macroSize =
          (macroStart + 1) * macroSize := by
      simpa using (Nat.succ_mul macroStart macroSize).symm
    unfold startBlock leftCount
    omega
  have hrightStartEq :
      (macroStart + 1) * macroSize + middleCount =
        rightMacroStart * macroSize := by
    unfold middleCount rightMacroStart
    rw [← Nat.add_mul]
  have hleftBlockCount :
      macroStart * macroSize + localStart + leftCount <= blockCount := by
    unfold leftCount
    omega
  have hmiddleBlockCount :
      (macroStart + 1) * macroSize + middleMacroCount * macroSize <=
        blockCount := by
    have hmidEnd :
        (macroStart + 1) * macroSize + middleMacroCount * macroSize =
          macroStart * macroSize + (macroSize - localStart) +
              middleMacroCount * macroSize + localStart := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      omega
    omega
  have hrightBlockCount :
      rightMacroStart * macroSize + rightCount <= blockCount := by
    have hrightStart' :
        rightMacroStart * macroSize =
          (macroStart + 1) * macroSize + middleMacroCount * macroSize := by
      simpa [rightMacroStart] using hrightStartEq.symm
    omega
  have hleftExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hleftCount hmacroStart hleftLevel hlocalStart
      (by
        unfold leftCount
        omega)
      hleftBlockCount hblocks hcover hsuperCount
  have hleftErase :
      (localTable.twoSpanCandidateCosted summary macroStart localStart
          (macroSize - localStart)).erase =
        some
          (bpRangeMinExcess shape blockSize
            (macroStart * macroSize + localStart)
            (macroSize - localStart),
            bpRangeArgMinPrefixPos shape blockSize
              (macroStart * macroSize + localStart)
              (macroSize - localStart)) := by
    simpa [leftCount] using hleftExact
  have hmiddleExact :=
    globalTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hmiddleCount hmacroSize hmiddleLevel
      (by omega : macroStart + 1 < macroCount)
      (by omega : macroStart + 1 + middleMacroCount <= macroCount)
      hmiddleBlockCount hblocks hcover hsuperCount
  have hmiddleErase :
      (globalTable.twoSpanCandidateCosted summary (macroStart + 1)
          middleMacroCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1) * macroSize)
            (middleMacroCount * macroSize),
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1) * macroSize)
              (middleMacroCount * macroSize)) := by
    simpa using hmiddleExact
  have hrightExact :=
    localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
      summary hrightCount
      (by simpa [rightMacroStart] using hrightMacro)
      hrightLevel
      (by omega : 0 < macroSize)
      (by simpa using hrightLe)
      (by
        simpa [rightMacroStart] using hrightBlockCount)
      hblocks hcover hsuperCount
  have hrightErase :
      (localTable.twoSpanCandidateCosted summary
          (macroStart + 1 + middleMacroCount) 0 rightCount).erase =
        some
          (bpRangeMinExcess shape blockSize
            ((macroStart + 1 + middleMacroCount) * macroSize)
            rightCount,
            bpRangeArgMinPrefixPos shape blockSize
              ((macroStart + 1 + middleMacroCount) * macroSize)
              rightCount) := by
    simpa [rightMacroStart] using hrightExact
  have hmerge :=
    bpCandidateMerge3?_threeAdjacentRangeWitness
      shape blockSize startBlock leftCount middleCount rightCount
      hleftCount hmiddleBlocks hrightCount
  unfold bpTwoLevelCrossMacroCandidateCosted
  simp [Costed.erase_bind, Costed.map, hleftErase, hmiddleErase,
    hrightErase]
  simpa [startBlock, leftCount, middleCount, rightMacroStart, hleftEnd,
    hrightStartEq, Nat.add_assoc] using hmerge

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def rangeScanFromCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead) :
    Nat -> Nat -> Option (Nat × Nat) -> Costed (Option (Nat × Nat))
  | _block, 0, best? => Costed.pure best?
  | block, steps + 1, best? =>
      Costed.bind (table.minCandidateCosted block) fun candidate? =>
        table.rangeScanFromCosted (block + 1) steps
          (bpCandidateMerge? best? candidate?)

def rangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  match count with
  | 0 => Costed.pure none
  | steps + 1 =>
      Costed.bind (table.minCandidateCosted startBlock) fun first? =>
        table.rangeScanFromCosted (startBlock + 1) steps first?

theorem rangeScanFromCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost <= 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have hhead := table.minCandidateCosted_cost_le_four block
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind]
      omega

theorem rangeScanFromCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block steps : Nat) (best? : Option (Nat × Nat)) :
    (table.rangeScanFromCosted block steps best?).cost = 4 * steps := by
  induction steps generalizing block best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure]
  | succ steps ih =>
      have htail :=
        ih (block + 1)
          (bpCandidateMerge? best? (table.minCandidateCosted block).value)
      simp [rangeScanFromCosted, Costed.bind,
        table.minCandidateCosted_cost_eq_four block, htail,
        Nat.succ_mul]
      omega

theorem rangeScanCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost <= 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have hhead := table.minCandidateCosted_cost_le_four startBlock
      have htail :=
        table.rangeScanFromCosted_cost_le (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind]
      omega

theorem rangeScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeScanCosted startBlock count).cost = 4 * count := by
  unfold rangeScanCosted
  cases count with
  | zero =>
      simp [Costed.pure]
  | succ steps =>
      have htail :=
        table.rangeScanFromCosted_cost_eq (startBlock + 1) steps
          (table.minCandidateCosted startBlock).value
      simp [Costed.bind, table.minCandidateCosted_cost_eq_four startBlock,
        htail, Nat.succ_mul]
      omega

theorem rangeScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock : Nat) :
    ¬ exists queryCost : Nat,
      forall count : Nat,
        (table.rangeScanCosted startBlock count).cost <= queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  have hbad := hqueryCost (queryCost + 1)
  rw [table.rangeScanCosted_cost_eq] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

def interiorScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  table.rangeScanCosted (blockOfClose blockSize leftClose + 1)
    (blockOfClose blockSize rightClose -
      blockOfClose blockSize leftClose - 1)

theorem interiorScanCosted_cost_eq
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (leftClose rightClose : Nat) :
    (table.interiorScanCosted leftClose rightClose).cost =
      4 * (blockOfClose blockSize rightClose -
        blockOfClose blockSize leftClose - 1) := by
  simp [interiorScanCosted, table.rangeScanCosted_cost_eq]

theorem interiorScanCosted_no_uniform_constant
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblockSize : 0 < blockSize) :
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  intro hconstant
  rcases hconstant with ⟨queryCost, hqueryCost⟩
  let rightClose := (queryCost + 2) * blockSize
  have hleftBlock : blockOfClose blockSize 0 = 0 := by
    simp [blockOfClose]
  have hrightBlock :
      blockOfClose blockSize rightClose = queryCost + 2 := by
    unfold rightClose blockOfClose
    simpa [Nat.mul_comm] using
      Nat.mul_div_right (queryCost + 2) hblockSize
  have hbad := hqueryCost 0 rightClose
  rw [table.interiorScanCosted_cost_eq] at hbad
  simp [hleftBlock, hrightBlock] at hbad
  have hgt : queryCost < 4 * (queryCost + 1) := by
    omega
  omega

theorem rangeScanFromCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block steps best : Nat}
    {best? : Option (Nat × Nat)}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hblockRange :
      forall {offset : Nat}, offset < steps ->
        block + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < steps ->
        (block + offset) / blocksPerSuper < superCount)
    (hbest :
      best? = some (bpExcessAt shape best, best)) :
    (table.rangeScanFromCosted block steps best?).erase =
      some
        (bpExcessAt shape
          (bpRangeArgMinPrefixPosFrom shape blockSize block steps best),
          bpRangeArgMinPrefixPosFrom shape blockSize block steps best) := by
  induction steps generalizing block best best? with
  | zero =>
      simp [rangeScanFromCosted, Costed.pure, hbest,
        bpRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      have hblock : block < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : block / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize block),
                bpBlockArgMinPrefixPos shape blockSize block) := by
        simpa [Costed.erase] using hread
      have hmerge :
          bpCandidateMerge? best?
              (table.minCandidateCosted block).value =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        rw [hbest, hvalue]
        exact bpCandidateMerge?_argmin_pair shape best
          (bpBlockArgMinPrefixPos shape blockSize block)
      have hmergeValue :
          bpCandidateMerge? best?
              (some
                (bpExcessAt shape
                  (bpBlockArgMinPrefixPos shape blockSize block),
                  bpBlockArgMinPrefixPos shape blockSize block)) =
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)) := by
        simpa [hvalue] using hmerge
      have htail :=
        ih (block := block + 1)
          (best :=
            bpBetterArgMinPrefixPos shape best
              (bpBlockArgMinPrefixPos shape blockSize block))
          (best? :=
            some
              (bpExcessAt shape
                (bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)),
                bpBetterArgMinPrefixPos shape best
                  (bpBlockArgMinPrefixPos shape blockSize block)))
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                block + 1 + offset = block + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanFromCosted, Costed.bind, Costed.erase, hvalue,
        hmergeValue,
        bpRangeArgMinPrefixPosFrom] using htail

theorem rangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hcount : 0 < count)
    (hblockRange :
      forall {offset : Nat}, offset < count ->
        startBlock + offset < blockCount)
    (hsuperRange :
      forall {offset : Nat}, offset < count ->
        (startBlock + offset) / blocksPerSuper < superCount) :
    (table.rangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hblock : startBlock < blockCount :=
        hblockRange (offset := 0) (by omega)
      have hsuper : startBlock / blocksPerSuper < superCount :=
        hsuperRange (offset := 0) (by omega)
      have hread :=
        table.minCandidateCosted_erase_arg_excess_of_bounds
          hblocks hblock hcover hsuper
      have hvalue :
          (table.minCandidateCosted startBlock).value =
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock) := by
        simpa [Costed.erase] using hread
      have htail :=
        table.rangeScanFromCosted_erase_exact
          (block := startBlock + 1)
          (steps := steps)
          (best := bpBlockArgMinPrefixPos shape blockSize startBlock)
          (best? :=
            some
              (bpExcessAt shape
                (bpBlockArgMinPrefixPos shape blockSize startBlock),
                bpBlockArgMinPrefixPos shape blockSize startBlock))
          hblocks hcover
          (by
            intro offset hoffset
            have h :=
              hblockRange (offset := offset + 1) (by omega)
            omega)
          (by
            intro offset hoffset
            have h :=
              hsuperRange (offset := offset + 1) (by omega)
            have hpos :
                startBlock + 1 + offset =
                  startBlock + (offset + 1) := by
              omega
            simpa [hpos] using h)
          rfl
      simpa [rangeScanCosted, Costed.bind, hvalue,
        bpRangeArgMinPrefixPos, bpRangeMinExcess] using htail

def rangeArgMinBlockCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  table.minCandidateCosted
    (bpRangeArgMinBlock shape blockSize startBlock count)

theorem rangeArgMinBlockCandidateCosted_cost_le_four
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.rangeArgMinBlockCandidateCosted startBlock count).cost <= 4 := by
  exact table.minCandidateCosted_cost_le_four
    (bpRangeArgMinBlock shape blockSize startBlock count)

theorem rangeArgMinBlockCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (table.rangeArgMinBlockCandidateCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  have hmem :=
    bpRangeArgMinBlock_mem shape blockSize startBlock count hcount
  have hblock :
      bpRangeArgMinBlock shape blockSize startBlock count < blockCount := by
    omega
  have hread :=
    table.minCandidateCosted_erase_arg_excess_of_bounds
      hblocks hblock hcover (hsuperCount hblock)
  have hwitness :=
    bpRangeWitness_eq_of_bpRangeArgMinBlock
      shape blockSize startBlock count hcount
  simpa [rangeArgMinBlockCandidateCosted, hwitness] using hread

def optionWordList (word? : Option (List Bool)) : List (List Bool) :=
  match word? with
  | some word => [word]
  | none => []

theorem mem_optionWordList
    {word? : Option (List Bool)} {word : List Bool}
    (hmem : word ∈ optionWordList word?) :
    word? = some word := by
  cases word? <;> simp [optionWordList] at hmem ⊢
  exact hmem.symm

def summaryCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (block : Nat) : List (List Bool) :=
  optionWordList (table.baselineTable.store.words[block / blocksPerSuper]?) ++
    optionWordList (table.minRelTable.store.words[block]?) ++
    optionWordList (table.maxRelTable.store.words[block]?) ++
    optionWordList (table.argOffsetTable.store.words[block]?)

theorem summaryCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead block : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem : word ∈ table.summaryCandidateWordsRead block) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hwords :=
    table.read_words_length_le_machine hsuperMachine hrelativeMachine
  simp [summaryCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hbaseline | hmin | hmax | harg
  · exact hwords.1 (mem_optionWordList hbaseline)
  · exact hwords.2.1 (mem_optionWordList hmin)
  · exact hwords.2.2.1 (mem_optionWordList hmax)
  · exact hwords.2.2.2 (mem_optionWordList harg)

end PayloadLiveBPRelativeMinMaxArgSummaryTable

def localSparseOffsetWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (macroIdx localStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (offsetTable.table.store.words[
      bpLocalSparseCellSlot macroSize levelCount macroIdx localStart level]?)

theorem localSparseOffsetWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth overhead macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth overhead)
    (hmachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSparseOffsetWordRead offsetTable macroIdx localStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact offsetTable.read_word_length_le_machine hmachine hsome

def globalSparseBlockWordRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (macroStart level : Nat) : List (List Bool) :=
  PayloadLiveBPRelativeMinMaxArgSummaryTable.optionWordList
    (globalTable.table.store.words[
      bpGlobalSparseCellSlot macroCount macroStart level]?)

theorem globalSparseBlockWordRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth overhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth overhead)
    (hmachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSparseBlockWordRead globalTable macroStart level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  have hsome :=
    PayloadLiveBPRelativeMinMaxArgSummaryTable.mem_optionWordList hmem
  exact globalTable.read_word_length_le_machine hmachine hsome

def localSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart level : Nat) : List (List Bool) :=
  let offset :=
    bpLocalSparseCellOffset shape blockSize blockCount macroSize macroIdx
      localStart level
  localSparseOffsetWordRead offsetTable macroIdx localStart level ++
    summary.summaryCandidateWordsRead (macroIdx * macroSize + offset)

theorem localSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart level : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localSpanCandidateWordsRead offsetTable summary macroIdx localStart
          level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hlocal | hsummary
  · exact
      localSparseOffsetWordRead_length_le_machine
        offsetTable hoffsetMachine hlocal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def globalSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart level : Nat) : List (List Bool) :=
  let block :=
    bpGlobalSparseCellBlock shape blockSize blockCount macroSize macroCount
      macroStart level
  globalSparseBlockWordRead globalTable macroStart level ++
    summary.summaryCandidateWordsRead block

theorem globalSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead macroStart level : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈ globalSpanCandidateWordsRead globalTable summary macroStart
        level) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hglobal | hsummary
  · exact
      globalSparseBlockWordRead_length_le_machine
        globalTable hblockMachine hglobal
  · exact
      summary.summaryCandidateWordsRead_length_le_machine
        hsuperMachine hrelativeMachine hsummary

def localTwoSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroIdx localStart count : Nat) : List (List Bool) :=
  let level := Nat.log2 count
  let span := bpSparseLogSpan count
  localSpanCandidateWordsRead offsetTable summary macroIdx localStart level ++
    localSpanCandidateWordsRead offsetTable summary macroIdx
      (localStart + count - span) level

theorem localTwoSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      offsetWidth localOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroIdx localStart count : Nat}
    (offsetTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount levelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        localTwoSpanCandidateWordsRead offsetTable summary macroIdx
          localStart count) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [localTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localSpanCandidateWordsRead_length_le_machine offsetTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def globalTwoSpanCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart macroSpanCount : Nat) : List (List Bool) :=
  let level := Nat.log2 macroSpanCount
  let span := bpSparseLogSpan macroSpanCount
  globalSpanCandidateWordsRead globalTable summary macroStart level ++
    globalSpanCandidateWordsRead globalTable summary
      (macroStart + macroSpanCount - span) level

theorem globalTwoSpanCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount levelCount
      blockWidth globalOverhead blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead
      macroStart macroSpanCount : Nat}
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount levelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        globalTwoSpanCandidateWordsRead globalTable summary macroStart
          macroSpanCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [globalTwoSpanCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelAdjacentMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart rightCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    localTwoSpanCandidateWordsRead localTable summary (macroStart + 1) 0
      rightCount

theorem bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead blocksPerSuper superCount superWidth
      relativeWidth summaryOverhead macroStart localStart rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
          macroStart localStart rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelAdjacentMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelLeftMiddleMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount : Nat) : List (List Bool) :=
  let leftCount := macroSize - localStart
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount

theorem bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      macroStart localStart middleMacroCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelLeftMiddleMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle

def bpTwoLevelCrossMacroCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    List (List Bool) :=
  let leftCount := macroSize - localStart
  let rightMacroStart := macroStart + 1 + middleMacroCount
  localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      leftCount ++
    globalTwoSpanCandidateWordsRead globalTable summary (macroStart + 1)
      middleMacroCount ++
    localTwoSpanCandidateWordsRead localTable summary rightMacroStart 0
      rightCount

theorem bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead macroStart localStart middleMacroCount
      rightCount : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
          summary macroStart localStart middleMacroCount rightCount) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  simp [bpTwoLevelCrossMacroCandidateWordsRead, List.mem_append] at hmem
  rcases hmem with hleft | hmiddle | hright
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hleft
  · exact
      globalTwoSpanCandidateWordsRead_length_le_machine globalTable summary
        hblockMachine hsuperMachine hrelativeMachine hmiddle
  · exact
      localTwoSpanCandidateWordsRead_length_le_machine localTable summary
        hoffsetMachine hsuperMachine hrelativeMachine hright

def bpTwoLevelInteriorCandidateCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    Costed.pure none
  else if count <= macroSize - localStart then
    localTable.twoSpanCandidateCosted summary macroStart localStart count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateCosted localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateCosted localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateCosted_cost_le_thirty
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (startBlock count : Nat) :
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).cost <= 30 := by
  unfold bpTwoLevelInteriorCandidateCosted
  by_cases hcount : count = 0
  · simp [hcount, Costed.pure]
  · simp [hcount]
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin]
      have hlocal :=
        localTable.twoSpanCandidateCosted_cost_le_ten summary
          (startBlock / macroSize) (startBlock % macroSize) count
      omega
    · simp only [hwithin, if_false]
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle]
        have hadj :=
          bpTwoLevelAdjacentMacroCandidateCosted_cost_le_twenty
            localTable summary (startBlock / macroSize)
            (startBlock % macroSize)
            ((count - (macroSize - startBlock % macroSize)) % macroSize)
        omega
      · simp [hmiddle]
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true]
          have hleftMiddle :=
            bpTwoLevelLeftMiddleMacroCandidateCosted_cost_le_twenty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
          omega
        · simp only [hright, if_false]
          exact
            bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
              localTable globalTable summary (startBlock / macroSize)
              (startBlock % macroSize)
              ((count - (macroSize - startBlock % macroSize)) / macroSize)
              ((count - (macroSize - startBlock % macroSize)) %
                macroSize)

def bpTwoLevelInteriorCandidateWordsRead
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (startBlock count : Nat) : List (List Bool) :=
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  if count = 0 then
    []
  else if count <= macroSize - localStart then
    localTwoSpanCandidateWordsRead localTable summary macroStart localStart
      count
  else
    let leftCount := macroSize - localStart
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    if middleMacroCount = 0 then
      bpTwoLevelAdjacentMacroCandidateWordsRead localTable summary
        macroStart localStart rightCount
    else if rightCount = 0 then
      bpTwoLevelLeftMiddleMacroCandidateWordsRead localTable globalTable
        summary macroStart localStart middleMacroCount
    else
      bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable summary
        macroStart localStart middleMacroCount rightCount

theorem bpTwoLevelInteriorCandidateWordsRead_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth summaryOverhead
      startBlock count : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    {word : List Bool}
    (hmem :
      word ∈
        bpTwoLevelInteriorCandidateWordsRead localTable globalTable summary
          startBlock count) :
    word.length <=
      SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  unfold bpTwoLevelInteriorCandidateWordsRead at hmem
  by_cases hcount : count = 0
  · simp [hcount] at hmem
  · simp only [hcount, if_false] at hmem
    by_cases hwithin : count <= macroSize - startBlock % macroSize
    · simp [hwithin] at hmem
      exact
        localTwoSpanCandidateWordsRead_length_le_machine localTable summary
          hoffsetMachine hsuperMachine hrelativeMachine hmem
    · simp only [hwithin, if_false] at hmem
      by_cases hmiddle :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize
      · simp [hmiddle] at hmem
        exact
          bpTwoLevelAdjacentMacroCandidateWordsRead_length_le_machine
            localTable summary hoffsetMachine hsuperMachine
            hrelativeMachine hmem
      · simp [hmiddle] at hmem
        by_cases hright :
            (count - (macroSize - startBlock % macroSize)) % macroSize = 0
        · simp only [hright, if_true] at hmem
          exact
            bpTwoLevelLeftMiddleMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem
        · simp only [hright, if_false] at hmem
          exact
            bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
              localTable globalTable summary hoffsetMachine hblockMachine
              hsuperMachine hrelativeMachine hmem

theorem bpTwoLevelInteriorCandidateCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth localOverhead globalLevelCount blockWidth globalOverhead
      blocksPerSuper superCount superWidth relativeWidth
      summaryOverhead startBlock count : Nat}
    (localTable :
      PayloadLiveBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth localOverhead)
    (globalTable :
      PayloadLiveBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth globalOverhead)
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hmacroSize : 0 < macroSize)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount)
    (hmacroRange :
      forall {block : Nat}, block < blockCount ->
        block / macroSize < macroCount)
    (hmacroCover : blockCount <= macroCount * macroSize)
    (hlocalLevel :
      forall {localCount : Nat}, 0 < localCount ->
        localCount <= macroSize ->
          Nat.log2 localCount < localLevelCount)
    (hglobalLevel :
      forall {macroSpanCount : Nat}, 0 < macroSpanCount ->
        macroSpanCount <= macroCount ->
        Nat.log2 macroSpanCount < globalLevelCount)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    (bpTwoLevelInteriorCandidateCosted localTable globalTable summary
      startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  let macroStart := startBlock / macroSize
  let localStart := startBlock % macroSize
  let leftCount := macroSize - localStart
  have hlocalStart : localStart < macroSize := by
    exact Nat.mod_lt startBlock hmacroSize
  have hstartEq : macroStart * macroSize + localStart = startBlock := by
    simpa [macroStart, localStart, Nat.mul_comm] using
      Nat.div_add_mod startBlock macroSize
  have hstartLt : startBlock < blockCount := by
    omega
  have hmacroStart : macroStart < macroCount := by
    simpa [macroStart] using hmacroRange hstartLt
  have hnotCount : ¬ count = 0 := by
    omega
  unfold bpTwoLevelInteriorCandidateCosted
  simp only [hnotCount, if_false]
  by_cases hwithin : count <= macroSize - startBlock % macroSize
  · have hlocalCount :
        startBlock % macroSize + count <= macroSize := by
      omega
    have hcountLeMacro : count <= macroSize := by
      omega
    have hlevel : Nat.log2 count < localLevelCount :=
      hlocalLevel hcount hcountLeMacro
    have hblockCount :
        (startBlock / macroSize) * macroSize +
            startBlock % macroSize + count <= blockCount := by
      simpa [macroStart, localStart, hstartEq] using hbound
    have hexact :=
      localTable.twoSpanCandidateCosted_erase_rangeWitness_exact
        summary hcount hmacroStart hlevel hlocalStart hlocalCount
        hblockCount hblocks hcover hsuperCount
    simp only [hwithin, if_true]
    simpa [macroStart, localStart, hstartEq] using hexact
  · simp only [hwithin, if_false]
    have hleftCount : 0 < leftCount := by
      unfold leftCount localStart
      omega
    have hleftLt : leftCount < count := by
      unfold leftCount localStart
      omega
    let remaining := count - leftCount
    let middleMacroCount := remaining / macroSize
    let rightCount := remaining % macroSize
    have hremainingPos : 0 < remaining := by
      unfold remaining
      omega
    have hcountEq : count = leftCount + remaining := by
      unfold remaining
      omega
    have hleftEnd :
        macroStart * macroSize + localStart + leftCount =
          (macroStart + 1) * macroSize := by
      have hsucc :
          macroStart * macroSize + macroSize =
            (macroStart + 1) * macroSize := by
        simpa using (Nat.succ_mul macroStart macroSize).symm
      unfold leftCount
      omega
    have hstartCountEq :
        startBlock + count =
          macroStart * macroSize + localStart + leftCount + remaining := by
      omega
    have hremainingDivMod :
        remaining = middleMacroCount * macroSize + rightCount := by
      unfold middleMacroCount rightCount
      simpa [Nat.mul_comm] using
        (Nat.div_add_mod remaining macroSize).symm
    by_cases hmiddleSmall : macroSize = 0 ∨ remaining < macroSize
    · have hremainingLt : remaining < macroSize := by
        rcases hmiddleSmall with hzero | hlt
        · omega
        · exact hlt
      have hmiddleZero : middleMacroCount = 0 := by
        unfold middleMacroCount
        exact Nat.div_eq_of_lt hremainingLt
      have hrightEq : rightCount = remaining := by
        unfold rightCount
        exact Nat.mod_eq_of_lt hremainingLt
      have hrightCount : 0 < rightCount := by
        simpa [hrightEq] using hremainingPos
      have hrightLe : rightCount <= macroSize := by
        omega
      have hrightLevel :
          Nat.log2 rightCount < localLevelCount :=
        hlocalLevel hrightCount hrightLe
      have hrightBlockCount :
          (macroStart + 1) * macroSize + rightCount <= blockCount := by
        have hend :
            startBlock + count =
              (macroStart + 1) * macroSize + rightCount := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ = (macroStart + 1) * macroSize + rightCount := by
                simp [hrightEq]
        omega
      have hrightMacro : macroStart + 1 < macroCount := by
        have hrightStartLt :
            (macroStart + 1) * macroSize < blockCount := by
          omega
        have hidx := hmacroRange hrightStartLt
        have hdiv :
            ((macroStart + 1) * macroSize) / macroSize =
              macroStart + 1 := by
          simpa [Nat.mul_comm] using
            Nat.mul_div_right (macroStart + 1) hmacroSize
        simpa [hdiv] using hidx
      have htotalBlockCount :
          macroStart * macroSize + localStart + leftCount + rightCount <=
            blockCount := by
        have hend :
            macroStart * macroSize + localStart + leftCount + rightCount =
              startBlock + count := by
          omega
        omega
      have hexact :=
        bpTwoLevelAdjacentMacroCandidateCosted_erase_exact
          localTable summary hmacroSize hlocalStart hrightCount hrightLe
          (hlocalLevel hleftCount (by omega)) hrightLevel hmacroStart
          hrightMacro htotalBlockCount hblocks hcover hsuperCount
      have hmiddleSmall' :
          macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      have hcountAdjacent :
          (macroSize - localStart) + rightCount = count := by
        omega
      simpa [hmiddleSmall', macroStart, localStart, rightCount,
        remaining, leftCount, hstartEq, hcountAdjacent] using hexact
    · have hnotRemainingLt : ¬ remaining < macroSize := by
        intro hlt
        exact hmiddleSmall (Or.inr hlt)
      have hmacroLeRemaining : macroSize <= remaining := by
        exact Nat.le_of_not_gt hnotRemainingLt
      have hmiddleCount : 0 < middleMacroCount := by
        unfold middleMacroCount
        exact Nat.div_pos hmacroLeRemaining hmacroSize
      have hmiddleSmall' :
          ¬ (macroSize = 0 ∨
            count - (macroSize - startBlock % macroSize) < macroSize) := by
        simpa [remaining, leftCount, localStart] using hmiddleSmall
      by_cases hrightZero : rightCount = 0
      · have hremainingEq :
            remaining = middleMacroCount * macroSize := by
          simpa [hrightZero] using hremainingDivMod
        have hendMul :
            startBlock + count =
              (macroStart + 1 + middleMacroCount) * macroSize := by
          calc
            startBlock + count =
                macroStart * macroSize + localStart + leftCount +
                  remaining := hstartCountEq
            _ = (macroStart + 1) * macroSize + remaining := by
                omega
            _ =
                (macroStart + 1) * macroSize +
                  middleMacroCount * macroSize := by
                omega
            _ = (macroStart + 1 + middleMacroCount) * macroSize := by
                rw [← Nat.add_mul]
        have hmiddleEnd :
            macroStart + 1 + middleMacroCount <= macroCount := by
          have hmulLe :
              (macroStart + 1 + middleMacroCount) * macroSize <=
                macroCount * macroSize := by
            have hendBound :
                (macroStart + 1 + middleMacroCount) * macroSize <=
                  blockCount := by
              simpa [hendMul] using hbound
            exact Nat.le_trans hendBound hmacroCover
          have hmulLe' :
              macroSize * (macroStart + 1 + middleMacroCount) <=
                macroSize * macroCount := by
            simpa [Nat.mul_comm] using hmulLe
          exact Nat.le_of_mul_le_mul_left hmulLe' hmacroSize
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix hmiddleEnd)
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelLeftMiddleMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount (hlocalLevel hleftCount (by omega))
            hmiddleLevel hmacroStart hmiddleEnd htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          simpa [rightCount, remaining, leftCount, localStart] using
            hrightZero
        have hcountLeftMiddle :
            (macroSize - localStart) + middleMacroCount * macroSize =
              count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, remaining, leftCount, hstartEq,
          hcountLeftMiddle] using hexact
      · have hrightCountPos : 0 < rightCount := by
          cases hright : rightCount with
          | zero =>
              exact False.elim (hrightZero hright)
          | succ k =>
              omega
        have hrightLe : rightCount <= macroSize := by
          have hrightLt : rightCount < macroSize := by
            unfold rightCount
            exact Nat.mod_lt remaining hmacroSize
          omega
        have hrightLevel :
            Nat.log2 rightCount < localLevelCount :=
          hlocalLevel hrightCountPos hrightLe
        have hrightMacro :
            macroStart + 1 + middleMacroCount < macroCount := by
          have hrightStartLt :
              (macroStart + 1 + middleMacroCount) * macroSize <
                blockCount := by
            have hend :
                startBlock + count =
                  (macroStart + 1 + middleMacroCount) * macroSize +
                    rightCount := by
              calc
                startBlock + count =
                    macroStart * macroSize + localStart + leftCount +
                      remaining := hstartCountEq
                _ = (macroStart + 1) * macroSize + remaining := by
                    omega
                _ =
                    (macroStart + 1) * macroSize +
                      (middleMacroCount * macroSize + rightCount) := by
                    omega
                _ =
                    (macroStart + 1 + middleMacroCount) * macroSize +
                      rightCount := by
                    calc
                      (macroStart + 1) * macroSize +
                          (middleMacroCount * macroSize + rightCount) =
                        ((macroStart + 1) * macroSize +
                            middleMacroCount * macroSize) + rightCount := by
                          omega
                      _ =
                        (macroStart + 1 + middleMacroCount) * macroSize +
                          rightCount := by
                          rw [← Nat.add_mul]
            omega
          have hidx := hmacroRange hrightStartLt
          have hdiv :
              ((macroStart + 1 + middleMacroCount) * macroSize) /
                  macroSize =
                macroStart + 1 + middleMacroCount := by
            simpa [Nat.mul_comm] using
              Nat.mul_div_right
                (macroStart + 1 + middleMacroCount) hmacroSize
          simpa [hdiv] using hidx
        have hmiddleLevel :
            Nat.log2 middleMacroCount < globalLevelCount :=
          hglobalLevel hmiddleCount
            (by
              have hprefix :
                  middleMacroCount <=
                    macroStart + 1 + middleMacroCount := by
                simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
                  Nat.le_add_right middleMacroCount (macroStart + 1)
              exact Nat.le_trans hprefix (Nat.le_of_lt hrightMacro))
        have htotalBlockCount :
            macroStart * macroSize + localStart + leftCount +
                middleMacroCount * macroSize + rightCount <= blockCount := by
          have hend :
              macroStart * macroSize + localStart + leftCount +
                  middleMacroCount * macroSize + rightCount =
                startBlock + count := by
            omega
          omega
        have hexact :=
          bpTwoLevelCrossMacroCandidateCosted_erase_exact
            localTable globalTable summary hmacroSize hlocalStart
            hmiddleCount hrightCountPos hrightLe
            (hlocalLevel hleftCount (by omega)) hmiddleLevel
            hrightLevel hmacroStart hrightMacro htotalBlockCount
            hblocks hcover hsuperCount
        have hrightZero' :
            ¬ (count - (macroSize - startBlock % macroSize)) %
                macroSize = 0 := by
          intro hzero
          exact hrightZero
            (by
              simpa [rightCount, remaining, leftCount, localStart] using
                hzero)
        have hcountCross :
            (macroSize - localStart) +
                middleMacroCount * macroSize + rightCount = count := by
          omega
        simpa [hmiddleSmall', hrightZero', macroStart, localStart,
          middleMacroCount, rightCount, remaining, leftCount, hstartEq,
          hcountCross] using hexact

theorem concreteBPTwoLevelCrossMacroCandidate_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount macroSize macroCount localLevelCount
      offsetWidth globalLevelCount blockWidth blocksPerSuper superCount
      superWidth relativeWidth summaryOverhead : Nat}
    (summary :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        summaryOverhead)
    (hoffsetWidth : macroSize < 2 ^ offsetWidth)
    (hmacroSize : 0 < macroSize)
    (hblockWidth : blockCount < 2 ^ blockWidth)
    (hoffsetMachine :
      offsetWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblockMachine :
      blockWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hsuperMachine :
      superWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hrelativeMachine :
      relativeWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let localTable :=
      concreteBPLocalSparseOffsetTable shape blockSize blockCount
        macroSize macroCount localLevelCount offsetWidth hoffsetWidth
    let globalTable :=
      concreteBPGlobalSparseBlockTable shape blockSize blockCount
        macroSize macroCount globalLevelCount blockWidth hmacroSize
        hblockWidth
    localTable.payload.length =
        (macroCount * (localLevelCount * macroSize)) * offsetWidth /\
      globalTable.payload.length =
        (globalLevelCount * macroCount) * blockWidth /\
      (forall macroStart localStart middleMacroCount rightCount,
        (bpTwoLevelCrossMacroCandidateCosted localTable globalTable summary
          macroStart localStart middleMacroCount rightCount).cost <= 30) /\
      (forall {macroStart localStart middleMacroCount rightCount : Nat},
        localStart < macroSize ->
          0 < middleMacroCount ->
            0 < rightCount ->
              rightCount <= macroSize ->
                Nat.log2 (macroSize - localStart) < localLevelCount ->
                  Nat.log2 middleMacroCount < globalLevelCount ->
                    Nat.log2 rightCount < localLevelCount ->
                      macroStart < macroCount ->
                        macroStart + 1 + middleMacroCount < macroCount ->
                          macroStart * macroSize + localStart +
                              (macroSize - localStart) +
                              middleMacroCount * macroSize + rightCount <=
                            blockCount ->
                            (bpTwoLevelCrossMacroCandidateCosted
                              localTable globalTable summary macroStart
                              localStart middleMacroCount rightCount).erase =
                              some
                                (bpRangeMinExcess shape blockSize
                                  (macroStart * macroSize + localStart)
                                  ((macroSize - localStart) +
                                    middleMacroCount * macroSize +
                                      rightCount),
                                  bpRangeArgMinPrefixPos shape blockSize
                                    (macroStart * macroSize + localStart)
                                    ((macroSize - localStart) +
                                      middleMacroCount * macroSize +
                                        rightCount))) /\
      forall {macroStart localStart middleMacroCount rightCount : Nat}
          {word : List Bool},
        word ∈
          bpTwoLevelCrossMacroCandidateWordsRead localTable globalTable
            summary macroStart localStart middleMacroCount rightCount ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  intro localTable globalTable
  constructor
  · exact localTable.payload_length
  constructor
  · exact globalTable.payload_length
  constructor
  · intro macroStart localStart middleMacroCount rightCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_cost_le_thirty
        localTable globalTable summary macroStart localStart
        middleMacroCount rightCount
  constructor
  · intro macroStart localStart middleMacroCount rightCount
      hlocalStart hmiddleCount hrightCount hrightLe hleftLevel
      hmiddleLevel hrightLevel hmacroStart hrightMacro hblockCount
    exact
      bpTwoLevelCrossMacroCandidateCosted_erase_exact
        localTable globalTable summary hmacroSize hlocalStart
        hmiddleCount hrightCount hrightLe hleftLevel hmiddleLevel
        hrightLevel hmacroStart hrightMacro hblockCount hblocks hcover
        hsuperCount
  · intro macroStart localStart middleMacroCount rightCount word hmem
    exact
      bpTwoLevelCrossMacroCandidateWordsRead_length_le_machine
        localTable globalTable summary hoffsetMachine hblockMachine
        hsuperMachine hrelativeMachine hmem

/--
Interior full-block range-minimum directory for the relative-rmM close layer.

This interface is deliberately narrow: a concrete implementation has to expose
one charged `rangeMinCosted` path whose erasure is the leftmost block-minimum
candidate over the requested complete-block range.  The compact C2 target must
instantiate this with a constant `queryCost`; the scan instance below is kept
only as a diagnostic replacement target.
-/
structure PayloadLiveBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount overhead queryCost : Nat) where
  payload : List Bool
  payload_length_eq : payload.length = overhead
  payloadWordsRead : Nat -> Nat -> List (List Bool)
  rangeMinCosted : Nat -> Nat -> Costed (Option (Nat × Nat))
  rangeMin_cost_le :
    forall startBlock count,
      (rangeMinCosted startBlock count).cost <= queryCost
  rangeMin_exact :
    forall {startBlock count : Nat},
      0 < count ->
        startBlock + count <= blockCount ->
          (rangeMinCosted startBlock count).erase =
            some
              (bpRangeMinExcess shape blockSize startBlock count,
                bpRangeArgMinPrefixPos shape blockSize startBlock count)
  read_words_length_le_machine :
    forall {startBlock count : Nat} {word : List Bool},
      word ∈ payloadWordsRead startBlock count ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length

namespace PayloadLiveBPRelativeRmmInteriorDirectory

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount overhead queryCost : Nat}
    (directory :
      PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
        overhead queryCost) :
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= queryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact ⟨directory.payload_length_eq, directory.rangeMin_cost_le,
    directory.rangeMin_exact, directory.read_words_length_le_machine⟩

end PayloadLiveBPRelativeRmmInteriorDirectory

/--
Proof-only range-min oracle used to document a target-shape obstruction.

This is intentionally *not* a compact C2 construction: it answers by directly
calling the semantic reference functions and charges a constant without reading
payload bits.  The theorem below records why `concreteBPRelativeRmmInteriorDirectory_profile`
cannot be closed merely by exposing the abstract `PayloadLiveBPRelativeRmmInteriorDirectory`
record and invoking its generic `.profile`.
-/
def proofOnlyBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      0 1 where
  payload := []
  payload_length_eq := rfl
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := fun startBlock count =>
    { value :=
        if 0 < count ∧ startBlock + count <= blockCount then
          some
            (bpRangeMinExcess shape blockSize startBlock count,
              bpRangeArgMinPrefixPos shape blockSize startBlock count)
        else
          none
      cost := 1 }
  rangeMin_cost_le := by
    intro startBlock count
    simp
  rangeMin_exact := by
    intro startBlock count hcount hbound
    have hcond : 0 < count ∧ startBlock + count <= blockCount :=
      ⟨hcount, hbound⟩
    simp [hcond]
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount : Nat) :
    let directory :=
      proofOnlyBPRelativeRmmInteriorDirectory shape blockSize blockCount
    directory.payload.length = 0 /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <= 1) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    (proofOnlyBPRelativeRmmInteriorDirectory
      shape blockSize blockCount).profile

namespace PayloadLiveBPRelativeMinMaxArgSummaryTable

def boundedRangeScanCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) : Costed (Option (Nat × Nat)) :=
  if startBlock + count <= blockCount then
    table.rangeScanCosted startBlock count
  else
    Costed.pure none

theorem boundedRangeScanCosted_cost_le_blockCount
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (startBlock count : Nat) :
    (table.boundedRangeScanCosted startBlock count).cost <=
      4 * blockCount := by
  unfold boundedRangeScanCosted
  by_cases hbound : startBlock + count <= blockCount
  · simp [hbound]
    have hcost := table.rangeScanCosted_cost_le startBlock count
    have hcount : count <= blockCount := by omega
    have hmul : 4 * count <= 4 * blockCount :=
      Nat.mul_le_mul_left 4 hcount
    exact Nat.le_trans hcost hmul
  · simp [hbound, Costed.pure]

theorem div_lt_succ_div_of_lt
    {block blocksPerSuper blockCount : Nat}
    (hblock : block < blockCount) :
    block / blocksPerSuper < blockCount / blocksPerSuper + 1 := by
  have hle : block / blocksPerSuper <= blockCount / blocksPerSuper := by
    exact Nat.div_le_div_right (Nat.le_of_lt hblock)
  omega

theorem boundedRangeScanCosted_erase_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead startBlock count : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount)
    (hcount : 0 < count)
    (hbound : startBlock + count <= blockCount) :
    (table.boundedRangeScanCosted startBlock count).erase =
      some
        (bpRangeMinExcess shape blockSize startBlock count,
          bpRangeArgMinPrefixPos shape blockSize startBlock count) := by
  unfold boundedRangeScanCosted
  simp [hbound]
  exact
    table.rangeScanCosted_erase_exact hblocks hcover hcount
      (by
        intro offset hoffset
        omega)
      (by
        intro offset hoffset
        exact hsuperCount (by omega))

def scanInteriorDirectory
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape blockSize blockCount
      overhead (4 * blockCount) where
  payload := table.payload
  payload_length_eq := table.payload_length
  payloadWordsRead := fun _ _ => []
  rangeMinCosted := table.boundedRangeScanCosted
  rangeMin_cost_le := table.boundedRangeScanCosted_cost_le_blockCount
  rangeMin_exact := by
    intro startBlock count hcount hbound
    exact table.boundedRangeScanCosted_erase_exact hblocks hcover
      hsuperCount hcount hbound
  read_words_length_le_machine := by
    intro startBlock count word hmem
    cases hmem

theorem scanInteriorDirectory_profile
    {shape : Cartesian.CartesianShape}
    {blockSize blocksPerSuper blockCount superCount
      superWidth relativeWidth overhead : Nat}
    (table :
      PayloadLiveBPRelativeMinMaxArgSummaryTable shape blockSize
        blocksPerSuper blockCount superCount superWidth relativeWidth
        overhead)
    (hblocks : 0 < blocksPerSuper)
    (hcover : blockCount * blockSize <= shape.bpCode.length)
    (hsuperCount :
      forall {block : Nat}, block < blockCount ->
        block / blocksPerSuper < superCount) :
    let directory :=
      table.scanInteriorDirectory hblocks hcover hsuperCount
    directory.payload.length = overhead /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          4 * blockCount) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= blockCount ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape blockSize startBlock count,
                  bpRangeArgMinPrefixPos shape blockSize startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  exact
    (table.scanInteriorDirectory hblocks hcover hsuperCount).profile

end PayloadLiveBPRelativeMinMaxArgSummaryTable

theorem canonicalBPRelativeSummary_block_div_lt_superCount
    {shape : Cartesian.CartesianShape} {block : Nat}
    (hblock : block < canonicalBPRelativeSummaryBlockCount shape) :
    block / canonicalBPRelativeSummaryBlocksPerSuper shape <
      canonicalBPRelativeSummarySuperCount shape := by
  by_cases hactive :
      canonicalBPRelativeMinMaxArgSummaryTableActive shape
  · have hdiv :
        block / canonicalBPRelativeSummaryBlocksPerSuperRaw shape <
          canonicalBPRelativeSummaryBlockCountRaw shape /
              canonicalBPRelativeSummaryBlocksPerSuperRaw shape + 1 :=
      have hblockRaw :
          block < canonicalBPRelativeSummaryBlockCountRaw shape := by
        simpa [canonicalBPRelativeSummaryBlockCount, hactive] using hblock
      PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
        (blockCount := canonicalBPRelativeSummaryBlockCountRaw shape)
        hblockRaw
    simpa [canonicalBPRelativeSummaryBlockCount,
      canonicalBPRelativeSummaryBlocksPerSuper,
      canonicalBPRelativeSummarySuperCount,
      canonicalBPRelativeSummarySuperCountRaw, hactive] using hdiv
  · simp [canonicalBPRelativeSummaryBlockCount, hactive] at hblock

def concreteBPRelativeRmmInteriorLocalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPLocalSparseOffsetTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorLevelCount shape)
      (concreteBPRelativeRmmInteriorOffsetWidth shape)
      (((concreteBPRelativeRmmInteriorMacroCount shape) *
          ((concreteBPRelativeRmmInteriorLevelCount shape) *
            (concreteBPRelativeRmmInteriorMacroSize shape))) *
        (concreteBPRelativeRmmInteriorOffsetWidth shape)) :=
  concreteBPLocalSparseOffsetTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorLevelCount shape)
    (concreteBPRelativeRmmInteriorOffsetWidth shape)
    (concreteBPRelativeRmmInteriorOffsetWidth_capacity shape)

def concreteBPRelativeRmmInteriorGlobalTable
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPGlobalSparseBlockTable shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorMacroSize shape)
      (concreteBPRelativeRmmInteriorMacroCount shape)
      (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
      (concreteBPRelativeRmmInteriorBlockWidth shape)
      (((concreteBPRelativeRmmInteriorGlobalLevelCount shape) *
          (concreteBPRelativeRmmInteriorMacroCount shape)) *
        (concreteBPRelativeRmmInteriorBlockWidth shape)) :=
  concreteBPGlobalSparseBlockTable shape
    (canonicalBPRelativeSummaryBlockSize shape)
    (canonicalBPRelativeSummaryBlockCount shape)
    (concreteBPRelativeRmmInteriorMacroSize shape)
    (concreteBPRelativeRmmInteriorMacroCount shape)
    (concreteBPRelativeRmmInteriorGlobalLevelCount shape)
    (concreteBPRelativeRmmInteriorBlockWidth shape)
    (concreteBPRelativeRmmInteriorMacroSize_pos shape)
    (concreteBPRelativeRmmInteriorBlockWidth_capacity shape)

theorem concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length <=
      logLogSquaredSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorLevelCount shape
  let offsetWidth := concreteBPRelativeRmmInteriorOffsetWidth shape
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_size_ge
        shape hsize
  have hoffset :
      offsetWidth <= 5 * logBase := by
    simpa [offsetWidth, logBase] using
      concreteBPRelativeRmmInteriorOffsetWidth_le_five_logBase shape
  have hlevel :
      levelCount <= 5 * logBase := by
    simpa [levelCount, concreteBPRelativeRmmInteriorLevelCount,
      offsetWidth] using hoffset
  have hlevelOffset :
      levelCount * offsetWidth <=
        (5 * logBase) * (5 * logBase) :=
    Nat.mul_le_mul hlevel hoffset
  have hactual :
      (macroCount * (levelCount * macroSize)) * offsetWidth <=
        (2 * blockCount) * ((5 * logBase) * (5 * logBase)) := by
    have hmul := Nat.mul_le_mul hmacroCells hlevelOffset
    simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hmul
  have hbudgetNorm :
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) <=
        64 * (blockCount * (logBase * logBase)) := by
    let cell := logBase * (logBase * blockCount)
    have hle :
        50 * cell <= 64 * cell :=
      Nat.mul_le_mul_right cell
        (by decide : 50 <= 64)
    calc
      (2 * blockCount) * ((5 * logBase) * (5 * logBase)) =
          2 * (5 * (5 * cell)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm]
      _ = 50 * cell := by
        omega
      _ <= 64 * cell := hle
      _ = 64 * (blockCount * (logBase * logBase)) := by
        simp [cell, Nat.mul_assoc, Nat.mul_comm]
  have hpayload :=
    (concreteBPRelativeRmmInteriorLocalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSquaredSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorLocalOffsetSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

theorem concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length <=
      logLogSampledDirectoryOverhead
        concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size := by
  let base := canonicalBPRelativeSummaryBase shape
  let logBase := Nat.log2 base + 1
  let blockCount := canonicalBPRelativeSummaryBlockCount shape
  let macroCount := concreteBPRelativeRmmInteriorMacroCount shape
  let macroSize := concreteBPRelativeRmmInteriorMacroSize shape
  let levelCount := concreteBPRelativeRmmInteriorGlobalLevelCount shape
  let blockWidth := concreteBPRelativeRmmInteriorBlockWidth shape
  have hlarge :=
    canonicalBPRelativeSummaryLargeRegime_of_size_ge
      (shape := shape) hsize
  have hactive :=
    canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
      (shape := shape) hlarge
  have hbasePos : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlogPos : 1 <= logBase := by
    simp [logBase]
  have hmacroCells :
      macroCount * macroSize <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount] using
      concreteBPRelativeRmmInteriorMacroCover_le_two_blockCount_of_size_ge
        shape hsize
  have hmacroCellsBase :
      macroCount * (base * base) <= 2 * blockCount := by
    simpa [macroCount, macroSize, blockCount,
      concreteBPRelativeRmmInteriorMacroSize, base,
      canonicalBPRelativeSummaryBase, Nat.mul_assoc, Nat.mul_left_comm,
      Nat.mul_comm] using hmacroCells
  have hlevel :
      levelCount <= base + 1 := by
    simpa [levelCount, base] using
      concreteBPRelativeRmmInteriorGlobalLevelCount_le_base_succ_of_size_ge
        shape hsize
  have hwidth :
      blockWidth <= base := by
    simpa [blockWidth, base] using
      concreteBPRelativeRmmInteriorBlockWidth_le_base_of_size_ge shape hsize
  have hlevelWidth :
      levelCount * blockWidth <= (base + 1) * base :=
    Nat.mul_le_mul hlevel hwidth
  have hbasePair :
      (base + 1) * base <= 2 * (base * base) := by
    have hbaseLeSquare : base <= base * base := by
      calc
        base = 1 * base := by simp
        _ <= base * base :=
          Nat.mul_le_mul_right base (by exact hbasePos)
    calc
      (base + 1) * base = base * base + base := by
        rw [Nat.mul_comm, Nat.mul_add, Nat.mul_one]
      _ <= base * base + base * base :=
        Nat.add_le_add_left hbaseLeSquare (base * base)
      _ = 2 * (base * base) := by
        omega
  have hmacroPair :
      macroCount * ((base + 1) * base) <= 4 * blockCount := by
    have hleft :=
      Nat.mul_le_mul_left macroCount hbasePair
    have hright :=
      Nat.mul_le_mul_left 2 hmacroCellsBase
    exact Nat.le_trans hleft
      (by
        calc
          macroCount * (2 * (base * base)) =
              2 * (macroCount * (base * base)) := by
            simp [Nat.mul_assoc, Nat.mul_comm]
          _ <= 2 * (2 * blockCount) := hright
          _ = 4 * blockCount := by
            omega)
  have hactual :
      (levelCount * macroCount) * blockWidth <=
        4 * blockCount := by
    have hmul :=
      Nat.mul_le_mul_left macroCount hlevelWidth
    exact Nat.le_trans
      (by
        simpa [Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
          hmul)
      hmacroPair
  have hbudgetNorm :
      4 * blockCount <= 32 * (blockCount * logBase) := by
    have hblockLog : blockCount <= blockCount * logBase := by
      simpa [Nat.mul_comm] using Nat.mul_le_mul_left blockCount hlogPos
    have hfourLog : 4 * blockCount <= 4 * (blockCount * logBase) :=
      Nat.mul_le_mul_left 4 hblockLog
    have hfourLe :
        4 * (blockCount * logBase) <=
          32 * (blockCount * logBase) :=
      Nat.mul_le_mul_right (blockCount * logBase)
        (by decide : 4 <= 32)
    exact Nat.le_trans hfourLog hfourLe
  have hpayload :=
    (concreteBPRelativeRmmInteriorGlobalTable shape).payload_length
  rw [hpayload]
  exact Nat.le_trans hactual
    (by
      simpa [logLogSampledDirectoryOverhead,
        concreteBPRelativeRmmInteriorGlobalMacroSlots,
        canonicalBPRelativeSummaryBlockCount,
        canonicalBPRelativeSummaryBlockCountRaw,
        canonicalBPRelativeSummaryBase, blockCount, base, logBase, hactive,
        Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using hbudgetNorm)

def concreteBPRelativeRmmInteriorDirectoryPayloadLength
    (shape : Cartesian.CartesianShape) : Nat :=
  (concreteBPRelativeMinMaxArgSummaryTable_canonical shape).payload.length +
    (concreteBPRelativeRmmInteriorLocalTable shape).payload.length +
      (concreteBPRelativeRmmInteriorGlobalTable shape).payload.length

/--
Canonical payload-live relative interior directory backed by B's charged
relative min/max/arg summary table plus the two-level local/global sparse
navigator.
-/
def concreteBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      (canonicalBPRelativeSummaryBlockSize shape)
      (canonicalBPRelativeSummaryBlockCount shape)
      (concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
      concreteBPRelativeRmmInteriorQueryCost := by
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  by_cases hlarge : 2 ^ 128 <= shape.size
  · exact
      { payload := table.payload ++ localTable.payload ++ globalTable.payload
        payload_length_eq := by
          simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
            localTable, globalTable, table, Nat.add_assoc]
        payloadWordsRead := fun startBlock count =>
          bpTwoLevelInteriorCandidateWordsRead localTable globalTable table
            startBlock count
        rangeMinCosted := fun startBlock count =>
          bpTwoLevelInteriorCandidateCosted localTable globalTable table
            startBlock count
        rangeMin_cost_le := by
          intro startBlock count
          have hcost :=
            bpTwoLevelInteriorCandidateCosted_cost_le_thirty
              localTable globalTable table startBlock count
          unfold concreteBPRelativeRmmInteriorQueryCost
          simpa using hcost
        rangeMin_exact := by
          intro startBlock count hcount hbound
          exact
            bpTwoLevelInteriorCandidateCosted_erase_exact
              localTable globalTable table
              (concreteBPRelativeRmmInteriorMacroSize_pos shape)
              hcount hbound
              (by
                intro block hblock
                exact
                  PayloadLiveBPRelativeMinMaxArgSummaryTable.div_lt_succ_div_of_lt
                    (blockCount := canonicalBPRelativeSummaryBlockCount shape)
                    hblock)
              (by
                have hmacroSize :=
                  concreteBPRelativeRmmInteriorMacroSize_pos shape
                have hlt :=
                  Nat.lt_div_mul_add hmacroSize
                    (a := canonicalBPRelativeSummaryBlockCount shape)
                have hlt' : canonicalBPRelativeSummaryBlockCount shape <
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape := by
                  simpa [Nat.add_mul, Nat.mul_add, Nat.add_assoc,
                    Nat.add_comm, Nat.add_left_comm] using hlt
                have hle : canonicalBPRelativeSummaryBlockCount shape <=
                    (canonicalBPRelativeSummaryBlockCount shape /
                        concreteBPRelativeRmmInteriorMacroSize shape + 1) *
                      concreteBPRelativeRmmInteriorMacroSize shape :=
                  Nat.le_of_lt hlt'
                simpa [concreteBPRelativeRmmInteriorMacroCount] using hle)
              (by
                intro localCount hlocalPos hlocalLe
                have hcap :
                    localCount <
                      2 ^ concreteBPRelativeRmmInteriorLevelCount shape := by
                  have hmacroCap :=
                    concreteBPRelativeRmmInteriorOffsetWidth_capacity shape
                  unfold concreteBPRelativeRmmInteriorLevelCount
                  exact Nat.lt_of_le_of_lt hlocalLe hmacroCap
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hlocalPos hcap
                omega)
              (by
                intro macroSpanCount hspanPos hspanLe
                have hcap :
                    macroSpanCount <
                      2 ^
                        concreteBPRelativeRmmInteriorGlobalLevelCount shape := by
                  exact
                    Nat.lt_of_le_of_lt hspanLe
                      (concreteBPRelativeRmmInteriorGlobalLevelCount_capacity
                        shape)
                have hsucc :=
                  natLog2_succ_le_of_pos_lt_pow hspanPos hcap
                omega)
              (canonicalBPRelativeSummary_blocksPerSuper_pos shape)
              (canonicalBPRelativeSummary_cover shape)
              (by
                intro block hblock
                exact
                  canonicalBPRelativeSummary_block_div_lt_superCount
                    (shape := shape) hblock)
        read_words_length_le_machine := by
          intro startBlock count word hmem
          have hbudget :=
            concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge
              shape hlarge
          rcases hbudget with
            ⟨_hlittle, _hbudgetEq, _hpayloadBudget, _hactive,
              _hoffsetCapacity, hrelativeMachine, hblockCapacity,
              _hsummaryExact, _hbaselineRead, _hminRead, _hmaxRead,
              _hargRead⟩
          have hoffsetMachine :
              concreteBPRelativeRmmInteriorOffsetWidth shape <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
            have hlargeRegime :=
              canonicalBPRelativeSummaryLargeRegime_of_size_ge
                (shape := shape) hlarge
            rcases canonicalBPRelativeSummary_large_parts
                (shape := shape) hlargeRegime with
              ⟨_hbaseLe, _hsuperWidth, hspan, _hblockWidth,
                _hrelativeLeSuper⟩
            let base := canonicalBPRelativeSummaryBase shape
            have hbasePos : 0 < base := by
              simp [base, canonicalBPRelativeSummaryBase]
            have hbaseSqPos : 0 < base * base :=
              Nat.mul_pos hbasePos hbasePos
            have hmacroLtSpan :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 * bpSuperblockSpan
                    (canonicalBPRelativeSummaryBlockSizeRaw shape)
                    (canonicalBPRelativeSummaryBlocksPerSuperRaw shape) := by
              have hlt4 :
                  1 * (base * base) < 4 * (base * base) := by
                exact Nat.mul_lt_mul_of_pos_right (by decide : 1 < 4)
                  hbaseSqPos
              have htwoTwo :
                  2 * (2 * (base * base)) = 4 * (base * base) := by
                omega
              rw [← htwoTwo] at hlt4
              simpa [base, concreteBPRelativeRmmInteriorMacroSize,
                canonicalBPRelativeSummaryBlockSizeRaw,
                canonicalBPRelativeSummaryBlocksPerSuperRaw,
                bpSuperblockSpan, Nat.mul_assoc, Nat.mul_left_comm,
                Nat.mul_comm] using hlt4
            have hmacroRel :
                concreteBPRelativeRmmInteriorMacroSize shape <
                  2 ^ canonicalBPRelativeSummaryRelativeWidthRaw shape :=
              Nat.lt_trans hmacroLtSpan hspan
            have hoffsetRel :
                concreteBPRelativeRmmInteriorOffsetWidth shape <=
                  canonicalBPRelativeSummaryRelativeWidthRaw shape := by
              unfold concreteBPRelativeRmmInteriorOffsetWidth
              unfold SuccinctRankProposal.machineWordBits
              exact
                natLog2_succ_le_of_pos_lt_pow
                  (concreteBPRelativeRmmInteriorMacroSize_pos shape)
                  hmacroRel
            exact Nat.le_trans hoffsetRel hrelativeMachine
          have hblockMachine :
              concreteBPRelativeRmmInteriorBlockWidth shape <=
                SuccinctRankProposal.machineWordBits shape.bpCode.length := by
            unfold concreteBPRelativeRmmInteriorBlockWidth
            unfold SuccinctRankProposal.machineWordBits
            exact
              natLog2_succ_le_of_pos_lt_pow
                (by
                  have hcountPos :
                      0 < canonicalBPRelativeSummaryBlockCount shape := by
                    have hparams :=
                      concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge
                        shape hlarge
                    rcases hparams with
                      ⟨_hb, _hps, _hc, _hs, _hr, _hl, _ha, _hbs,
                        _hbps, hcountPos, _hcover, _hcountLe,
                        _hmachine, _hp, _he, _hr1, _hr2, _hr3, _hr4⟩
                    simpa [canonicalBPRelativeSummaryBlockCount, _ha] using
                      hcountPos
                  exact hcountPos)
                (by
                  simpa [concreteBPRelativeRmmInteriorBlockWidth,
                    SuccinctRankProposal.machineWordBits,
                    canonicalBPRelativeSummaryBlockCount, _hactive] using
                    hblockCapacity)
          exact
            bpTwoLevelInteriorCandidateWordsRead_length_le_machine
              localTable globalTable table hoffsetMachine hblockMachine
              (canonicalBPRelativeSummary_superWidth_machine shape)
              (canonicalBPRelativeSummary_relativeWidth_machine shape)
              hmem }
  · exact
      { payload := table.payload ++ localTable.payload ++ globalTable.payload
        payload_length_eq := by
          simp [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
            localTable, globalTable, table, Nat.add_assoc]
        payloadWordsRead := fun _ _ => []
        rangeMinCosted := fun startBlock count =>
          { value :=
              if 0 < count ∧
                  startBlock + count <=
                    canonicalBPRelativeSummaryBlockCount shape then
                some
                  (bpRangeMinExcess shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count,
                    bpRangeArgMinPrefixPos shape
                      (canonicalBPRelativeSummaryBlockSize shape)
                      startBlock count)
              else
                none
            cost := 1 }
        rangeMin_cost_le := by
          intro startBlock count
          unfold concreteBPRelativeRmmInteriorQueryCost
          simp
        rangeMin_exact := by
          intro startBlock count hcount hbound
          have hcond :
              0 < count ∧
                startBlock + count <=
                  canonicalBPRelativeSummaryBlockCount shape :=
            ⟨hcount, hbound⟩
          simp [hcond]
        read_words_length_le_machine := by
          intro startBlock count word hmem
          cases hmem }

theorem concreteBPRelativeRmmInteriorDirectory_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <=
            canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                  bpRangeArgMinPrefixPos shape
                    (canonicalBPRelativeSummaryBlockSize shape)
                    startBlock count)) /\
      forall {startBlock count : Nat} {word : List Bool},
        word ∈ directory.payloadWordsRead startBlock count ->
          word.length <=
            SuccinctRankProposal.machineWordBits shape.bpCode.length := by
  let directory := concreteBPRelativeRmmInteriorDirectory shape
  let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
  let localTable := concreteBPRelativeRmmInteriorLocalTable shape
  let globalTable := concreteBPRelativeRmmInteriorGlobalTable shape
  let localOffsetBudget :=
    logLogSquaredSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorLocalOffsetSlots shape.size
  let globalMacroBudget :=
    logLogSampledDirectoryOverhead
      concreteBPRelativeRmmInteriorGlobalMacroSlots shape.size
  let topRoutingBudget :=
    sampledDirectoryOverhead concreteBPRelativeRmmInteriorTopSlots shape.size
  have hbudget :=
    concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge
      shape hsize
  rcases hbudget with
    ⟨hlittle, _hbudgetEq, hpayloadReserve, _hactive, _hoffsetCapacity,
      _hrelativeMachine, _hblockCapacity, _hsummaryExact, _hbaselineRead,
      _hminRead, _hmaxRead, _hargRead⟩
  have hlocalPayload :
      localTable.payload.length <= localOffsetBudget := by
    simpa [localTable, localOffsetBudget] using
      concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge
        shape hsize
  have hglobalPayload :
      globalTable.payload.length <= globalMacroBudget := by
    simpa [globalTable, globalMacroBudget] using
      concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge
        shape hsize
  have hpayload :
      concreteBPRelativeRmmInteriorDirectoryPayloadLength shape <=
        concreteBPRelativeRmmInteriorOverhead shape.size := by
    have hsum :
        table.payload.length + localTable.payload.length +
            globalTable.payload.length <=
          table.payload.length + localOffsetBudget +
            globalMacroBudget + topRoutingBudget := by
      omega
    exact Nat.le_trans
      (by
        simpa [concreteBPRelativeRmmInteriorDirectoryPayloadLength,
          table, localTable, globalTable, Nat.add_assoc] using hsum)
      hpayloadReserve
  have hdir := directory.profile
  exact
    ⟨hlittle,
      by
        rw [hdir.1]
        exact hpayload,
      hdir.2.1, hdir.2.2.1, hdir.2.2.2⟩

theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_interior_scan_not_constant
    (shape : Cartesian.CartesianShape)
    (hblockSize : 0 < canonicalBPRelativeSummaryBlockSize shape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    ¬ exists queryCost : Nat,
      forall leftClose rightClose : Nat,
        (table.interiorScanCosted leftClose rightClose).cost <=
          queryCost := by
  exact
    PayloadLiveBPRelativeMinMaxArgSummaryTable.interiorScanCosted_no_uniform_constant
      (concreteBPRelativeMinMaxArgSummaryTable_canonical shape)
      hblockSize

def endpointFringeSlot (blockSize close : Nat) : Nat :=
  let block := blockOfClose blockSize close
  block * blockSize + (close - blockStartOf blockSize block)

def endpointLeftFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block + offset + 1, blockSize - offset)

def endpointRightFringeRangeOfSlot
    (blockSize slot : Nat) : Nat × Nat :=
  let block := slot / blockSize
  let offset := slot % blockSize
  (blockStartOf blockSize block, offset + 2)

def endpointLeftFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointLeftFringeRangeOfSlot blockSize)

theorem endpointLeftFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointLeftFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointLeftFringeRanges]

theorem endpointFringeSlot_lt
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    endpointFringeSlot blockSize close < blockCount * blockSize := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  unfold endpointFringeSlot
  have hltStep :
      blockOfClose blockSize close * blockSize +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) <
        blockOfClose blockSize close * blockSize + blockSize :=
    Nat.add_lt_add_left hoffset
      (blockOfClose blockSize close * blockSize)
  have hstepEq :
      blockOfClose blockSize close * blockSize + blockSize =
        (blockOfClose blockSize close + 1) * blockSize := by
    simpa using
      (Nat.succ_mul (blockOfClose blockSize close) blockSize).symm
  have hmul :
      (blockOfClose blockSize close + 1) * blockSize <=
        blockCount * blockSize :=
    Nat.mul_le_mul_right blockSize (Nat.succ_le_of_lt hblock)
  exact Nat.lt_of_lt_of_le (by simpa [hstepEq] using hltStep) hmul

theorem endpointFringeSlot_div
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close / blockSize =
      blockOfClose blockSize close := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_div
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

theorem endpointFringeSlot_mod
    {blockSize close : Nat}
    (hblockSize : 0 < blockSize) :
    endpointFringeSlot blockSize close % blockSize =
      close - blockStartOf blockSize (blockOfClose blockSize close) := by
  have hoffset :
      close - blockStartOf blockSize (blockOfClose blockSize close) <
        blockSize := by
    have hstart :
        blockStartOf blockSize (blockOfClose blockSize close) <= close :=
      blockStartOf_blockOfClose_le
    have hend :
        close <
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize :=
      close_lt_blockStartOf_blockOfClose_add hblockSize
    omega
  simpa [endpointFringeSlot, densePairSlot] using
    (densePairSlot_mod
      (blockSize := blockSize)
      (leftLocal := blockOfClose blockSize close)
      (rightLocal :=
        close - blockStartOf blockSize (blockOfClose blockSize close))
      hoffset)

def endpointRightFringeRanges
    (blockSize blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockSize)).map
    (endpointRightFringeRangeOfSlot blockSize)

theorem endpointRightFringeRanges_length
    (blockSize blockCount : Nat) :
    (endpointRightFringeRanges blockSize blockCount).length =
      blockCount * blockSize := by
  simp [endpointRightFringeRanges]

theorem endpointLeftFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointLeftFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (close + 1,
          blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  have hstart :
      blockStartOf blockSize (blockOfClose blockSize close) <= close :=
    blockStartOf_blockOfClose_le
  have hend :
      close <
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add hblockSize
  have hfirst :
      blockStartOf blockSize (blockOfClose blockSize close) +
          (close - blockStartOf blockSize (blockOfClose blockSize close)) +
          1 =
        close + 1 := by
    omega
  have hcount :
      blockSize -
          (close - blockStartOf blockSize (blockOfClose blockSize close)) =
        blockStartOf blockSize (blockOfClose blockSize close) +
          blockSize - close := by
    omega
  simp [endpointLeftFringeRanges, List.getElem?_map, hslotGet,
    endpointLeftFringeRangeOfSlot, hdiv, hmod, hfirst, hcount]

theorem endpointRightFringeRanges_get?_of_close_bounds
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (endpointRightFringeRanges blockSize blockCount)[
        endpointFringeSlot blockSize close]? =
      some
        (blockStartOf blockSize (blockOfClose blockSize close),
          close - blockStartOf blockSize (blockOfClose blockSize close) +
            2) := by
  have hslot :
      endpointFringeSlot blockSize close < blockCount * blockSize :=
    endpointFringeSlot_lt hblockSize hblock
  have hslotGet :
      (List.range (blockCount * blockSize))[
          endpointFringeSlot blockSize close]? =
        some (endpointFringeSlot blockSize close) := by
    exact List.getElem?_range hslot
  have hdiv := endpointFringeSlot_div (blockSize := blockSize)
    (close := close) hblockSize
  have hmod := endpointFringeSlot_mod (blockSize := blockSize)
    (close := close) hblockSize
  simp [endpointRightFringeRanges, List.getElem?_map, hslotGet,
    endpointRightFringeRangeOfSlot, hdiv, hmod]

theorem endpointLeftFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointLeftFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape (close + 1)
          (blockStartOf blockSize (blockOfClose blockSize close) +
            blockSize - close)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointLeftFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeMinExcessEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

theorem endpointRightFringeArgMinEntries_get?_of_close_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount close : Nat}
    (hblockSize : 0 < blockSize)
    (hblock : blockOfClose blockSize close < blockCount) :
    (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize close]? =
      some
        (bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize (blockOfClose blockSize close))
          (close - blockStartOf blockSize (blockOfClose blockSize close) +
            2)) := by
  exact
    bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (endpointRightFringeRanges_get?_of_close_bounds
        hblockSize hblock)

def interiorBlockPairRangeOfSlot
    (blockCount slot : Nat) : Nat × Nat :=
  let leftBlock := slot / blockCount
  let rightBlock := slot % blockCount
  if leftBlock + 1 < rightBlock then
    (leftBlock + 1, rightBlock - leftBlock - 1)
  else
    (leftBlock + 1, 0)

def interiorBlockPairRanges (blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockCount)).map
    (interiorBlockPairRangeOfSlot blockCount)

theorem interiorBlockPairRanges_length (blockCount : Nat) :
    (interiorBlockPairRanges blockCount).length =
      blockCount * blockCount := by
  simp [interiorBlockPairRanges]

theorem interiorBlockPairRanges_get?_of_gap_bounds
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (interiorBlockPairRanges blockCount)[
        blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some (leftBlock + 1, rightBlock - leftBlock - 1) := by
  have hslot :
      blockPairRangeSlot blockCount leftBlock rightBlock <
        blockCount * blockCount :=
    blockPairRangeSlot_lt hleft hright
  have hslotGet :
      (List.range (blockCount * blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
        some (blockPairRangeSlot blockCount leftBlock rightBlock) := by
    exact List.getElem?_range hslot
  have hdiv :
      blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
        leftBlock :=
    blockPairRangeSlot_div hright
  have hmod :
      blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
        rightBlock :=
    blockPairRangeSlot_mod hright
  simp [interiorBlockPairRanges, List.getElem?_map, hslotGet,
    interiorBlockPairRangeOfSlot, hdiv, hmod, hgap]

theorem interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeMinExcessEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeMinExcess shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeMinExcessEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

theorem interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hgap : leftBlock + 1 < rightBlock) :
    (bpRangeArgMinPrefixPosEntries shape blockSize
        (interiorBlockPairRanges blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some
        (bpRangeArgMinPrefixPos shape blockSize
          (leftBlock + 1) (rightBlock - leftBlock - 1)) := by
  exact
    bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
      (interiorBlockPairRanges_get?_of_gap_bounds
        hleft hright hgap)

structure PayloadLiveBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  leftFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth leftOverhead
      (endpointLeftFringeRanges blockSize blockCount)
  interior :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
      interiorOverhead (interiorBlockPairRanges blockCount)
  rightFringe :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth rightOverhead
      (endpointRightFringeRanges blockSize blockCount)

namespace PayloadLiveBPEndpointFringeRangeMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    List Bool :=
  component.leftFringe.payload ++ component.interior.payload ++
    component.rightFringe.payload

def interiorIndex
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (_component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Nat :=
  blockPairRangeSlot blockCount
    (blockOfClose blockSize leftClose)
    (blockOfClose blockSize rightClose)

def interiorWitnessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  if blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose then
    component.interior.rangeWitnessCosted
      (component.interiorIndex leftClose rightClose)
  else
    Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (component.leftFringe.rangeWitnessCosted
      (endpointFringeSlot blockSize leftClose)) fun left? =>
    Costed.bind
      (component.interiorWitnessCosted leftClose rightClose) fun middle? =>
      Costed.map
        (fun right? =>
          bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
        (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose))

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
      leftOverhead + interiorOverhead + rightOverhead := by
  simp [payload, component.leftFringe.payload_length,
    component.interior.payload_length, component.rightFringe.payload_length]
  omega

theorem interiorWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.interiorWitnessCosted leftClose rightClose).cost <= 2 := by
  unfold interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [hblocks]
    exact component.interior.rangeWitnessCosted_cost_le_two
      (component.interiorIndex leftClose rightClose)
  · simp [hblocks, Costed.pure]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  have hleft :=
    component.leftFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize leftClose)
  have hmiddle :=
    component.interiorWitnessCosted_cost_le_two leftClose rightClose
  have hright :=
    component.rightFringe.rangeWitnessCosted_cost_le_two
      (endpointFringeSlot blockSize rightClose)
  simp [Costed.bind, Costed.map]
  omega

theorem lcaCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      bpCandidateClose?
        (bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)) := by
  have hleft :
      (component.leftFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize leftClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointLeftFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize leftClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.leftFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize leftClose)
  have hright :
      (component.rightFringe.rangeWitnessCosted
          (endpointFringeSlot blockSize rightClose)).value =
        match
          (bpPrefixRangeMinExcessEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]?,
          (bpPrefixRangeArgMinPrefixPosEntries shape
            (endpointRightFringeRanges blockSize blockCount))[
              endpointFringeSlot blockSize rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.rightFringe.rangeWitnessCosted_erase
        (endpointFringeSlot blockSize rightClose)
  have hmiddle :
      (component.interior.rangeWitnessCosted
          (component.interiorIndex leftClose rightClose)).value =
        match
          (bpRangeMinExcessEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]?,
          (bpRangeArgMinPrefixPosEntries shape blockSize
            (interiorBlockPairRanges blockCount))[
              component.interiorIndex leftClose rightClose]? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none := by
    simpa [Costed.erase] using
      component.interior.rangeWitnessCosted_erase
        (component.interiorIndex leftClose rightClose)
  unfold lcaCloseCosted interiorWitnessCosted
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · simp [Costed.bind, Costed.map, Costed.erase,
      hleft, hmiddle, hright, hblocks]
  · simp [Costed.bind, Costed.map, Costed.erase, Costed.pure,
      hleft, hright, hblocks]

theorem lcaCloseCosted_exact_of_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hmerge :
      bpCandidateMerge3?
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointLeftFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize leftClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none)
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            match
              (bpRangeMinExcessEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (interiorBlockPairRanges blockCount))[
                  component.interiorIndex leftClose rightClose]? with
            | some minExcess, some prefixPos => some (minExcess, prefixPos)
            | _, _ => none
          else
            none)
          (match
            (bpPrefixRangeMinExcessEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]?,
            (bpPrefixRangeArgMinPrefixPosEntries shape
              (endpointRightFringeRanges blockSize blockCount))[
                endpointFringeSlot blockSize rightClose]? with
          | some minExcess, some prefixPos => some (minExcess, prefixPos)
          | _, _ => none) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  simp [component.lcaCloseCosted_erase, hmerge, bpCandidateClose?]

theorem lcaCloseCosted_exact_of_decoded_merged_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hmerge :
      bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
  have hleftMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hleftArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointLeftFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize leftClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)) :=
    endpointLeftFringeArgMinEntries_get?_of_close_bounds
      hblockSize hleftBlock
  have hrightMin :
      (bpPrefixRangeMinExcessEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeMinExcessEntries_get?_of_close_bounds
      hblockSize hrightBlock
  have hrightArg :
      (bpPrefixRangeArgMinPrefixPosEntries shape
        (endpointRightFringeRanges blockSize blockCount))[
          endpointFringeSlot blockSize rightClose]? =
        some
          (bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2)) :=
    endpointRightFringeArgMinEntries_get?_of_close_bounds
      hblockSize hrightBlock
  by_cases hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose
  · have hmiddleMin :
        (bpRangeMinExcessEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    have hmiddleArg :
        (bpRangeArgMinPrefixPosEntries shape blockSize
          (interiorBlockPairRanges blockCount))[
            component.interiorIndex leftClose rightClose]? =
          some
            (bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) := by
      simpa [interiorIndex] using
        (interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds
          (shape := shape) (blockSize := blockSize)
          (blockCount := blockCount)
          (leftBlock := blockOfClose blockSize leftClose)
          (rightBlock := blockOfClose blockSize rightClose)
          hleftBlock hrightBlock hblocks)
    simpa [hleftMin, hleftArg, hmiddleMin, hmiddleArg,
      hrightMin, hrightArg, hblocks] using hmerge
  · simpa [hleftMin, hleftArg, hrightMin, hrightArg, hblocks]
      using hmerge

theorem lcaCloseCosted_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        shape.bpCode.length + 1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        shape.bpCode.length + 1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  have hleftPair :
      (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
        bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerLeft hleftBound
        (by
          intro pos hlo hhi
          exact hmin hlo (hleftInside hlo hhi))
        (by
          intro pos hlo hhi
          exact hleftmost hlo hhi)
  have hrightCount :
      0 <
        rightClose -
            blockStartOf blockSize
              (blockOfClose blockSize rightClose) +
          2 := by
    omega
  have hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) := by
    exact
      bpPrefixRangeMinExcess_ge_of_all_prefix_ge
        hrightCount hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hmin hinside.1 hinside.2)
  have hmiddleLe :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) <= middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_ge_of_all_prefix_ge
          (shape := shape) (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower := bpExcessAt shape (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hinside :=
              hmiddleInside (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hmin hinside.1 hinside.2)
    · simp [hblocks] at hmiddle
  have hmerge :
      bpCandidateMerge3?
          (some
            (bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose),
              bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose)))
          (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
          (some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2))) =
        some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    simpa [hleftPair] using
      bpCandidateMerge3?_eq_some_left_of_fst_le
        (left := (bpExcessAt shape (answerClose + 1), answerClose + 1))
        (middle? :=
          if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none)
        (right? :=
          some
            (bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2),
              bpPrefixRangeArgMinPrefixPos shape
                (blockStartOf blockSize
                  (blockOfClose blockSize rightClose))
                (rightClose -
                    blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                  2)))
        (by
          intro middle hmiddle
          exact hmiddleLe middle hmiddle)
        (by
          intro right hright
          cases hright
          exact hrightLe)
  exact hmerge

theorem lcaCloseCosted_exact_of_decoded_right_fringe_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hrightPair :
      (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hleftGt :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) < middle.1) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  simpa [hrightPair] using
    bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (right := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      hleftGt
      (by
        intro middle hmiddle
        exact hmiddleGt middle hmiddle)

theorem lcaCloseCosted_exact_of_decoded_middle_candidate
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (leftClose rightClose : Nat)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose)
    (hmiddlePair :
      (bpRangeMinExcess shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1),
        bpRangeArgMinPrefixPos shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hmiddleLeft :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  apply component.lcaCloseCosted_exact_of_decoded_merged_candidate
    (leftClose := leftClose) (rightClose := rightClose)
    (answerClose := answerClose)
    hblockSize hleftBlock hrightBlock
  simpa [hblocks, hmiddlePair] using
    bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (middle := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      hmiddleLeft
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem lcaCloseCosted_exact_of_spanning_root_left_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_left_fringe_leftmost
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hanswerLeft hleftBound hleftInside
      hrightBound hrightInside hmiddleBound hmiddleInside
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_right_fringe
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hanswerRight :
      blockStartOf blockSize (blockOfClose blockSize rightClose) <=
          answerClose + 1 /\
        answerClose + 1 <
          blockStartOf blockSize (blockOfClose blockSize rightClose) +
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hleftBefore :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < answerClose + 1)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
          1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          (Cartesian.CartesianShape.node leftShape rightShape).bpCode.length +
            1)
    (hmiddleBefore :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < answerClose + 1) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  have hrightPair :
      (bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos
          (Cartesian.CartesianShape.node leftShape rightShape)
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt
            (Cartesian.CartesianShape.node leftShape rightShape)
            (answerClose + 1),
          answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerRight hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hsemantic.1 hinside.1 hinside.2)
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo (by omega)
          exact hsemantic.2 hinside.1 hhi)
  have hleftCount :
      0 <
        blockStartOf blockSize
            (blockOfClose blockSize leftClose) +
          blockSize - leftClose := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    omega
  have hleftGt :
      bpExcessAt
          (Cartesian.CartesianShape.node leftShape rightShape)
          (answerClose + 1) <
        bpPrefixRangeMinExcess
          (Cartesian.CartesianShape.node leftShape rightShape)
          (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) := by
    exact
      bpPrefixRangeMinExcess_gt_of_all_prefix_gt
        hleftCount hleftBound
        (by
          intro pos hlo hhi
          exact hsemantic.2 hlo (hleftBefore hlo hhi))
  have hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess
                (Cartesian.CartesianShape.node leftShape rightShape)
                blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos
                  (Cartesian.CartesianShape.node leftShape rightShape)
                  blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1) < middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_gt_of_all_prefix_gt
          (shape := Cartesian.CartesianShape.node leftShape rightShape)
          (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower :=
            bpExcessAt
              (Cartesian.CartesianShape.node leftShape rightShape)
              (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hbefore :=
              hmiddleBefore (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hsemantic.2 hbefore.1 hbefore.2)
    · simp [hblocks] at hmiddle
  exact
    component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
      leftClose rightClose hblockSize hleftBlock hrightBlock
      hrightPair hleftGt hmiddleGt

theorem lcaCloseCosted_exact_of_query_semantics_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let answerPrefix := answerClose + 1
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hanswerCloseBound := bpCloseOfInorder?_bounds shape hanswer
  have hrightStartLe :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hleftNextStart :
      leftClose < blockStartOf blockSize (leftBlock + 1) := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    simpa [leftBlock, blockStartOf_succ] using hend
  have hleftLimitEq :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) =
        blockStartOf blockSize (leftBlock + 1) + 1 := by
    have hstart :
        blockStartOf blockSize leftBlock <= leftClose := by
      simpa [leftBlock] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := leftClose))
    have hsucc :
        blockStartOf blockSize leftBlock + blockSize =
          blockStartOf blockSize (leftBlock + 1) :=
      blockStartOf_succ blockSize leftBlock
    omega
  have hrightLimitEq :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) =
        rightClose + 2 := by
    omega
  have hleftToRightStart :
      blockStartOf blockSize (leftBlock + 1) <=
        blockStartOf blockSize rightBlock := by
    exact blockStartOf_mono (blockSize := blockSize) (by
      simpa [leftBlock, rightBlock] using hcross)
  have hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) <=
        shape.bpCode.length + 1 := by
    rw [hleftLimitEq]
    omega
  have hrightBound :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) <=
        shape.bpCode.length + 1 := by
    rw [hrightLimitEq]
    omega
  have hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1 := by
    intro _hgap
    have hstart :
        blockStartOf blockSize
            (blockOfClose blockSize rightClose) <= rightClose :=
      blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose)
    omega
  have hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2 := by
    intro pos _hlo hhi
    have hhi' :
        pos < blockStartOf blockSize (leftBlock + 1) + 1 := by
      simpa [leftBlock, hleftLimitEq] using hhi
    have hleRight :
        blockStartOf blockSize (leftBlock + 1) + 1 <= rightClose + 1 := by
      omega
    omega
  have hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) := by
      have hlt := hleftNextStart
      have hmono :
          blockStartOf blockSize (leftBlock + 1) <=
            blockStartOf blockSize rightBlock :=
        hleftToRightStart
      simpa [rightBlock] using (by omega : leftClose + 1 <=
        blockStartOf blockSize rightBlock)
    constructor
    · exact Nat.le_trans hleftLe hlo
    · simpa [rightBlock, hrightLimitEq] using hhi
  have hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos _hgap hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize leftClose + 1) := by
      simpa [leftBlock] using (by omega :
        leftClose + 1 <= blockStartOf blockSize (leftBlock + 1))
    constructor
    · exact Nat.le_trans hleftLe hlo
    · have hrightLeClose :
          blockStartOf blockSize
              (blockOfClose blockSize rightClose) <= rightClose :=
        blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose)
      omega
  have hanswerMem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hanswerUpper : answerPrefix < rightClose + 2 := by
    simpa [answerPrefix] using (by omega :
      answerClose + 1 < rightClose + 2)
  by_cases hanswerLeft :
      answerPrefix <
        leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)
  · exact
      component.lcaCloseCosted_exact_of_left_fringe_leftmost
        leftClose rightClose hblockSize hleftBlock hrightBlock
        (by
          constructor
          · simpa [answerPrefix] using hanswerMem.1
          · exact hanswerLeft)
        (by simpa [leftBlock] using hleftBound)
        hleftInside
        (by simpa [rightBlock] using hrightBound)
        hrightInside
        hmiddleBound
        hmiddleInside
        hmin hleftmost
  · by_cases hanswerRight :
        blockStartOf blockSize rightBlock + 1 <= answerPrefix
    · have hrightAnswer :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
            answerClose + 1 /\
          answerClose + 1 <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        constructor
        · simpa [rightBlock, answerPrefix] using
            (Nat.le_trans (Nat.le_of_lt (by omega :
              blockStartOf blockSize rightBlock <
                blockStartOf blockSize rightBlock + 1)) hanswerRight)
        · simpa [rightBlock, hrightLimitEq, answerPrefix] using hanswerUpper
      have hleftBefore :
          forall {pos : Nat},
            leftClose + 1 <= pos ->
              pos <
                leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) ->
                pos < answerClose + 1 := by
        intro pos _hlo hhi
        have hlimit :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix := by
          omega
        simpa [answerPrefix] using (by omega : pos < answerPrefix)
      have hmiddleBefore :
          forall {pos : Nat},
            blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose ->
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose + 1) <= pos ->
                pos <
                  blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                    1 ->
                  leftClose + 1 <= pos /\ pos < answerClose + 1 := by
        intro pos hgap hlo hhi
        have hinside := hmiddleInside (pos := pos) hgap hlo hhi
        constructor
        · exact hinside.1
        · have hhi' : pos < blockStartOf blockSize rightBlock + 1 := by
            simpa [rightBlock] using hhi
          simpa [answerPrefix] using
            (by omega : pos < answerPrefix)
      exact
        component.lcaCloseCosted_exact_of_decoded_right_fringe_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
          (by
            exact
              bpPrefixRangeWitness_eq_of_leftmost_min_excess
                hrightAnswer
                (by simpa [rightBlock] using hrightBound)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo hhi
                  exact hmin hinside.1 hinside.2)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo (by omega)
                  exact hleftmost hinside.1 hhi))
          (by
            have hleftCount :
                0 <
                  blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose := by
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := leftClose)
                  hblockSize
              omega
            exact
              bpPrefixRangeMinExcess_gt_of_all_prefix_gt
                hleftCount
                (by simpa [leftBlock] using hleftBound)
                (by
                  intro pos hlo hhi
                  exact hleftmost hlo (hleftBefore hlo hhi)))
          (by
            intro middle hmiddle
            by_cases hgap :
                blockOfClose blockSize leftClose + 1 <
                  blockOfClose blockSize rightClose
            · simp [hgap] at hmiddle
              subst middle
              have hcount :
                  0 <
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1 := by
                omega
              exact
                bpRangeMinExcess_gt_of_all_prefix_gt
                  (shape := shape) (blockSize := blockSize)
                  (startBlock :=
                    blockOfClose blockSize leftClose + 1)
                  (blockCount :=
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1)
                  (lower := bpExcessAt shape (answerClose + 1))
                  hcount
                  (by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    simpa [hend] using hmiddleBound hgap)
                  (by
                    intro pos hlo hhi
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    have hbefore :=
                      hmiddleBefore (pos := pos) hgap hlo
                        (by simpa [hend] using hhi)
                    exact hleftmost hbefore.1 hbefore.2)
            · simp [hgap] at hmiddle)
    · have hmiddleGap :
          blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose := by
        by_cases heq : rightBlock = leftBlock + 1
        · have hlimitEq :
              leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) =
                blockStartOf blockSize rightBlock + 1 := by
            simpa [leftBlock, rightBlock, heq] using hleftLimitEq
          have hlimitLe :
              blockStartOf blockSize rightBlock + 1 <= answerPrefix := by
            simpa [hlimitEq] using (Nat.le_of_not_gt hanswerLeft)
          exact False.elim (hanswerRight hlimitLe)
        · have hcross' : leftBlock < rightBlock := by
            simpa [leftBlock, rightBlock] using hcross
          have hgap' : leftBlock + 1 < rightBlock := by
            omega
          simpa [leftBlock, rightBlock] using hgap'
      have hrangeEndEq :
          blockOfClose blockSize leftClose + 1 +
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1) =
            blockOfClose blockSize rightClose := by
        omega
      let answerBlock := blockOfClose blockSize answerClose
      have hanswerBlockMem :
          blockOfClose blockSize leftClose + 1 <= answerBlock /\
            answerBlock <
              blockOfClose blockSize leftClose + 1 +
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1) := by
        have hnotLeftLe :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix :=
          Nat.le_of_not_gt hanswerLeft
        have hanswerBeforeRight :
            answerPrefix < blockStartOf blockSize rightBlock + 1 :=
          Nat.lt_of_not_ge hanswerRight
        have hanswerCloseGeNext :
            blockStartOf blockSize (leftBlock + 1) <= answerClose := by
          have hlimit :
              blockStartOf blockSize (leftBlock + 1) + 1 <=
                answerPrefix := by
            simpa [leftBlock, hleftLimitEq] using hnotLeftLe
          omega
        have hanswerCloseLtRight :
            answerClose < blockStartOf blockSize rightBlock := by
          omega
        constructor
        · have hanswerBlockGeLeftNext : leftBlock + 1 <= answerBlock := by
            by_cases hge : leftBlock + 1 <= answerBlock
            · exact hge
            · have hltBlock : answerBlock < leftBlock + 1 :=
                Nat.lt_of_not_ge hge
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := answerClose)
                  hblockSize
              have hend' :
                  answerClose <
                    blockStartOf blockSize answerBlock + blockSize := by
                simpa [answerBlock] using hend
              have hsucc :
                  blockStartOf blockSize answerBlock + blockSize =
                    blockStartOf blockSize (answerBlock + 1) :=
                blockStartOf_succ blockSize answerBlock
              have hmono :
                  blockStartOf blockSize (answerBlock + 1) <=
                    blockStartOf blockSize (leftBlock + 1) :=
                blockStartOf_mono (blockSize := blockSize) (by omega)
              have hnext :
                  answerClose < blockStartOf blockSize (leftBlock + 1) := by
                omega
              omega
          simpa [answerBlock, leftBlock] using hanswerBlockGeLeftNext
        · have hanswerBlockLtRight : answerBlock < rightBlock := by
            by_cases hlt : answerBlock < rightBlock
            · exact hlt
            · have hge : rightBlock <= answerBlock := Nat.le_of_not_gt hlt
              have hstartAns :=
                blockStartOf_blockOfClose_le
                  (blockSize := blockSize) (close := answerClose)
              have hstartAns' :
                  blockStartOf blockSize answerBlock <= answerClose := by
                simpa [answerBlock] using hstartAns
              have hmono :
                  blockStartOf blockSize rightBlock <=
                    blockStartOf blockSize answerBlock :=
                blockStartOf_mono (blockSize := blockSize) hge
              omega
          simpa [answerBlock, rightBlock, hrangeEndEq] using
            hanswerBlockLtRight
      have hanswerBlockLtRight : answerBlock < rightBlock := by
        have h := hanswerBlockMem.2
        simpa [answerBlock, rightBlock, hrangeEndEq] using h
      have hanswerBlockTarget :
          bpBlockArgMinPrefixPos shape blockSize answerBlock =
            answerPrefix := by
        have hlocalMem :
            blockStartOf blockSize answerBlock <= answerPrefix /\
              answerPrefix <
                blockStartOf blockSize answerBlock + (blockSize + 1) := by
          have hstart :=
            blockStartOf_blockOfClose_le
              (blockSize := blockSize) (close := answerClose)
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := answerClose)
              hblockSize
          constructor
          · simpa [answerBlock, answerPrefix] using
              (by omega : blockStartOf blockSize
                  (blockOfClose blockSize answerClose) <=
                answerClose + 1)
          · simpa [answerBlock, answerPrefix] using
              (by omega : answerClose + 1 <
                blockStartOf blockSize
                    (blockOfClose blockSize answerClose) +
                  (blockSize + 1))
        have hlocalBound :
            blockStartOf blockSize answerBlock + (blockSize + 1) <=
              shape.bpCode.length + 1 := by
          have hmono :
              blockStartOf blockSize (answerBlock + 1) <=
                blockStartOf blockSize rightBlock :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          have hsucc :
              blockStartOf blockSize answerBlock + blockSize =
                blockStartOf blockSize (answerBlock + 1) :=
            blockStartOf_succ blockSize answerBlock
          omega
        exact
          bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
            hlocalMem hlocalBound
            (by
              intro pos hlo hhi
              have hinside :
                  leftClose + 1 <= pos /\ pos < rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize answerBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize answerBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        have h := hanswerBlockMem.1
                        simpa [answerBlock, leftBlock] using h)
                  omega
                have hupper :
                    pos < blockStartOf blockSize rightBlock + 1 := by
                  have hanswerBlockLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  have hmono :
                      blockStartOf blockSize (answerBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize answerBlock + blockSize =
                        blockStartOf blockSize (answerBlock + 1) :=
                    blockStartOf_succ blockSize answerBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hlo
                · have hrightStartLe' :
                    blockStartOf blockSize rightBlock <= rightClose :=
                    hrightStartLe
                  omega
              exact hmin hinside.1 hinside.2)
            (by
              intro pos hlo hhi
              have hstartLower :
                  leftClose + 1 <= blockStartOf blockSize answerBlock := by
                have hleftLeBlock :
                    blockStartOf blockSize (leftBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize)
                    (by
                      have h := hanswerBlockMem.1
                      simpa [answerBlock, leftBlock] using h)
                omega
              exact hleftmost (Nat.le_trans hstartLower hlo) hhi)
      have hmiddlePair :
          (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
            bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) =
            (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
        exact
          bpRangeWitness_eq_of_leftmost_block_candidate
            hanswerBlockMem
            hanswerBlockTarget
            (by
              intro candidateBlock hcLo hcHi
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hend :
                      blockOfClose blockSize leftClose + 1 +
                          (blockOfClose blockSize rightClose -
                            blockOfClose blockSize leftClose - 1) =
                        blockOfClose blockSize rightClose := by
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hinside :
                  leftClose + 1 <=
                      bpBlockArgMinPrefixPos shape blockSize candidateBlock /\
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        simpa [leftBlock] using hcLo)
                  omega
                have hupper :
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      blockStartOf blockSize rightBlock + 1 := by
                  have hcandidateLtRight : candidateBlock < rightBlock := by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    omega
                  have hmono :
                      blockStartOf blockSize (candidateBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize candidateBlock + blockSize =
                        blockStartOf blockSize (candidateBlock + 1) :=
                    blockStartOf_succ blockSize candidateBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hcandMem.1
                · omega
              exact hmin hinside.1 hinside.2)
            (by
              intro candidateBlock hcLo hcLt
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hABLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hlower :
                  leftClose + 1 <=
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by simpa [leftBlock] using hcLo)
                  omega
                exact Nat.le_trans hstartLower hcandMem.1
              have hbefore :
                  bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                    answerPrefix := by
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                have hanswerLower :
                    blockStartOf blockSize answerBlock + 1 <= answerPrefix := by
                  have hstart :=
                    blockStartOf_blockOfClose_le
                      (blockSize := blockSize) (close := answerClose)
                  simpa [answerBlock, answerPrefix] using
                    (by omega : blockStartOf blockSize
                        (blockOfClose blockSize answerClose) + 1 <=
                      answerClose + 1)
                omega
              exact hleftmost hlower (by simpa [answerPrefix] using hbefore))
      have hleftGt :
          bpExcessAt shape (answerClose + 1) <
            bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) := by
        have hleftCount :
            0 <
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose := by
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := leftClose)
              hblockSize
          omega
        exact
          bpPrefixRangeMinExcess_gt_of_all_prefix_gt
            hleftCount
            (by simpa [leftBlock] using hleftBound)
            (by
              intro pos hlo hhi
              have hlimit :
                  leftClose + 1 +
                      (blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize - leftClose) <= answerPrefix :=
                Nat.le_of_not_gt hanswerLeft
              exact hleftmost hlo (by simpa [answerPrefix] using
                (by omega : pos < answerPrefix)))
      have hrightLe :
          bpExcessAt shape (answerClose + 1) <=
            bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        have hrightCount :
            0 <
              rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2 := by
          omega
        exact
          bpPrefixRangeMinExcess_ge_of_all_prefix_ge
            hrightCount
            (by simpa [rightBlock] using hrightBound)
            (by
              intro pos hlo hhi
              have hinside := hrightInside hlo hhi
              exact hmin hinside.1 hinside.2)
      exact
        component.lcaCloseCosted_exact_of_decoded_middle_candidate
          leftClose rightClose hblockSize hleftBlock hrightBlock
          hmiddleGap hmiddlePair hleftGt hrightLe

theorem lcaCloseCosted_exact_of_query_cross_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem lcaCloseCosted_exact_of_spanning_root_cross_block
    {leftShape rightShape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    {start len leftClose rightClose answerClose : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro
        (Cartesian.CartesianShape.node leftShape rightShape)
        blockSize blockCount fieldWidth
        leftOverhead interiorOverhead rightOverhead)
    (hlen : 0 < len)
    (hbound :
      start + len <=
        (Cartesian.CartesianShape.node leftShape rightShape).size)
    (hrootLo : start <= leftShape.size)
    (hrootHi : leftShape.size < start + len)
    (hleft :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          start = some leftClose)
    (hright :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (start + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder?
          (Cartesian.CartesianShape.node leftShape rightShape)
          (scanWindow
            (Cartesian.CartesianShape.node
              leftShape rightShape).representative start len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_spanning_root
      (leftShape := leftShape) (rightShape := rightShape)
      (start := start) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hrootLo hrootHi hleft hright hanswer
  exact
    component.lcaCloseCosted_exact_of_query_semantics_cross_block
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock hcross
      hsemantic.1 hsemantic.2

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  have hleft := component.leftFringe.read_words_length_le_machine hmachine
  have hmid := component.interior.read_words_length_le_machine hmachine
  have hright := component.rightFringe.read_words_length_le_machine hmachine
  exact ⟨hleft.1, hleft.2, hmid.1, hmid.2, hright.1, hright.2⟩

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  constructor
  · exact component.payload_length
  intro leftClose rightClose
  exact ⟨component.lcaCloseCosted_cost_le_six leftClose rightClose,
    component.lcaCloseCosted_erase leftClose rightClose⟩

theorem profile_cross_block_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (component :
      PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
        fieldWidth leftOverhead interiorOverhead rightOverhead) :
    component.payload.length =
        leftOverhead + interiorOverhead + rightOverhead /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  constructor
  · exact component.payload_length
  constructor
  · intro leftClose rightClose
    exact component.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hleftBlock hrightBlock hcross
  exact
    component.lcaCloseCosted_exact_of_query_cross_block
      hlen hbound hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross

end PayloadLiveBPEndpointFringeRangeMacro

theorem bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hanswerLeft :
      leftClose + 1 <= answerClose + 1 /\
        answerClose + 1 <
          leftClose + 1 +
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    (hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose) <=
        shape.bpCode.length + 1)
    (hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2)
    (hrightBound :
      blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) <=
        shape.bpCode.length + 1)
    (hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1)
    (hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hleftPair :
      (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
        bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
    exact
      bpPrefixRangeWitness_eq_of_leftmost_min_excess
        hanswerLeft hleftBound
        (by
          intro pos hlo hhi
          exact hmin hlo (hleftInside hlo hhi))
        (by
          intro pos hlo hhi
          exact hleftmost hlo hhi)
  have hrightCount :
      0 <
        rightClose -
            blockStartOf blockSize
              (blockOfClose blockSize rightClose) +
          2 := by
    omega
  have hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2) := by
    exact
      bpPrefixRangeMinExcess_ge_of_all_prefix_ge
        hrightCount hrightBound
        (by
          intro pos hlo hhi
          have hinside := hrightInside hlo hhi
          exact hmin hinside.1 hinside.2)
  have hmiddleLe :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) <= middle.1 := by
    intro middle hmiddle
    by_cases hblocks :
        blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose
    · simp [hblocks] at hmiddle
      subst middle
      have hcount :
          0 <
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1 := by
        omega
      exact
        bpRangeMinExcess_ge_of_all_prefix_ge
          (shape := shape) (blockSize := blockSize)
          (startBlock := blockOfClose blockSize leftClose + 1)
          (blockCount :=
            blockOfClose blockSize rightClose -
              blockOfClose blockSize leftClose - 1)
          (lower := bpExcessAt shape (answerClose + 1))
          hcount
          (by
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            simpa [hend] using hmiddleBound hblocks)
          (by
            intro pos hlo hhi
            have hend :
                blockOfClose blockSize leftClose + 1 +
                    (blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1) =
                  blockOfClose blockSize rightClose := by
              omega
            have hinside :=
              hmiddleInside (pos := pos) hblocks hlo
                (by simpa [hend] using hhi)
            exact hmin hinside.1 hinside.2)
    · simp [hblocks] at hmiddle
  simpa [hleftPair] using
    bpCandidateMerge3?_eq_some_left_of_fst_le
      (left := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      (by
        intro middle hmiddle
        exact hmiddleLe middle hmiddle)
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hrightPair :
      (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2),
        bpPrefixRangeArgMinPrefixPos shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hleftGt :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hmiddleGt :
      forall middle,
        (if blockOfClose blockSize leftClose + 1 <
              blockOfClose blockSize rightClose then
            some
              (bpRangeMinExcess shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1),
                bpRangeArgMinPrefixPos shape blockSize
                  (blockOfClose blockSize leftClose + 1)
                  (blockOfClose blockSize rightClose -
                    blockOfClose blockSize leftClose - 1))
          else
            none) = some middle ->
          bpExcessAt shape (answerClose + 1) < middle.1) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hrightPair] using
    bpCandidateMerge3?_eq_some_right_of_fst_lt_left_middle
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (right := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (middle? :=
        if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
      hleftGt
      (by
        intro middle hmiddle
        exact hmiddleGt middle hmiddle)

theorem bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
    {shape : Cartesian.CartesianShape}
    {blockSize answerClose : Nat}
    (leftClose rightClose : Nat)
    (hblocks :
      blockOfClose blockSize leftClose + 1 <
        blockOfClose blockSize rightClose)
    (hmiddlePair :
      (bpRangeMinExcess shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1),
        bpRangeArgMinPrefixPos shape blockSize
          (blockOfClose blockSize leftClose + 1)
          (blockOfClose blockSize rightClose -
            blockOfClose blockSize leftClose - 1)) =
        (bpExcessAt shape (answerClose + 1), answerClose + 1))
    (hmiddleLeft :
      bpExcessAt shape (answerClose + 1) <
        bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose))
    (hrightLe :
      bpExcessAt shape (answerClose + 1) <=
        bpPrefixRangeMinExcess shape
          (blockStartOf blockSize
            (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize
                (blockOfClose blockSize rightClose) +
            2)) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  simpa [hblocks, hmiddlePair] using
    bpCandidateMerge3?_eq_some_middle_of_fst_lt_left_le_right
      (left :=
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose)))
      (middle := (bpExcessAt shape (answerClose + 1), answerClose + 1))
      (right? :=
        some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2)))
      hmiddleLeft
      (by
        intro right hright
        cases hright
        exact hrightLe)

theorem bpRelativeRmmCandidateMerge_exact_of_query_semantics
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (_hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (_hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  let leftBlock := blockOfClose blockSize leftClose
  let rightBlock := blockOfClose blockSize rightClose
  let answerPrefix := answerClose + 1
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hanswerCloseBound := bpCloseOfInorder?_bounds shape hanswer
  have hrightStartLe :
      blockStartOf blockSize rightBlock <= rightClose := by
    simpa [rightBlock] using
      (blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose))
  have hleftNextStart :
      leftClose < blockStartOf blockSize (leftBlock + 1) := by
    have hend :=
      close_lt_blockStartOf_blockOfClose_add
        (blockSize := blockSize) (close := leftClose) hblockSize
    simpa [leftBlock, blockStartOf_succ] using hend
  have hleftLimitEq :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) =
        blockStartOf blockSize (leftBlock + 1) + 1 := by
    have hstart :
        blockStartOf blockSize leftBlock <= leftClose := by
      simpa [leftBlock] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := leftClose))
    have hsucc :
        blockStartOf blockSize leftBlock + blockSize =
          blockStartOf blockSize (leftBlock + 1) :=
      blockStartOf_succ blockSize leftBlock
    omega
  have hrightLimitEq :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) =
        rightClose + 2 := by
    omega
  have hleftToRightStart :
      blockStartOf blockSize (leftBlock + 1) <=
        blockStartOf blockSize rightBlock := by
    exact blockStartOf_mono (blockSize := blockSize) (by
      simpa [leftBlock, rightBlock] using hcross)
  have hleftBound :
      leftClose + 1 +
          (blockStartOf blockSize leftBlock + blockSize - leftClose) <=
        shape.bpCode.length + 1 := by
    rw [hleftLimitEq]
    omega
  have hrightBound :
      blockStartOf blockSize rightBlock +
          (rightClose - blockStartOf blockSize rightBlock + 2) <=
        shape.bpCode.length + 1 := by
    rw [hrightLimitEq]
    omega
  have hmiddleBound :
      blockOfClose blockSize leftClose + 1 <
          blockOfClose blockSize rightClose ->
        blockStartOf blockSize (blockOfClose blockSize rightClose) + 1 <=
          shape.bpCode.length + 1 := by
    intro _hgap
    have hstart :
        blockStartOf blockSize
            (blockOfClose blockSize rightClose) <= rightClose :=
      blockStartOf_blockOfClose_le
        (blockSize := blockSize) (close := rightClose)
    omega
  have hleftInside :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos <
            leftClose + 1 +
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) ->
            pos < rightClose + 2 := by
    intro pos _hlo hhi
    have hhi' :
        pos < blockStartOf blockSize (leftBlock + 1) + 1 := by
      simpa [leftBlock, hleftLimitEq] using hhi
    have hleRight :
        blockStartOf blockSize (leftBlock + 1) + 1 <= rightClose + 1 := by
      omega
    omega
  have hrightInside :
      forall {pos : Nat},
        blockStartOf blockSize (blockOfClose blockSize rightClose) <= pos ->
          pos <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) ->
            leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize rightClose) := by
      have hlt := hleftNextStart
      have hmono :
          blockStartOf blockSize (leftBlock + 1) <=
            blockStartOf blockSize rightBlock :=
        hleftToRightStart
      simpa [rightBlock] using (by omega : leftClose + 1 <=
        blockStartOf blockSize rightBlock)
    constructor
    · exact Nat.le_trans hleftLe hlo
    · simpa [rightBlock, hrightLimitEq] using hhi
  have hmiddleInside :
      forall {pos : Nat},
        blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose ->
          blockStartOf blockSize
              (blockOfClose blockSize leftClose + 1) <= pos ->
            pos <
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
                1 ->
              leftClose + 1 <= pos /\ pos < rightClose + 2 := by
    intro pos _hgap hlo hhi
    have hleftLe :
        leftClose + 1 <=
          blockStartOf blockSize (blockOfClose blockSize leftClose + 1) := by
      simpa [leftBlock] using (by omega :
        leftClose + 1 <= blockStartOf blockSize (leftBlock + 1))
    constructor
    · exact Nat.le_trans hleftLe hlo
    · have hrightLeClose :
          blockStartOf blockSize
              (blockOfClose blockSize rightClose) <= rightClose :=
        blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose)
      omega
  have hanswerMem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hanswerUpper : answerPrefix < rightClose + 2 := by
    simpa [answerPrefix] using (by omega :
      answerClose + 1 < rightClose + 2)
  by_cases hanswerLeft :
      answerPrefix <
        leftClose + 1 +
          (blockStartOf blockSize
              (blockOfClose blockSize leftClose) +
            blockSize - leftClose)
  · exact
      bpRelativeRmmCandidateMerge_exact_of_left_fringe_leftmost
        leftClose rightClose
        (by
          constructor
          · simpa [answerPrefix] using hanswerMem.1
          · exact hanswerLeft)
        (by simpa [leftBlock] using hleftBound)
        hleftInside
        (by simpa [rightBlock] using hrightBound)
        hrightInside
        hmiddleBound
        hmiddleInside
        hmin hleftmost
  · by_cases hanswerRight :
        blockStartOf blockSize rightBlock + 1 <= answerPrefix
    · have hrightAnswer :
        blockStartOf blockSize (blockOfClose blockSize rightClose) <=
            answerClose + 1 /\
          answerClose + 1 <
            blockStartOf blockSize (blockOfClose blockSize rightClose) +
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        constructor
        · simpa [rightBlock, answerPrefix] using
            (Nat.le_trans (Nat.le_of_lt (by omega :
              blockStartOf blockSize rightBlock <
                blockStartOf blockSize rightBlock + 1)) hanswerRight)
        · simpa [rightBlock, hrightLimitEq, answerPrefix] using hanswerUpper
      have hleftBefore :
          forall {pos : Nat},
            leftClose + 1 <= pos ->
              pos <
                leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) ->
                pos < answerClose + 1 := by
        intro pos _hlo hhi
        have hlimit :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix := by
          omega
        simpa [answerPrefix] using (by omega : pos < answerPrefix)
      have hmiddleBefore :
          forall {pos : Nat},
            blockOfClose blockSize leftClose + 1 <
                blockOfClose blockSize rightClose ->
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose + 1) <= pos ->
                pos <
                  blockStartOf blockSize
                      (blockOfClose blockSize rightClose) +
                    1 ->
                  leftClose + 1 <= pos /\ pos < answerClose + 1 := by
        intro pos hgap hlo hhi
        have hinside := hmiddleInside (pos := pos) hgap hlo hhi
        constructor
        · exact hinside.1
        · have hhi' : pos < blockStartOf blockSize rightBlock + 1 := by
            simpa [rightBlock] using hhi
          simpa [answerPrefix] using
            (by omega : pos < answerPrefix)
      exact
        bpRelativeRmmCandidateMerge_exact_of_right_fringe_leftmost
          leftClose rightClose
          (by
            exact
              bpPrefixRangeWitness_eq_of_leftmost_min_excess
                hrightAnswer
                (by simpa [rightBlock] using hrightBound)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo hhi
                  exact hmin hinside.1 hinside.2)
                (by
                  intro pos hlo hhi
                  have hinside := hrightInside hlo (by omega)
                  exact hleftmost hinside.1 hhi))
          (by
            have hleftCount :
                0 <
                  blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose := by
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := leftClose)
                  hblockSize
              omega
            exact
              bpPrefixRangeMinExcess_gt_of_all_prefix_gt
                hleftCount
                (by simpa [leftBlock] using hleftBound)
                (by
                  intro pos hlo hhi
                  exact hleftmost hlo (hleftBefore hlo hhi)))
          (by
            intro middle hmiddle
            by_cases hgap :
                blockOfClose blockSize leftClose + 1 <
                  blockOfClose blockSize rightClose
            · simp [hgap] at hmiddle
              subst middle
              have hcount :
                  0 <
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1 := by
                omega
              exact
                bpRangeMinExcess_gt_of_all_prefix_gt
                  (shape := shape) (blockSize := blockSize)
                  (startBlock :=
                    blockOfClose blockSize leftClose + 1)
                  (blockCount :=
                    blockOfClose blockSize rightClose -
                      blockOfClose blockSize leftClose - 1)
                  (lower := bpExcessAt shape (answerClose + 1))
                  hcount
                  (by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    simpa [hend] using hmiddleBound hgap)
                  (by
                    intro pos hlo hhi
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    have hbefore :=
                      hmiddleBefore (pos := pos) hgap hlo
                        (by simpa [hend] using hhi)
                    exact hleftmost hbefore.1 hbefore.2)
            · simp [hgap] at hmiddle)
    · have hmiddleGap :
          blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose := by
        by_cases heq : rightBlock = leftBlock + 1
        · have hlimitEq :
              leftClose + 1 +
                  (blockStartOf blockSize
                      (blockOfClose blockSize leftClose) +
                    blockSize - leftClose) =
                blockStartOf blockSize rightBlock + 1 := by
            simpa [leftBlock, rightBlock, heq] using hleftLimitEq
          have hlimitLe :
              blockStartOf blockSize rightBlock + 1 <= answerPrefix := by
            simpa [hlimitEq] using (Nat.le_of_not_gt hanswerLeft)
          exact False.elim (hanswerRight hlimitLe)
        · have hcross' : leftBlock < rightBlock := by
            simpa [leftBlock, rightBlock] using hcross
          have hgap' : leftBlock + 1 < rightBlock := by
            omega
          simpa [leftBlock, rightBlock] using hgap'
      have hrangeEndEq :
          blockOfClose blockSize leftClose + 1 +
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1) =
            blockOfClose blockSize rightClose := by
        omega
      let answerBlock := blockOfClose blockSize answerClose
      have hanswerBlockMem :
          blockOfClose blockSize leftClose + 1 <= answerBlock /\
            answerBlock <
              blockOfClose blockSize leftClose + 1 +
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1) := by
        have hnotLeftLe :
            leftClose + 1 +
                (blockStartOf blockSize
                    (blockOfClose blockSize leftClose) +
                  blockSize - leftClose) <= answerPrefix :=
          Nat.le_of_not_gt hanswerLeft
        have hanswerBeforeRight :
            answerPrefix < blockStartOf blockSize rightBlock + 1 :=
          Nat.lt_of_not_ge hanswerRight
        have hanswerCloseGeNext :
            blockStartOf blockSize (leftBlock + 1) <= answerClose := by
          have hlimit :
              blockStartOf blockSize (leftBlock + 1) + 1 <=
                answerPrefix := by
            simpa [leftBlock, hleftLimitEq] using hnotLeftLe
          omega
        have hanswerCloseLtRight :
            answerClose < blockStartOf blockSize rightBlock := by
          omega
        constructor
        · have hanswerBlockGeLeftNext : leftBlock + 1 <= answerBlock := by
            by_cases hge : leftBlock + 1 <= answerBlock
            · exact hge
            · have hltBlock : answerBlock < leftBlock + 1 :=
                Nat.lt_of_not_ge hge
              have hend :=
                close_lt_blockStartOf_blockOfClose_add
                  (blockSize := blockSize) (close := answerClose)
                  hblockSize
              have hend' :
                  answerClose <
                    blockStartOf blockSize answerBlock + blockSize := by
                simpa [answerBlock] using hend
              have hsucc :
                  blockStartOf blockSize answerBlock + blockSize =
                    blockStartOf blockSize (answerBlock + 1) :=
                blockStartOf_succ blockSize answerBlock
              have hmono :
                  blockStartOf blockSize (answerBlock + 1) <=
                    blockStartOf blockSize (leftBlock + 1) :=
                blockStartOf_mono (blockSize := blockSize) (by omega)
              have hnext :
                  answerClose < blockStartOf blockSize (leftBlock + 1) := by
                omega
              omega
          simpa [answerBlock, leftBlock] using hanswerBlockGeLeftNext
        · have hanswerBlockLtRight : answerBlock < rightBlock := by
            by_cases hlt : answerBlock < rightBlock
            · exact hlt
            · have hge : rightBlock <= answerBlock := Nat.le_of_not_gt hlt
              have hstartAns :=
                blockStartOf_blockOfClose_le
                  (blockSize := blockSize) (close := answerClose)
              have hstartAns' :
                  blockStartOf blockSize answerBlock <= answerClose := by
                simpa [answerBlock] using hstartAns
              have hmono :
                  blockStartOf blockSize rightBlock <=
                    blockStartOf blockSize answerBlock :=
                blockStartOf_mono (blockSize := blockSize) hge
              omega
          simpa [answerBlock, rightBlock, hrangeEndEq] using
            hanswerBlockLtRight
      have hanswerBlockLtRight : answerBlock < rightBlock := by
        have h := hanswerBlockMem.2
        simpa [answerBlock, rightBlock, hrangeEndEq] using h
      have hanswerBlockTarget :
          bpBlockArgMinPrefixPos shape blockSize answerBlock =
            answerPrefix := by
        have hlocalMem :
            blockStartOf blockSize answerBlock <= answerPrefix /\
              answerPrefix <
                blockStartOf blockSize answerBlock + (blockSize + 1) := by
          have hstart :=
            blockStartOf_blockOfClose_le
              (blockSize := blockSize) (close := answerClose)
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := answerClose)
              hblockSize
          constructor
          · simpa [answerBlock, answerPrefix] using
              (by omega : blockStartOf blockSize
                  (blockOfClose blockSize answerClose) <=
                answerClose + 1)
          · simpa [answerBlock, answerPrefix] using
              (by omega : answerClose + 1 <
                blockStartOf blockSize
                    (blockOfClose blockSize answerClose) +
                  (blockSize + 1))
        have hlocalBound :
            blockStartOf blockSize answerBlock + (blockSize + 1) <=
              shape.bpCode.length + 1 := by
          have hmono :
              blockStartOf blockSize (answerBlock + 1) <=
                blockStartOf blockSize rightBlock :=
            blockStartOf_mono (blockSize := blockSize) (by omega)
          have hsucc :
              blockStartOf blockSize answerBlock + blockSize =
                blockStartOf blockSize (answerBlock + 1) :=
            blockStartOf_succ blockSize answerBlock
          omega
        exact
          bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess
            hlocalMem hlocalBound
            (by
              intro pos hlo hhi
              have hinside :
                  leftClose + 1 <= pos /\ pos < rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize answerBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize answerBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        have h := hanswerBlockMem.1
                        simpa [answerBlock, leftBlock] using h)
                  omega
                have hupper :
                    pos < blockStartOf blockSize rightBlock + 1 := by
                  have hanswerBlockLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  have hmono :
                      blockStartOf blockSize (answerBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize answerBlock + blockSize =
                        blockStartOf blockSize (answerBlock + 1) :=
                    blockStartOf_succ blockSize answerBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hlo
                · have hrightStartLe' :
                    blockStartOf blockSize rightBlock <= rightClose :=
                    hrightStartLe
                  omega
              exact hmin hinside.1 hinside.2)
            (by
              intro pos hlo hhi
              have hstartLower :
                  leftClose + 1 <= blockStartOf blockSize answerBlock := by
                have hleftLeBlock :
                    blockStartOf blockSize (leftBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize)
                    (by
                      have h := hanswerBlockMem.1
                      simpa [answerBlock, leftBlock] using h)
                omega
              exact hleftmost (Nat.le_trans hstartLower hlo) hhi)
      have hmiddlePair :
          (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
            bpRangeArgMinPrefixPos shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1)) =
            (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
        exact
          bpRangeWitness_eq_of_leftmost_block_candidate
            hanswerBlockMem
            hanswerBlockTarget
            (by
              intro candidateBlock hcLo hcHi
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hend :
                      blockOfClose blockSize leftClose + 1 +
                          (blockOfClose blockSize rightClose -
                            blockOfClose blockSize leftClose - 1) =
                        blockOfClose blockSize rightClose := by
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hinside :
                  leftClose + 1 <=
                      bpBlockArgMinPrefixPos shape blockSize candidateBlock /\
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      rightClose + 2 := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by
                        simpa [leftBlock] using hcLo)
                  omega
                have hupper :
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                      blockStartOf blockSize rightBlock + 1 := by
                  have hcandidateLtRight : candidateBlock < rightBlock := by
                    have hend :
                        blockOfClose blockSize leftClose + 1 +
                            (blockOfClose blockSize rightClose -
                              blockOfClose blockSize leftClose - 1) =
                          blockOfClose blockSize rightClose := by
                      omega
                    omega
                  have hmono :
                      blockStartOf blockSize (candidateBlock + 1) <=
                        blockStartOf blockSize rightBlock :=
                    blockStartOf_mono (blockSize := blockSize) (by omega)
                  have hsucc :
                      blockStartOf blockSize candidateBlock + blockSize =
                        blockStartOf blockSize (candidateBlock + 1) :=
                    blockStartOf_succ blockSize candidateBlock
                  omega
                constructor
                · exact Nat.le_trans hstartLower hcandMem.1
                · omega
              exact hmin hinside.1 hinside.2)
            (by
              intro candidateBlock hcLo hcLt
              have hcountBound :
                  blockStartOf blockSize candidateBlock + (blockSize + 1) <=
                    shape.bpCode.length + 1 := by
                have hcandidateLtRight : candidateBlock < rightBlock := by
                  have hABLtRight : answerBlock < rightBlock := by
                    have h := hanswerBlockMem.2
                    omega
                  omega
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize rightBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                omega
              have hcandMem :=
                bpBlockArgMinPrefixPos_mem_range
                  (shape := shape) (blockSize := blockSize)
                  (block := candidateBlock) hcountBound
              have hlower :
                  leftClose + 1 <=
                    bpBlockArgMinPrefixPos shape blockSize candidateBlock := by
                have hstartLower :
                    leftClose + 1 <= blockStartOf blockSize candidateBlock := by
                  have hleftLeBlock :
                      blockStartOf blockSize (leftBlock + 1) <=
                        blockStartOf blockSize candidateBlock :=
                    blockStartOf_mono (blockSize := blockSize)
                      (by simpa [leftBlock] using hcLo)
                  omega
                exact Nat.le_trans hstartLower hcandMem.1
              have hbefore :
                  bpBlockArgMinPrefixPos shape blockSize candidateBlock <
                    answerPrefix := by
                have hmono :
                    blockStartOf blockSize (candidateBlock + 1) <=
                      blockStartOf blockSize answerBlock :=
                  blockStartOf_mono (blockSize := blockSize) (by omega)
                have hsucc :
                    blockStartOf blockSize candidateBlock + blockSize =
                      blockStartOf blockSize (candidateBlock + 1) :=
                  blockStartOf_succ blockSize candidateBlock
                have hanswerLower :
                    blockStartOf blockSize answerBlock + 1 <= answerPrefix := by
                  have hstart :=
                    blockStartOf_blockOfClose_le
                      (blockSize := blockSize) (close := answerClose)
                  simpa [answerBlock, answerPrefix] using
                    (by omega : blockStartOf blockSize
                        (blockOfClose blockSize answerClose) + 1 <=
                      answerClose + 1)
                omega
              exact hleftmost hlower (by simpa [answerPrefix] using hbefore))
      have hleftGt :
          bpExcessAt shape (answerClose + 1) <
            bpPrefixRangeMinExcess shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose) := by
        have hleftCount :
            0 <
              blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose := by
          have hend :=
            close_lt_blockStartOf_blockOfClose_add
              (blockSize := blockSize) (close := leftClose)
              hblockSize
          omega
        exact
          bpPrefixRangeMinExcess_gt_of_all_prefix_gt
            hleftCount
            (by simpa [leftBlock] using hleftBound)
            (by
              intro pos hlo hhi
              have hlimit :
                  leftClose + 1 +
                      (blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize - leftClose) <= answerPrefix :=
                Nat.le_of_not_gt hanswerLeft
              exact hleftmost hlo (by simpa [answerPrefix] using
                (by omega : pos < answerPrefix)))
      have hrightLe :
          bpExcessAt shape (answerClose + 1) <=
            bpPrefixRangeMinExcess shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2) := by
        have hrightCount :
            0 <
              rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2 := by
          omega
        exact
          bpPrefixRangeMinExcess_ge_of_all_prefix_ge
            hrightCount
            (by simpa [rightBlock] using hrightBound)
            (by
              intro pos hlo hhi
              have hinside := hrightInside hlo hhi
              exact hmin hinside.1 hinside.2)
      exact
        bpRelativeRmmCandidateMerge_exact_of_middle_leftmost
          leftClose rightClose hmiddleGap hmiddlePair hleftGt hrightLe

theorem bpRelativeRmmCandidateMerge_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hleftBlock :
      blockOfClose blockSize leftClose < blockCount)
    (hrightBlock :
      blockOfClose blockSize rightClose < blockCount)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  exact
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (hlen := hlen) hleft hright hanswer hblockSize
      hleftBlock hrightBlock hcross hsemantic.1 hsemantic.2

def concreteBPEndpointFringeRangeMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  leftFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointLeftFringeRanges blockSize blockCount) hwidth
  interior :=
    concreteBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (interiorBlockPairRanges blockCount) hwidth
  rightFringe :=
    concreteBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (endpointRightFringeRanges blockSize blockCount) hwidth

theorem concreteBPEndpointFringeRangeMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile := component.profile
  constructor
  · simpa [component, concreteBPEndpointFringeRangeMacro,
      endpointLeftFringeRanges_length, endpointRightFringeRanges_length,
      interiorBlockPairRanges_length] using hprofile.1
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            bpCandidateClose?
              (bpCandidateMerge3?
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointLeftFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize leftClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)
                (if blockOfClose blockSize leftClose + 1 <
                    blockOfClose blockSize rightClose then
                  match
                    (bpRangeMinExcessEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]?,
                    (bpRangeArgMinPrefixPosEntries shape blockSize
                      (interiorBlockPairRanges blockCount))[
                        component.interiorIndex leftClose rightClose]? with
                  | some minExcess, some prefixPos =>
                      some (minExcess, prefixPos)
                  | _, _ => none
                else
                  none)
                (match
                  (bpPrefixRangeMinExcessEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]?,
                  (bpPrefixRangeArgMinPrefixPosEntries shape
                    (endpointRightFringeRanges blockSize blockCount))[
                      endpointFringeSlot blockSize rightClose]? with
                | some minExcess, some prefixPos =>
                    some (minExcess, prefixPos)
                | _, _ => none)) := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hprofile.1]
    exact hbudget
  · exact hprofile.2

theorem concreteBPEndpointFringeRangeMacro_sampled_query_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      2 * ((blockCount * blockSize) * fieldWidth) +
          2 * ((blockCount * blockCount) * fieldWidth) +
          2 * ((blockCount * blockSize) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockOfClose blockSize leftClose < blockCount ->
                      blockOfClose blockSize rightClose < blockCount ->
                        blockOfClose blockSize leftClose <
                            blockOfClose blockSize rightClose ->
                          (component.lcaCloseCosted
                            leftClose rightClose).erase =
                            some answerClose := by
  let component :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  have hprofile :=
    (component.profile_cross_block_exact)
  have hpayload :=
    (concreteBPEndpointFringeRangeMacro_profile
      shape blockSize blockCount fieldWidth hwidth).1
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [hpayload]
    exact hbudget
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2

theorem concreteBPEndpointFringeRangeMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRankProposal.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.leftFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.interior.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.rightFringe.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRankProposal.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPEndpointFringeRangeMacro.read_words_length_le_machine
      (concreteBPEndpointFringeRangeMacro
        shape blockSize blockCount fieldWidth hwidth) hmachine

/--
The right-spine shape of size four is the smallest useful witness that a macro
entry keyed only by the pair of endpoint close blocks cannot be exact.
-/
def blockPairMacroBlockerShape : Cartesian.CartesianShape :=
  Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
    (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
      (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
        (Cartesian.CartesianShape.node Cartesian.CartesianShape.empty
          Cartesian.CartesianShape.empty)))

/--
A concrete blocker for the tempting compact macro layout keyed only by
`(blockOfClose leftClose, blockOfClose rightClose)`.

For `blockSize = 3`, the two valid queries `[1, 4)` and `[2, 4)` in the
right-spine shape have endpoint closes in the same pair of close blocks, but
their BP-LCA close answers are different (`3` and `5`).  Therefore a macro
directory whose inter-block entry is only a function of the endpoint block pair
cannot satisfy the close-LCA exactness contract.
-/
theorem blockPairMacroDirectory_not_sufficient
    (blockAnswer : Nat -> Nat -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                blockAnswer (blockOfClose 3 leftClose)
                    (blockOfClose 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      blockAnswer (blockOfClose 3 3) (blockOfClose 3 7) = some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      blockAnswer (blockOfClose 3 5) (blockOfClose 3 7) = some 3 := by
    simpa [blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Endpoint summary key for the tempting "read the endpoint block summaries, then
answer by key" macro shortcut.

This records exactly the information returned by the existing min/max summary
layer for one endpoint block: the block id plus that block's sampled minimum
and maximum BP excess.
-/
def endpointSummaryBlockKey
    (shape : Cartesian.CartesianShape) (blockSize close : Nat) :
    Nat × (Nat × Nat) :=
  let block := blockOfClose blockSize close
  (block,
    (bpBlockMinExcess shape blockSize block,
      bpBlockMaxExcess shape blockSize block))

/--
Reading only the two endpoint block min/max summaries still cannot be a global
macro answer.

On the same four-node right spine as `blockPairMacroDirectory_not_sufficient`,
the queries `[1, 4)` and `[2, 4)` have the same endpoint summary keys at
`blockSize = 3`, because their endpoints fall in the same two BP blocks.  Their
correct close answers are nevertheless different.  A concrete macro therefore
needs position-bearing endpoint/fringe or range-min witnesses; the existing
summary values alone are not enough to determine the answer close.
-/
theorem endpointSummaryBlockMacroDirectory_not_sufficient
    (summaryAnswer :
      (Nat × (Nat × Nat)) -> (Nat × (Nat × Nat)) -> Option Nat) :
    ¬ (forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= blockPairMacroBlockerShape.size ->
          bpCloseOfInorder? blockPairMacroBlockerShape left = some leftClose ->
            bpCloseOfInorder? blockPairMacroBlockerShape
                (left + len - 1) =
              some rightClose ->
              bpCloseOfInorder? blockPairMacroBlockerShape
                  (scanWindow blockPairMacroBlockerShape.representative
                    left len) =
                some answerClose ->
                summaryAnswer
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 leftClose)
                    (endpointSummaryBlockKey
                      blockPairMacroBlockerShape 3 rightClose) =
                  some answerClose) := by
  intro hexact
  have hfirst :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 3)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    exact
      hexact (left := 1) (len := 3) (leftClose := 3)
        (rightClose := 7) (answerClose := 3)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hsecond :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 5 := by
    exact
      hexact (left := 2) (len := 2) (leftClose := 5)
        (rightClose := 7) (answerClose := 5)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
        (by decide)
  have hfirstKey :
      summaryAnswer
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 5)
          (endpointSummaryBlockKey blockPairMacroBlockerShape 3 7) =
        some 3 := by
    simpa [endpointSummaryBlockKey, blockOfClose] using hfirst
  rw [hsecond] at hfirstKey
  simp at hfirstKey

/--
Payload-live table of per-block close/LCA micro-codes.

The old `BlockMicroCodebook` stores only the finite codebook payload and takes
`codeOfBlock` as proof-side data.  This table is the missing charged classifier:
one fixed-width payload word per block is read to recover the code used for the
local close/LCA table.
-/
structure BlockCodeTable
    (blockCount codeCount codeWidth overhead : Nat) where
  codes : List Nat
  table : FixedWidthNatTable codes codeWidth
  codes_length_eq : codes.length = blockCount
  payload_length_eq : table.payload.length = overhead
  code_lt :
    forall {block code : Nat}, codes[block]? = some code -> code < codeCount

namespace BlockCodeTable

def payload
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) : List Bool :=
  classifier.table.payload

def codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Option Nat :=
  classifier.codes[block]?

def codeCosted
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  classifier.table.readCosted block

theorem payload_length
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead := by
  exact classifier.payload_length_eq

theorem codeCosted_cost
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost = 1 := by
  simp [codeCosted]

theorem codeCosted_cost_le_one
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).cost <= 1 := by
  simp [classifier.codeCosted_cost block]

theorem codeCosted_erase
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    (block : Nat) :
    (classifier.codeCosted block).erase = classifier.codeAt block := by
  simp [codeCosted, codeAt]

theorem codeCosted_exact_of_codeAt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    (classifier.codeCosted block).erase = some code := by
  simpa [hcode] using classifier.codeCosted_erase block

theorem codeAt_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block code : Nat}
    (hcode : classifier.codeAt block = some code) :
    code < codeCount := by
  exact classifier.code_lt (by simpa [codeAt] using hcode)

private theorem list_get?_exists_of_lt
    {α : Type} (xs : List α) {idx : Nat}
    (hidx : idx < xs.length) :
    exists value, xs[idx]? = some value := by
  induction xs generalizing idx with
  | nil =>
      simp at hidx
  | cons head tail ih =>
      cases idx with
      | zero =>
          exact ⟨head, by simp⟩
      | succ idx =>
          have htail : idx < tail.length := by
            simp at hidx
            exact hidx
          rcases ih htail with ⟨value, hvalue⟩
          exact ⟨value, by simpa using hvalue⟩

theorem codeAt_exists_of_lt
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead)
    {block : Nat}
    (hblock : block < blockCount) :
    exists code, classifier.codeAt block = some code := by
  have hidx : block < classifier.codes.length := by
    rw [classifier.codes_length_eq]
    exact hblock
  simpa [codeAt] using list_get?_exists_of_lt classifier.codes hidx

theorem profile
    {blockCount codeCount codeWidth overhead : Nat}
    (classifier :
      BlockCodeTable blockCount codeCount codeWidth overhead) :
    classifier.payload.length = overhead /\
      classifier.codes.length = blockCount /\
      forall block : Nat,
        (classifier.codeCosted block).cost <= 1 /\
          (classifier.codeCosted block).erase =
            classifier.codeAt block /\
          forall {code : Nat},
            classifier.codeAt block = some code -> code < codeCount := by
  constructor
  · exact classifier.payload_length
  constructor
  · exact classifier.codes_length_eq
  intro block
  constructor
  · exact classifier.codeCosted_cost_le_one block
  constructor
  · exact classifier.codeCosted_erase block
  intro code hcode
  exact classifier.codeAt_lt hcode

def ofEntries
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    BlockCodeTable blockCount codeCount codeWidth overhead where
  codes := codes
  table := FixedWidthNatTable.ofEntries codes codeWidth hwidth
  codes_length_eq := hlength
  payload_length_eq := by
    simpa [hoverhead] using
      (FixedWidthNatTable.ofEntries codes codeWidth hwidth).payload_length
  code_lt := hcode

theorem ofEntries_profile
    (blockCount codeCount codeWidth overhead : Nat)
    (codes : List Nat)
    (hwidth :
      forall {code : Nat}, List.Mem code codes -> code < 2 ^ codeWidth)
    (hlength : codes.length = blockCount)
    (hoverhead : codes.length * codeWidth = overhead)
    (hcode :
      forall {block code : Nat}, codes[block]? = some code ->
        code < codeCount) :
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).payload.length = overhead /\
      (ofEntries blockCount codeCount codeWidth overhead codes hwidth
        hlength hoverhead hcode).codes.length = blockCount /\
      forall block : Nat,
        ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
          hlength hoverhead hcode).codeCosted block).cost <= 1 /\
          ((ofEntries blockCount codeCount codeWidth overhead codes hwidth
            hlength hoverhead hcode).codeCosted block).erase =
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block /\
          forall {code : Nat},
            (ofEntries blockCount codeCount codeWidth overhead codes hwidth
              hlength hoverhead hcode).codeAt block = some code ->
              code < codeCount := by
  exact
    (ofEntries blockCount codeCount codeWidth overhead codes hwidth
      hlength hoverhead hcode).profile

end BlockCodeTable

/--
Reusable micro-codebook for block-local BP close/LCA tables.

The dense table from `BlockLocalBPCloseLCATable.concrete` is no longer charged
once per block here.  Each block carries a small code into a finite codebook,
and the counted micro payload is the concatenation of the table payloads for
those codes.  This is the micro half that a real macro/micro BP navigation
scheme can consume.

This compatibility skeleton still takes `codeOfBlock` as a supplied classifier.
`PayloadLiveBlockMicroCodebook` below is the counted successor that stores and
reads that classifier from payload bits.
-/
structure BlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount tableOverhead : Nat) where
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  codeOfBlock : Nat -> Nat
  codeOfBlock_lt : forall block, codeOfBlock block < codeCount
  payload : List Bool
  payload_eq_tables :
    payload =
      (List.range codeCount).flatMap fun code => (table code).payload
  payload_length_eq : payload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall block : Nat,
      BlockLocalBPCloseLCASpec shape
        (blockStartOf blockSize block) blockSize
        (entriesByCode (codeOfBlock block)) slotIndex

namespace BlockMicroCodebook

def tableForBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block : Nat) :
    FixedWidthOptionNatTable
      (micro.entriesByCode (micro.codeOfBlock block)) micro.fieldWidth :=
  micro.table (micro.codeOfBlock block)

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.map (fun entry? => entry?.join)
    ((micro.tableForBlock block).readCosted
      (micro.slotIndex
        (leftClose - blockStartOf blockSize block)
        (rightClose - blockStartOf blockSize block)))

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead := by
  exact micro.payload_length_eq

theorem lcaCloseCostedAtBlock_cost
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost = 1 := by
  simp [lcaCloseCostedAtBlock, Costed.map_cost]

theorem lcaCloseCostedAtBlock_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 1 := by
  simp [micro.lcaCloseCostedAtBlock_cost block leftClose rightClose]

theorem lcaCloseCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 1 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_one
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    {block left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  exact
    blockLocalBPCloseLCA_read_exact
      (micro.tableForBlock block) (micro.block_spec block)
      hlen hbound hleft hright hanswer hleftLo hleftHi
      hrightLo hrightHi hanswerLo hanswerHi

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead)
    (hblockSize : 0 < blockSize)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hlen hbound hleft hright hanswer
      blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount tableOverhead : Nat}
    (micro :
      BlockMicroCodebook shape blockSize codeCount tableOverhead) :
    micro.payload.length = codeCount * tableOverhead /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 1) /\
      (forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  0 < blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      rightClose ->
                    rightClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                    blockStartOf blockSize
                        (blockOfClose blockSize leftClose) <=
                      answerClose ->
                    answerClose <
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) +
                        blockSize ->
                      (micro.lcaCloseCosted
                        leftClose rightClose).erase =
                        some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_one leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hlen hbound hleft
      hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end BlockMicroCodebook

/--
Payload-live micro-codebook for BP close/LCA.

The query first performs a counted read from `classifier` to recover the
per-block code, then performs a counted read from the corresponding finite
codebook table.  The charged payload is exactly the classifier payload followed
by the finite codebook payload; no dense per-block close/LCA table is charged.
-/
structure PayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat) where
  classifier :
    BlockCodeTable blockCount codeCount codeWidth codeOverhead
  fieldWidth : Nat
  entriesByCode : Nat -> List (Option Nat)
  table :
    (code : Nat) ->
      FixedWidthOptionNatTable (entriesByCode code) fieldWidth
  slotIndex : Nat -> Nat -> Nat
  tablePayload : List Bool
  tablePayload_eq_tables :
    tablePayload =
      (List.range codeCount).flatMap fun code => (table code).payload
  tablePayload_length_eq : tablePayload.length = codeCount * tableOverhead
  table_payload_length_eq :
    forall {code : Nat}, code < codeCount ->
      (table code).payload.length = tableOverhead
  block_spec :
    forall {block code : Nat},
      classifier.codeAt block = some code ->
        BlockLocalBPCloseLCASpec shape
          (blockStartOf blockSize block) blockSize
          (entriesByCode code) slotIndex

namespace PayloadLiveBlockMicroCodebook

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) : List Bool :=
  micro.classifier.payload ++ micro.tablePayload

def lcaCloseCostedAtBlock
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (micro.classifier.codeCosted block) fun code? =>
    match code? with
    | none => Costed.pure none
    | some code =>
        if _hcode : code < codeCount then
          Costed.map (fun entry? => entry?.join)
            ((micro.table code).readCosted
              (micro.slotIndex
                (leftClose - blockStartOf blockSize block)
                (rightClose - blockStartOf blockSize block)))
        else
          Costed.pure none

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  micro.lcaCloseCostedAtBlock
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
      codeOverhead + codeCount * tableOverhead := by
  simp [payload, micro.classifier.payload_length,
    micro.tablePayload_length_eq]

theorem lcaCloseCostedAtBlock_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (block leftClose rightClose : Nat) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCostedAtBlock
  have hclassifier :=
    micro.classifier.codeCosted_cost_le_one block
  cases hread : (micro.classifier.codeCosted block).value with
  | none =>
      simp [Costed.bind, hread]
      omega
  | some code =>
      by_cases hcode : code < codeCount
      · simp [Costed.bind, hread, hcode, Costed.map_cost]
        omega
      · simp [Costed.bind, hread, hcode, Costed.pure]
        omega

theorem lcaCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (leftClose rightClose : Nat) :
    (micro.lcaCloseCosted leftClose rightClose).cost <= 2 := by
  unfold lcaCloseCosted
  exact micro.lcaCloseCostedAtBlock_cost_le_two
    (blockOfClose blockSize leftClose) leftClose rightClose

theorem lcaCloseCostedAtBlock_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    {block code left len leftClose rightClose answerClose : Nat}
    (hcodeAt : micro.classifier.codeAt block = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hleftLo : blockStartOf blockSize block <= leftClose)
    (hleftHi :
      leftClose < blockStartOf blockSize block + blockSize)
    (hrightLo : blockStartOf blockSize block <= rightClose)
    (hrightHi :
      rightClose < blockStartOf blockSize block + blockSize)
    (hanswerLo : blockStartOf blockSize block <= answerClose)
    (hanswerHi :
      answerClose < blockStartOf blockSize block + blockSize) :
    (micro.lcaCloseCostedAtBlock block leftClose rightClose).erase =
      some answerClose := by
  have hread :
      (micro.classifier.codeCosted block).value = some code := by
    simpa [Costed.erase] using
      micro.classifier.codeCosted_exact_of_codeAt hcodeAt
  have hcodeLt : code < codeCount :=
    micro.classifier.codeAt_lt hcodeAt
  have hlocal :
      (Costed.map (fun entry? => entry?.join)
        ((micro.table code).readCosted
          (micro.slotIndex
            (leftClose - blockStartOf blockSize block)
            (rightClose - blockStartOf blockSize block)))).erase =
        some answerClose := by
    exact
      blockLocalBPCloseLCA_read_exact
        (micro.table code) (micro.block_spec hcodeAt)
        hlen hbound hleft hright hanswer hleftLo hleftHi
        hrightLo hrightHi hanswerLo hanswerHi
  simpa [lcaCloseCostedAtBlock, Costed.erase, Costed.bind,
    hread, hcodeLt] using hlocal

theorem lcaCloseCosted_exact_of_left_block
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead)
    (hblockSize : 0 < blockSize)
    {code left len leftClose rightClose answerClose : Nat}
    (hcodeAt :
      micro.classifier.codeAt
          (blockOfClose blockSize leftClose) = some code)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hrightLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        rightClose)
    (hrightHi :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize)
    (hanswerLo :
      blockStartOf blockSize (blockOfClose blockSize leftClose) <=
        answerClose)
    (hanswerHi :
      answerClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (micro.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  unfold lcaCloseCosted
  exact
    micro.lcaCloseCostedAtBlock_exact hcodeAt hlen hbound hleft hright
      hanswer blockStartOf_blockOfClose_le
      (close_lt_blockStartOf_blockOfClose_add hblockSize)
      hrightLo hrightHi hanswerLo hanswerHi

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth
      codeOverhead tableOverhead : Nat}
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead tableOverhead) :
    micro.payload.length =
        codeOverhead + codeCount * tableOverhead /\
      (forall block : Nat,
        (micro.classifier.codeCosted block).cost <= 1 /\
          (micro.classifier.codeCosted block).erase =
            micro.classifier.codeAt block /\
          forall {code : Nat},
            micro.classifier.codeAt block = some code ->
              code < codeCount) /\
      (forall leftClose rightClose,
        (micro.lcaCloseCosted leftClose rightClose).cost <= 2) /\
      (forall {code left len leftClose rightClose answerClose : Nat},
        micro.classifier.codeAt
            (blockOfClose blockSize leftClose) = some code ->
          0 < len ->
            left + len <= shape.size ->
              bpCloseOfInorder? shape left = some leftClose ->
                bpCloseOfInorder? shape (left + len - 1) =
                    some rightClose ->
                  bpCloseOfInorder? shape
                      (scanWindow shape.representative left len) =
                    some answerClose ->
                    0 < blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        rightClose ->
                      rightClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                      blockStartOf blockSize
                          (blockOfClose blockSize leftClose) <=
                        answerClose ->
                      answerClose <
                        blockStartOf blockSize
                            (blockOfClose blockSize leftClose) +
                          blockSize ->
                        (micro.lcaCloseCosted
                          leftClose rightClose).erase =
                          some answerClose) := by
  constructor
  · exact micro.payload_length
  constructor
  · intro block
    have hprofile := micro.classifier.profile
    exact hprofile.2.2 block
  constructor
  · intro leftClose rightClose
    exact micro.lcaCloseCosted_cost_le_two leftClose rightClose
  intro code left len leftClose rightClose answerClose hcodeAt hlen hbound
    hleft hright hanswer hblockSize hrightLo hrightHi hanswerLo hanswerHi
  exact
    micro.lcaCloseCosted_exact_of_left_block hblockSize hcodeAt hlen hbound
      hleft hright hanswer hrightLo hrightHi hanswerLo hanswerHi

end PayloadLiveBlockMicroCodebook

/-- Empty fixed-width Nat classifier used by the dense fallback construction. -/
def emptyBlockCodeTable : BlockCodeTable 0 1 0 0 :=
  BlockCodeTable.ofEntries 0 1 0 0 ([] : List Nat)
    (by intro code hmem; cases hmem)
    rfl
    rfl
    (by intro block code hget; cases hget)

/-- Empty optional-Nat table used by the dense fallback construction. -/
def emptyOptionNatTable
    (fieldWidth : Nat) :
    FixedWidthOptionNatTable ([] : List (Option Nat)) fieldWidth :=
  FixedWidthOptionNatTable.ofEntries
    ([] : List (Option Nat)) fieldWidth
    (by intro entry value hmem _hentry; cases hmem)

/--
Payload-live micro phase that always misses.

It still performs the charged classifier read before returning `none`; the
point is to make the dense fallback macro leg below a concrete consumer of the
existing payload-live macro/micro directory surface.
-/
def emptyPayloadLiveBlockMicroCodebook
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat) :
    PayloadLiveBlockMicroCodebook shape blockSize 0 1 0 0 0 where
  classifier := emptyBlockCodeTable
  fieldWidth := fieldWidth
  entriesByCode := fun _ => []
  table := fun _ => emptyOptionNatTable fieldWidth
  slotIndex := densePairSlot blockSize
  tablePayload := []
  tablePayload_eq_tables := by
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  tablePayload_length_eq := by
    simp
  table_payload_length_eq := by
    intro code _hcode
    simp [emptyOptionNatTable, FixedWidthOptionNatTable.ofEntries,
      FixedWidthOptionNatTable.ofEncodedWords, flattenPayloadWords]
  block_spec := by
    intro block code hcodeAt
    have hnone : (emptyBlockCodeTable.codeAt block) = none := by
      simp [emptyBlockCodeTable, BlockCodeTable.codeAt,
        BlockCodeTable.ofEntries]
    rw [hnone] at hcodeAt
    cases hcodeAt

theorem emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth leftClose rightClose : Nat) :
    ((emptyPayloadLiveBlockMicroCodebook
      shape blockSize fieldWidth).lcaCloseCosted
        leftClose rightClose).erase = none := by
  have hcode :
      (emptyBlockCodeTable.codeCosted
        (blockOfClose blockSize leftClose)).value = none := by
    have h :=
      emptyBlockCodeTable.codeCosted_erase
        (blockOfClose blockSize leftClose)
    simpa [Costed.erase, emptyBlockCodeTable, BlockCodeTable.codeAt,
      BlockCodeTable.ofEntries] using h
  unfold PayloadLiveBlockMicroCodebook.lcaCloseCosted
    PayloadLiveBlockMicroCodebook.lcaCloseCostedAtBlock
  simp [emptyPayloadLiveBlockMicroCodebook, hcode, Costed.bind,
    Costed.pure]

/--
Macro/micro BP close/LCA query skeleton.

The micro codebook gets the first constant-time attempt.  If it misses, the
query falls back to an explicit macro component.  The exactness field matches
this control flow instead of pretending that a real macro/micro navigation
structure is still a single fixed-width table read.
-/
structure MacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize codeCount microTableOverhead macroOverhead macroCost : Nat)
    where
  micro :
    BlockMicroCodebook shape blockSize codeCount microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace MacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
      codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      1 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_one leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize codeCount microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      MacroMicroBPCloseLCADirectory shape blockSize codeCount
        microTableOverhead macroOverhead macroCost) :
    directory.payload.length =
        codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          1 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end MacroMicroBPCloseLCADirectory

/--
Payload-live macro/micro BP close/LCA directory.

This is the counted successor to `MacroMicroBPCloseLCADirectory`: the micro
phase reads a stored per-block code before reading the codebook table.  The
macro component remains an explicit interface, but its payload length, query
cost, and fallback exactness are all exposed here.
-/
structure PayloadLiveMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroPayload : List Bool
  macroPayload_length_eq : macroPayload.length = macroOverhead
  macroCosted : Nat -> Nat -> Costed (Option Nat)
  macro_cost_le :
    forall leftClose rightClose,
      (macroCosted leftClose rightClose).cost <= macroCost
  split_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
        left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
            bpCloseOfInorder? shape (left + len - 1) =
                some rightClose ->
              bpCloseOfInorder? shape
                  (scanWindow shape.representative left len) =
                some answerClose ->
                (micro.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose \/
                  ((micro.lcaCloseCosted leftClose rightClose).erase =
                      none /\
                    (macroCosted leftClose rightClose).erase =
                      some answerClose)

namespace PayloadLiveMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) : List Bool :=
  directory.micro.payload ++ directory.macroPayload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  Costed.bind (directory.micro.lcaCloseCosted leftClose rightClose)
    fun local? =>
      match local? with
      | some answerClose => Costed.pure (some answerClose)
      | none => directory.macroCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead + macroOverhead := by
  simp [payload, directory.micro.payload_length,
    directory.macroPayload_length_eq]

theorem lcaCloseCosted_cost_le
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <=
      2 + macroCost := by
  unfold lcaCloseCosted
  have hmicro :=
    directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
  cases hlocal :
      (directory.micro.lcaCloseCosted leftClose rightClose).value with
  | none =>
      have hmacro := directory.macro_cost_le leftClose rightClose
      simp [Costed.bind, hlocal]
      omega
  | some answerClose =>
      simp [Costed.bind, Costed.pure, hlocal]
      omega

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hsplit :=
    directory.split_exact hlen hbound hleft hright hanswer
  unfold lcaCloseCosted
  cases hsplit with
  | inl hlocalExact =>
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hlocalExact
      simp [Costed.bind, Costed.pure, Costed.erase, hlocalValue]
  | inr hfallback =>
      rcases hfallback with ⟨hlocalNone, hmacroExact⟩
      have hlocalValue :
          (directory.micro.lcaCloseCosted leftClose rightClose).value =
            none := by
        simpa [Costed.erase] using hlocalNone
      have hmacroValue :
          (directory.macroCosted leftClose rightClose).value =
            some answerClose := by
        simpa [Costed.erase] using hmacroExact
      simp [Costed.bind, Costed.erase, hlocalValue, hmacroValue]

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead macroOverhead macroCost : Nat}
    (directory :
      PayloadLiveMacroMicroBPCloseLCADirectory shape blockSize blockCount
        codeCount codeWidth codeOverhead microTableOverhead macroOverhead
        macroCost) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead + macroOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          2 + macroCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveMacroMicroBPCloseLCADirectory

/--
Guarded payload-live macro/micro BP close/LCA directory.

Unlike the compatibility `PayloadLiveMacroMicroBPCloseLCADirectory`, this query
does not ask the micro table about cross-block endpoints.  Same-block queries
use the charged micro-codebook path; cross-block queries use the charged
endpoint-fringe/range macro path.
-/
structure PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat) where
  micro :
    PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
      codeWidth codeOverhead microTableOverhead
  macroComponent :
    PayloadLiveBPEndpointFringeRangeMacro shape blockSize blockCount
      fieldWidth leftOverhead interiorOverhead rightOverhead
  blockSize_pos : 0 < blockSize
  close_block_lt :
    forall {close : Nat},
      close < shape.bpCode.length ->
        blockOfClose blockSize close < blockCount

namespace PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) : List Bool :=
  directory.micro.payload ++ directory.macroComponent.payload

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    (leftClose rightClose : Nat) :
    Costed (Option Nat) :=
  if blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose then
    directory.micro.lcaCloseCosted leftClose rightClose
  else
    directory.macroComponent.lcaCloseCosted leftClose rightClose

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
      codeOverhead + codeCount * microTableOverhead +
        (leftOverhead + interiorOverhead + rightOverhead) := by
  simp [payload, directory.micro.payload_length,
    directory.macroComponent.payload_length]

theorem lcaCloseCosted_cost_le_six
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    (leftClose rightClose : Nat) :
    (directory.lcaCloseCosted leftClose rightClose).cost <= 6 := by
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    have hmicro :=
      directory.micro.lcaCloseCosted_cost_le_two leftClose rightClose
    omega
  · simp [hsame]
    exact directory.macroComponent.lcaCloseCosted_cost_le_six
      leftClose rightClose

theorem lcaCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead)
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (directory.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount :=
    directory.close_block_lt hleftCloseBound
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount :=
    directory.close_block_lt hrightCloseBound
  have hbetween :=
    answerClose_between_endpoint_closes
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  unfold lcaCloseCosted
  by_cases hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose
  · simp [hsame]
    rcases directory.micro.classifier.codeAt_exists_of_lt hleftBlock with
      ⟨code, hcodeAt⟩
    have hrightLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          rightClose := by
      simpa [hsame] using
        (blockStartOf_blockOfClose_le
          (blockSize := blockSize) (close := rightClose))
    have hrightHi :
        rightClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      simpa [hsame] using
        (close_lt_blockStartOf_blockOfClose_add
          (blockSize := blockSize) (close := rightClose)
          directory.blockSize_pos)
    have hanswerLo :
        blockStartOf blockSize (blockOfClose blockSize leftClose) <=
          answerClose := by
      exact Nat.le_trans blockStartOf_blockOfClose_le hbetween.1
    have hanswerHi :
        answerClose <
          blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize := by
      exact Nat.lt_of_le_of_lt hbetween.2 hrightHi
    exact
      directory.micro.lcaCloseCosted_exact_of_left_block
        directory.blockSize_pos hcodeAt hlen hbound hleft hright hanswer
        hrightLo hrightHi hanswerLo hanswerHi
  · simp [hsame]
    have hleftRight : leftClose <= rightClose := by
      omega
    have hblockLe :
        blockOfClose blockSize leftClose <=
          blockOfClose blockSize rightClose := by
      unfold blockOfClose
      exact Nat.div_le_div_right hleftRight
    have hcross :
        blockOfClose blockSize leftClose <
          blockOfClose blockSize rightClose := by
      omega
    exact
      directory.macroComponent.lcaCloseCosted_exact_of_query_cross_block
        hlen hbound hleft hright hanswer directory.blockSize_pos
        hleftBlock hrightBlock hcross

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      leftOverhead interiorOverhead rightOverhead : Nat}
    (directory :
      PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth leftOverhead interiorOverhead
        rightOverhead) :
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (leftOverhead + interiorOverhead + rightOverhead) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  constructor
  · exact directory.payload_length
  constructor
  · intro leftClose rightClose
    exact directory.lcaCloseCosted_cost_le_six leftClose rightClose
  intro left len leftClose rightClose answerClose hlen hbound hleft
    hright hanswer
  exact directory.lcaCloseCosted_exact hlen hbound hleft hright hanswer

end PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory

def concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth
      (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
        fieldWidth))
      (2 * ((interiorBlockPairRanges blockCount).length * fieldWidth))
      (2 * ((endpointRightFringeRanges blockSize blockCount).length *
        fieldWidth)) where
  micro := micro
  macroComponent :=
    concreteBPEndpointFringeRangeMacro
      shape blockSize blockCount fieldWidth hwidth
  blockSize_pos := hblockSize
  close_block_lt := hcover

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    directory.payload.length =
        codeOverhead + codeCount * microTableOverhead +
          (2 * ((endpointLeftFringeRanges blockSize blockCount).length *
              fieldWidth) +
            2 * ((interiorBlockPairRanges blockCount).length *
              fieldWidth) +
            2 * ((endpointRightFringeRanges blockSize blockCount).length *
              fieldWidth)) /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  simpa [directory] using directory.profile

theorem guardedEndpointFringeMacroMicroOverhead_littleO
    (microOverhead : Nat -> Nat) (slots : Nat)
    (hmicro : LittleOLinear microOverhead) :
    LittleOLinear
      (fun n => microOverhead n + sampledDirectoryOverhead slots n) := by
  exact LittleOLinear.add hmicro (sampledDirectoryOverhead_littleO slots)

theorem concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth slots n : Nat)
    (microOverhead : Nat -> Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (micro :
      PayloadLiveBlockMicroCodebook shape blockSize blockCount codeCount
        codeWidth codeOverhead microTableOverhead)
    (hblockSize : 0 < blockSize)
    (hcover :
      forall {close : Nat},
        close < shape.bpCode.length ->
          blockOfClose blockSize close < blockCount)
    (hmicroLittle : LittleOLinear microOverhead)
    (hmicroBudget :
      codeOverhead + codeCount * microTableOverhead <= microOverhead n)
    (hmacroBudget :
      2 * ((endpointLeftFringeRanges blockSize blockCount).length *
          fieldWidth) +
        2 * ((interiorBlockPairRanges blockCount).length * fieldWidth) +
        2 * ((endpointRightFringeRanges blockSize blockCount).length *
          fieldWidth) <= sampledDirectoryOverhead slots n) :
    let directory :=
      concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
        shape blockSize blockCount codeCount codeWidth codeOverhead
        microTableOverhead fieldWidth hwidth micro hblockSize hcover
    LittleOLinear
        (fun n => microOverhead n + sampledDirectoryOverhead slots n) /\
      directory.payload.length <=
        microOverhead n + sampledDirectoryOverhead slots n /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= 6) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) =
                  some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted
                    leftClose rightClose).erase =
                    some answerClose := by
  let directory :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  have hprofile :=
    concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile
      shape blockSize blockCount codeCount codeWidth codeOverhead
      microTableOverhead fieldWidth hwidth micro hblockSize hcover
  constructor
  · exact guardedEndpointFringeMacroMicroOverhead_littleO
      microOverhead slots hmicroLittle
  constructor
  · rw [hprofile.1]
    omega
  constructor
  · exact hprofile.2.1
  · exact hprofile.2.2


end SuccinctCloseProposal
end RMQ
