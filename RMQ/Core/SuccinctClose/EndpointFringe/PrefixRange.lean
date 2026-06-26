import RMQ.Core.SuccinctClose.RangeWitness

/-!
# Endpoint-fringe prefix-range witnesses

Prefix-range argmin/excess lemmas and payload-live prefix-range witness tables
for the endpoint-fringe BP close path. The historical
`RMQ.SuccinctCloseProposal` namespace is preserved.
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


end SuccinctCloseProposal
end RMQ
