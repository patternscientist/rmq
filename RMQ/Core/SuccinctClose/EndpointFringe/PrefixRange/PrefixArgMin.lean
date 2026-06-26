import RMQ.Core.SuccinctClose.RangeWitness

/-!
# Endpoint-fringe prefix argmin basics

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

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

end SuccinctClose
end RMQ
