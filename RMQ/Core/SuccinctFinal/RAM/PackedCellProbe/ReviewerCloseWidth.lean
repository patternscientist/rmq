import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.ReviewerPhysicalRead

/-!
# The close half's chunk tables fit one cell

Segments `21` and `22` are `FixedWidthNatTable`s, so their reads are uniform word
grids exactly like the live access sources. Before either can be lowered to a probe,
its entry width has to be shown no wider than a reviewer cell -- otherwise a single
logical read would span three cells and the one-or-two-cell plan would not apply.

## Why this is not immediate

The cell width is `machineWordBits (packedReviewerCellBound n + 2)`, a **logarithm**
of the cell bound. It is not enough that a chunk entry is narrower than the payload;
the entry's *bound* has to be no larger than the cell bound. So the arithmetic below
compares bounds, not widths.

For the select chunk table this is easy: its entry bound is `c + 1`, and the table's
own overhead -- which is inside the reviewer overhead, hence inside the cell bound --
is `2 ^ c * (c + 1) * W`, already at least `c + 1`.

For the fringe chunk table it is not, because the entry bound `(2c+1)(2c+2)(c+1)` is
cubic in `c` while the naive lower bound on the table's overhead, `2 ^ c * (c+1)^2`,
only beats it from `c = 5` on. The gap is closed by the entry width itself: the
overhead carries a factor `W`, and `W >= 4` because a width of three or less would
force the entry bound below `2 ^ 3 = 8`, which contradicts `24 <= entryBound`. That
contradiction needs no evaluation of `Nat.log2`.

## What this module does not establish

Nothing about segment `20`. The interior component store is not a uniform grid at
all (see `ReviewerCloseGeometry`), so it has no single entry width to bound.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open RMQ.Cartesian

/-! ### The fringe chunk table -/

/--
**The fringe entry width is at least four.** A width of three or less would put the
entry bound under `2 ^ 3 = 8`, and the entry bound is at least `24` whenever the
chunk parameter is positive -- which `bpFringeChunkBits_pos` says it always is.
-/
private theorem packedFringeEntryWidth_ge_four (c : Nat) (hc : 1 <= c) :
    4 <= SuccinctClose.bpFringeChunkEntryWidth c := by
  have hlt := SuccinctClose.bpFringeChunkEntryBound_lt_two_pow_width c
  have h24 : 24 <= SuccinctClose.bpFringeChunkEntryBound c := by
    show 24 <= (2 * c + 1) * ((2 * c + 2) * (c + 1))
    have h1 : 3 <= 2 * c + 1 := by omega
    have hinner : 4 * 2 <= (2 * c + 2) * (c + 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hout : 3 * 8 <= (2 * c + 1) * ((2 * c + 2) * (c + 1)) :=
      Nat.mul_le_mul h1 (by omega)
    omega
  by_cases hW : 4 <= SuccinctClose.bpFringeChunkEntryWidth c
  · exact hW
  · have hle : SuccinctClose.bpFringeChunkEntryWidth c <= 3 := by omega
    have hpow :
        (2 : Nat) ^ SuccinctClose.bpFringeChunkEntryWidth c <= 2 ^ 3 :=
      Nat.pow_le_pow_right (by omega) hle
    have h8 : (2 : Nat) ^ 3 = 8 := by decide
    omega

/--
**The fringe entry bound is inside the fringe table's own overhead.** Cubic in `c` on
the left, `2 ^ c * (c + 1) ^ 2 * W` on the right; the factor `W >= 4` is what covers
the small `c` where the exponential has not yet taken over.
-/
private theorem packedFringeEntryBound_le_overhead (c : Nat) (hc : 1 <= c) :
    SuccinctClose.bpFringeChunkEntryBound c <=
      SuccinctClose.bpFringeChunkRowCount c *
        SuccinctClose.bpFringeChunkEntryWidth c := by
  have hW := packedFringeEntryWidth_ge_four c hc
  have hcpow : c + 1 <= 2 ^ c := Nat.lt_two_pow_self
  have hcube :
      (c + 1) * ((c + 1) * (c + 1)) <= SuccinctClose.bpFringeChunkRowCount c := by
    show (c + 1) * ((c + 1) * (c + 1)) <= 2 ^ c * ((c + 1) * (c + 1))
    exact Nat.mul_le_mul_right _ hcpow
  have hEB :
      SuccinctClose.bpFringeChunkEntryBound c <=
        4 * ((c + 1) * ((c + 1) * (c + 1))) := by
    show (2 * c + 1) * ((2 * c + 2) * (c + 1)) <=
      4 * ((c + 1) * ((c + 1) * (c + 1)))
    have hinner : (2 * c + 2) * (c + 1) <= (2 * (c + 1)) * (c + 1) :=
      Nat.mul_le_mul_right _ (by omega)
    have houter :
        (2 * c + 1) * ((2 * c + 2) * (c + 1)) <=
          (2 * (c + 1)) * ((2 * (c + 1)) * (c + 1)) :=
      Nat.mul_le_mul (by omega) hinner
    have hnorm :
        (2 * (c + 1)) * ((2 * (c + 1)) * (c + 1)) =
          4 * ((c + 1) * ((c + 1) * (c + 1))) := by
      simp [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm]
    omega
  have hscale :
      4 * ((c + 1) * ((c + 1) * (c + 1))) <=
        4 * SuccinctClose.bpFringeChunkRowCount c :=
    Nat.mul_le_mul (Nat.le_refl 4) hcube
  have hwiden :
      4 * SuccinctClose.bpFringeChunkRowCount c <=
        SuccinctClose.bpFringeChunkEntryWidth c *
          SuccinctClose.bpFringeChunkRowCount c :=
    Nat.mul_le_mul_right _ hW
  have hcomm :
      SuccinctClose.bpFringeChunkEntryWidth c *
          SuccinctClose.bpFringeChunkRowCount c =
        SuccinctClose.bpFringeChunkRowCount c *
          SuccinctClose.bpFringeChunkEntryWidth c :=
    Nat.mul_comm _ _
  omega

/-- **A fringe chunk entry is never wider than a reviewer cell.** -/
theorem packedFringeEntryWidth_le_reviewerCellWidth (n : Nat) :
    SuccinctClose.bpFringeChunkEntryWidth
        (SuccinctClose.bpFringeChunkBits (2 * n)) <=
      packedReviewerCellWidth n := by
  have hc : 1 <= SuccinctClose.bpFringeChunkBits (2 * n) :=
    SuccinctClose.bpFringeChunkBits_pos _
  have hover :=
    packedFringeEntryBound_le_overhead (SuccinctClose.bpFringeChunkBits (2 * n)) hc
  have hoverdef :
      SuccinctClose.bpFringeChunkRowCount
            (SuccinctClose.bpFringeChunkBits (2 * n)) *
          SuccinctClose.bpFringeChunkEntryWidth
            (SuccinctClose.bpFringeChunkBits (2 * n)) =
        SuccinctClose.bpFringeTableOverhead n := rfl
  have hbound :
      SuccinctClose.bpFringeChunkEntryBound
          (SuccinctClose.bpFringeChunkBits (2 * n)) <=
        packedReviewerCellBound n + 2 := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hdef :
      SuccinctClose.bpFringeChunkEntryWidth
          (SuccinctClose.bpFringeChunkBits (2 * n)) =
        SuccinctRank.machineWordBits
          (SuccinctClose.bpFringeChunkEntryBound
            (SuccinctClose.bpFringeChunkBits (2 * n))) := rfl
  rw [hdef]
  exact packedReviewerMachineWordBits_le_cellWidth hbound

/-! ### The select chunk table -/

/-- **A select chunk entry is never wider than a reviewer cell.** -/
theorem packedSelectChunkEntryWidth_le_reviewerCellWidth (n : Nat) :
    SuccinctClose.bpChunkSelectEntryWidth
        (SuccinctClose.bpFringeChunkBits (2 * n)) <=
      packedReviewerCellWidth n := by
  have hW :
      0 <
        SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits (2 * n)) :=
    SuccinctRank.machineWordBits_pos _
  have hpow :
      0 < (2 : Nat) ^ SuccinctClose.bpFringeChunkBits (2 * n) :=
    Nat.two_pow_pos _
  -- `c + 1 <= rowCount`, by the exponential factor being at least one.
  have hrow :
      SuccinctClose.bpFringeChunkBits (2 * n) + 1 <=
        SuccinctClose.bpChunkSelectRowCount
          (SuccinctClose.bpFringeChunkBits (2 * n)) := by
    have hmul :
        1 * (SuccinctClose.bpFringeChunkBits (2 * n) + 1) <=
          2 ^ SuccinctClose.bpFringeChunkBits (2 * n) *
            (SuccinctClose.bpFringeChunkBits (2 * n) + 1) :=
      Nat.mul_le_mul_right _ hpow
    rw [Nat.one_mul] at hmul
    exact hmul
  -- `rowCount <= rowCount * width`, by the width being at least one.
  have hwiden :
      SuccinctClose.bpChunkSelectRowCount
          (SuccinctClose.bpFringeChunkBits (2 * n)) <=
        SuccinctClose.bpChunkSelectRowCount
            (SuccinctClose.bpFringeChunkBits (2 * n)) *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits (2 * n)) := by
    have hmul :
        SuccinctClose.bpChunkSelectRowCount
              (SuccinctClose.bpFringeChunkBits (2 * n)) * 1 <=
          SuccinctClose.bpChunkSelectRowCount
              (SuccinctClose.bpFringeChunkBits (2 * n)) *
            SuccinctClose.bpChunkSelectEntryWidth
              (SuccinctClose.bpFringeChunkBits (2 * n)) :=
      Nat.mul_le_mul (Nat.le_refl _) hW
    rw [Nat.mul_one] at hmul
    exact hmul
  have hoverdef :
      SuccinctClose.bpChunkSelectRowCount
            (SuccinctClose.bpFringeChunkBits (2 * n)) *
          SuccinctClose.bpChunkSelectEntryWidth
            (SuccinctClose.bpFringeChunkBits (2 * n)) =
        SuccinctClose.bpChunkSelectTableOverhead n := rfl
  have hstep :
      SuccinctClose.bpFringeChunkBits (2 * n) + 1 <=
        SuccinctClose.bpChunkSelectTableOverhead n := by
    rw [← hoverdef]
    exact Nat.le_trans hrow hwiden
  have hbound :
      SuccinctClose.bpFringeChunkBits (2 * n) + 1 <=
        packedReviewerCellBound n + 2 := by
    unfold packedReviewerCellBound
      concreteBPNativeSuccinctRMQCanonicalReviewerOverhead
    omega
  have hdef :
      SuccinctClose.bpChunkSelectEntryWidth
          (SuccinctClose.bpFringeChunkBits (2 * n)) =
        SuccinctRank.machineWordBits
          (SuccinctClose.bpFringeChunkBits (2 * n) + 1) := rfl
  rw [hdef]
  exact packedReviewerMachineWordBits_le_cellWidth hbound

end PackedCellProbe

end SuccinctFinal

end RMQ
