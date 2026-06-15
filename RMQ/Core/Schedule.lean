import RMQ.Core.Spec

/-!
# Query scheduling helpers

This module contains block-boundary arithmetic used by hybrid RMQ schedules.
The definitions are deliberately independent of any concrete backend.
-/

namespace RMQ

/-- Number of full `b`-sized blocks in a list of length `n`. -/
def compressedLength (n b : Nat) : Nat :=
  n / b

theorem compressedLength_lt_self
    {n b : Nat} (hn : 0 < n) (hb : 1 < b) :
    compressedLength n b < n := by
  unfold compressedLength
  exact Nat.div_lt_self hn hb

/-- First block boundary strictly after `left`. -/
def leftBoundaryBlock (left b : Nat) : Nat :=
  left / b + 1

/-- Last block boundary at or before `right`. -/
def rightBoundaryBlock (right b : Nat) : Nat :=
  right / b

theorem left_lt_leftBoundaryBlock_mul
    {left b : Nat} (hb : 0 < b) :
    left < leftBoundaryBlock left b * b := by
  unfold leftBoundaryBlock
  have h := Nat.lt_div_mul_add hb (a := left)
  simpa [Nat.add_mul, Nat.one_mul, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

theorem rightBoundaryBlock_mul_le
    (right b : Nat) :
    rightBoundaryBlock right b * b <= right := by
  unfold rightBoundaryBlock
  exact Nat.div_mul_le_self right b

theorem rightBoundaryBlock_le_compressed
    {xs : List Int} {b right : Nat}
    (hb : 0 < b) (hright : right <= xs.length) :
    rightBoundaryBlock right b <= compressedLength xs.length b := by
  unfold rightBoundaryBlock compressedLength
  have hmul : (right / b) * b <= xs.length :=
    Nat.le_trans (Nat.div_mul_le_self right b) hright
  exact (Nat.le_div_iff_mul_le hb).2 hmul

end RMQ
