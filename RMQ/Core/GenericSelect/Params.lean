import RMQ.Core.GenericSelect.LowLevel

/-!
# Generic select directory: Clark parameters and overhead (Tier 3/4)

Generic `n : Nat` analogues of the BP-specialised sparse/dense select
parameters and overhead budgets in `SuccinctSelect`, retargeted from
`shape.bpCode.length` to a plain bit-length `n`.  These are the leaves of the
`docs/GENERIC_SELECT_REFACTOR_SCOPE.md` refactor: pure functions of `n` plus
their positivity / `LittleOLinear` facts.  Nothing here reads payload or fixes a
target bit.
-/

namespace RMQ.GenericSelect

open SuccinctSpace SuccinctRank

/-- Generic machine word size for a length-`n` bitvector. -/
def wordBits (n : Nat) : Nat := SuccinctRank.machineWordBits n

/-- `log` of the word size plus one (the `ell` scale used for local strides). -/
def ell (n : Nat) : Nat := Nat.log2 (wordBits n) + 1

/-- Occurrences per superblock: `Theta(log^2 n)`. -/
def superStride (n : Nat) : Nat := wordBits n * wordBits n

/-- Occurrences per local block within a superblock. -/
def localStride (n : Nat) : Nat := max 1 (wordBits n / (ell n * ell n))

/-- Span threshold separating "long"/sparse superblocks from dense ones. -/
def superLongSpan (n : Nat) : Nat := superStride n * wordBits n * ell n

/-- Span threshold separating sparse local blocks from dense ones. -/
def localSparseSpan (n : Nat) : Nat := wordBits n

theorem wordBits_pos (n : Nat) : 0 < wordBits n :=
  SuccinctRank.machineWordBits_pos n

theorem ell_pos (n : Nat) : 0 < ell n := by
  unfold ell; omega

theorem superStride_pos (n : Nat) : 0 < superStride n := by
  unfold superStride
  exact Nat.mul_pos (wordBits_pos n) (wordBits_pos n)

theorem localStride_pos (n : Nat) : 0 < localStride n := by
  unfold localStride; omega

/--
Generic simple sparse/dense select overhead budget, evaluated at the bit length
`n` directly. The older BP-shaped profile fed `2 * n` only because its argument
was `shape.size` and the bit length is `2 * size`.
-/
def canonicalOverhead (n : Nat) : Nat :=
  sparseDenseSelectOverhead 32 32 32 32 n

theorem canonicalOverhead_littleO :
    SuccinctSpace.LittleOLinear canonicalOverhead := by
  unfold canonicalOverhead
  exact sparseDenseSelectOverhead_littleO 32 32 32 32

end RMQ.GenericSelect
