import RMQ.Core.SuccinctFinal

/-!
# EG-CP-F01: the frozen packed cell width `w`

Scratch evidence file (not in tree).
-/

namespace RMQ
namespace PackedHeader

open RMQ.SuccinctFinal

/-- The frozen packed cell width.  `n` is the input length. -/
def frozenWordWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (2 * n)

theorem frozenWordWidth_closed_form (n : Nat) :
    frozenWordWidth n = Nat.log2 (2 * n) + 1 := rfl

/-! ## log2 helpers -/

private theorem log2_eq_of_bounds {n k : Nat}
    (hlow : 2 ^ k <= n) (hhigh : n < 2 ^ (k + 1)) :
    Nat.log2 n = k := by
  have hpk : 0 < 2 ^ k := Nat.pow_pos (by omega)
  have hn : n ≠ 0 := by omega
  have h1 : k <= Nat.log2 n := (Nat.le_log2 hn).mpr hlow
  have h2 : Nat.log2 n < k + 1 := (Nat.log2_lt hn).mpr hhigh
  omega

theorem log2_zero : Nat.log2 0 = 0 := by simp

theorem log2_one : Nat.log2 1 = 0 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem log2_three : Nat.log2 3 = 1 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem log2_four : Nat.log2 4 = 2 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem log2_two_mul_of_pos {n : Nat} (hn : 0 < n) :
    Nat.log2 (2 * n) = Nat.log2 n + 1 := by
  have hn0 : n ≠ 0 := by omega
  have hself : 2 ^ Nat.log2 n <= n := Nat.log2_self_le hn0
  have hlt : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  refine log2_eq_of_bounds ?_ ?_
  · have hsucc : 2 ^ (Nat.log2 n + 1) = 2 ^ Nat.log2 n * 2 := by
      rw [Nat.pow_succ]
    omega
  · have hsucc : 2 ^ (Nat.log2 n + 1 + 1) = 2 ^ (Nat.log2 n + 1) * 2 := by
      rw [Nat.pow_succ]
    omega

/-! ## The three contract inequalities, for ALL `n` including 0 and 1 -/

theorem one_le_frozenWordWidth (n : Nat) : 1 <= frozenWordWidth n := by
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  omega

theorem lt_two_pow_frozenWordWidth (n : Nat) : n < 2 ^ frozenWordWidth n := by
  have h : 2 * n < 2 ^ (Nat.log2 (2 * n) + 1) := Nat.lt_log2_self
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  omega

theorem frozenWordWidth_le_two_mul_log2_succ (n : Nat) :
    frozenWordWidth n <= 2 * (Nat.log2 (n + 1) + 1) := by
  by_cases hn : n = 0
  · subst hn
    simp only [frozenWordWidth, SuccinctRank.machineWordBits]
    rw [show (2 * 0 : Nat) = 0 from rfl, log2_zero, Nat.zero_add, log2_one]
    omega
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have heq : Nat.log2 (2 * n) = Nat.log2 n + 1 := log2_two_mul_of_pos hpos
    have hmono : Nat.log2 n <= Nat.log2 (n + 1) :=
      SuccinctRank.natLog2_le_log2_of_le hn (by omega) (by omega)
    simp only [frozenWordWidth, SuccinctRank.machineWordBits]
    omega

/-! ## `K_w = 2` is the smallest literal that works -/

theorem frozenWordWidth_two : frozenWordWidth 2 = 3 := by
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  rw [show (2 * 2 : Nat) = 4 from rfl, log2_four]

theorem K_w_zero_fails : ¬ (frozenWordWidth 0 <= 0 * (Nat.log2 (0 + 1) + 1)) := by
  have h := one_le_frozenWordWidth 0
  omega

theorem K_w_one_fails : ¬ (frozenWordWidth 2 <= 1 * (Nat.log2 (2 + 1) + 1)) := by
  rw [frozenWordWidth_two, show (2 + 1 : Nat) = 3 from rfl, log2_three]
  omega

/-! ## Corollary: `w n = Theta (log n)` -/

theorem log2_succ_le_frozenWordWidth (n : Nat) :
    Nat.log2 (n + 1) + 1 <= frozenWordWidth n := by
  by_cases hn : n = 0
  · subst hn
    simp only [frozenWordWidth, SuccinctRank.machineWordBits]
    rw [show (2 * 0 : Nat) = 0 from rfl, log2_zero, log2_one]
    omega
  · have hpos : 0 < n := Nat.pos_of_ne_zero hn
    have heq : Nat.log2 (2 * n) = Nat.log2 n + 1 := log2_two_mul_of_pos hpos
    have hmono : Nat.log2 (n + 1) <= Nat.log2 (2 * n) :=
      SuccinctRank.natLog2_le_log2_of_le (by omega) (by omega) (by omega)
    simp only [frozenWordWidth, SuccinctRank.machineWordBits]
    omega

theorem frozenWordWidth_theta (n : Nat) :
    Nat.log2 (n + 1) + 1 <= frozenWordWidth n /\
      frozenWordWidth n <= 2 * (Nat.log2 (n + 1) + 1) :=
  ⟨log2_succ_le_frozenWordWidth n, frozenWordWidth_le_two_mul_log2_succ n⟩

theorem frozenWordWidth_littleO :
    SuccinctSpace.LittleOLinear frozenWordWidth :=
  SuccinctSpace.LittleOLinear.comp_two_mul_arg
    SuccinctRank.machineWordBits_littleO

/-! ## `w` is the rank directory's divisor -/

theorem route_wordSize_eq_machineWordBits (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize shape
      = SuccinctRank.machineWordBits shape.bpCode.length := rfl

theorem route_blocksPerSuper_eq_wordSize (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlocksPerSuper shape
      = builtRelativeSplitBPCloseRankWordSize shape := rfl

theorem route_wordSize_eq_frozen (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize shape
      = frozenWordWidth shape.size := by
  rw [route_wordSize_eq_machineWordBits, Cartesian.CartesianShape.bpCode_length]
  rfl

theorem route_blocksPerSuper_eq_frozen (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlocksPerSuper shape
      = frozenWordWidth shape.size := by
  rw [route_blocksPerSuper_eq_wordSize, route_wordSize_eq_frozen]

/-- Query independence, in the only non-vacuous form available: the route's
cell width for two shapes of equal size agrees, for every choice of endpoints
and every pair of stores.  The endpoint/store binders are unused on purpose --
that is the claim. -/
theorem route_wordSize_size_only
    (shape shape' : Cartesian.CartesianShape)
    (hsize : shape.size = shape'.size)
    (_left _right _left' _right' : Nat) :
    builtRelativeSplitBPCloseRankWordSize shape
      = builtRelativeSplitBPCloseRankWordSize shape' := by
  rw [route_wordSize_eq_frozen, route_wordSize_eq_frozen, hsize]

/-- The rank lookup at `RMQ/Core/SuccinctRank.lean:143` divides by
`wordSize` and then by `blocksPerSuper`; both are `frozenWordWidth shape.size`,
so the composite super-divisor is exactly `w * w`. -/
theorem route_rank_divisors_eq_frozen (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankWordSize shape = frozenWordWidth shape.size /\
      builtRelativeSplitBPCloseRankBlocksPerSuper shape
        = frozenWordWidth shape.size /\
      builtRelativeSplitBPCloseRankWordSize shape *
          builtRelativeSplitBPCloseRankBlocksPerSuper shape
        = frozenWordWidth shape.size * frozenWordWidth shape.size := by
  refine ⟨route_wordSize_eq_frozen shape, route_blocksPerSuper_eq_frozen shape, ?_⟩
  rw [route_wordSize_eq_frozen, route_blocksPerSuper_eq_frozen]

/-- The block sample *field width* is a distinct, nested quantity; it is not a
divisor.  It is pinned by `w` and bounded by `2 * w + 1`. -/
theorem route_blockWidth_eq_frozen (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth shape
      = SuccinctRank.machineWordBits
          (frozenWordWidth shape.size * frozenWordWidth shape.size) := by
  rw [show builtRelativeSplitBPCloseRankBlockWidth shape
        = SuccinctRank.machineWordBits
            (builtRelativeSplitBPCloseRankWordSize shape *
              builtRelativeSplitBPCloseRankWordSize shape) from rfl,
    route_wordSize_eq_frozen]

theorem route_blockWidth_le (shape : Cartesian.CartesianShape) :
    builtRelativeSplitBPCloseRankBlockWidth shape
      <= 2 * frozenWordWidth shape.size + 1 := by
  rw [route_blockWidth_eq_frozen]
  have hbound := SuccinctRank.machineWordBits_mul_self_log_bound
    (frozenWordWidth shape.size)
  have hself := GenericSelect.machineWordBits_le_self_of_pos
    (n := frozenWordWidth shape.size)
    (by have := one_le_frozenWordWidth shape.size; omega)
  omega

/-! ## Small-size table and pinned values -/

theorem frozenWordWidth_zero : frozenWordWidth 0 = 1 := by
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  rw [show (2 * 0 : Nat) = 0 from rfl, log2_zero]

theorem log2_two : Nat.log2 2 = 1 :=
  log2_eq_of_bounds (by decide) (by decide)

theorem frozenWordWidth_one : frozenWordWidth 1 = 2 := by
  simp only [frozenWordWidth, SuccinctRank.machineWordBits]
  rw [show (2 * 1 : Nat) = 2 from rfl, log2_two]

#eval (List.range 9).map frozenWordWidth
#eval (frozenWordWidth 512, frozenWordWidth 1024, frozenWordWidth 8192)

#print axioms one_le_frozenWordWidth
#print axioms lt_two_pow_frozenWordWidth
#print axioms frozenWordWidth_le_two_mul_log2_succ
#print axioms K_w_one_fails
#print axioms K_w_zero_fails
#print axioms frozenWordWidth_theta
#print axioms frozenWordWidth_littleO
#print axioms route_wordSize_eq_frozen
#print axioms route_blocksPerSuper_eq_frozen
#print axioms route_wordSize_size_only
#print axioms frozenWordWidth_zero
#print axioms route_rank_divisors_eq_frozen
#print axioms route_blockWidth_eq_frozen
#print axioms route_blockWidth_le
#print axioms frozenWordWidth_closed_form
#print axioms log2_two_mul_of_pos
#print axioms route_wordSize_eq_machineWordBits
#print axioms route_blocksPerSuper_eq_wordSize
#print axioms frozenWordWidth_one

end PackedHeader
end RMQ
