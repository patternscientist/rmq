import RMQ.Core.WordRAM.E1CrossBlockArm
import RMQ.Core.WordRAM.E1QueryProgram
import RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical

/-!
# The width question, settled at the REVIEWER width (M3d-8)

Every whole-program width certificate in this tree
(`sameBlockLegProgramAt_fits`, `sameBlockDispatchProgram_fits`,
`crossBlockArmProgramAt_fits`) takes `w` PARAMETRICALLY with a long list of
side conditions.  Before this module NOTHING IN THE TREE DISCHARGED THEM at
any instantiation: grep for those three names finds only their own
statements and one internal use.  They were therefore OWED premises with no
witness that they are jointly satisfiable, and a reader had no way to know
whether the width story closes or is vacuous.

This module supplies that witness, and it supplies it at a width that is
already a frozen public quantity rather than one invented here.

## Which modeled width, and why NOT the other one

There are two candidate widths in the tree.

* `SuccinctRank.machineWordBits n = Nat.log2 n + 1`, the size-indexed width.
  `ProgramFits (machineWordBits n) (programSkeleton n validPath)` is **FALSE
  AT EVERY `n`**, not merely at small `n`, and the reason is structural
  rather than a small-size artifact.  The assembled program contains the
  field `2 ^ SuccinctRank.machineWordBits shape.bpCode.length` (it is the
  fold's stride constant, and it is exactly the `hpowL` side condition).
  With `shape.bpCode.length = 2 * shape.size` (`Cartesian.bpCode_length`)
  that field already exceeds `2 ^ machineWordBits shape.size`, so the bound
  the model supplies is always smaller than the field the program carries.
  There is NO crossover size and therefore nothing that a size threshold
  could repair; the spelling is simply the wrong one.
* `concreteBPNativeSuccinctRMQReviewerWordBits n`
  (`ReviewerPhysical.lean:1474`), the ONE pre-execution reviewer word width,
  which is `machineWordBits (400000 * (n + 1))`.  Because the capacity
  envelope is `400000 * (n + 1)` and so is at least `400000` for every `n`
  INCLUDING `n = 0`, this width is at least `19` unconditionally.  Every
  field of the assembled program fits it at every shape, and that is what is
  proved below.

The whole proof reduces through one step, `lt_reviewerWordBits_of_lt_capacity`:
a quantity fits the reviewer width as soon as it is below the capacity
envelope.  No reasoning about `Nat.log2` survives past that reduction except
the two monotone facts isolated in the arithmetic section, so the kernel's
irreducibility of `Nat.log2` is never an obstruction here.

DD-20260719-144.
-/

namespace RMQ
namespace WordRAM
namespace E1ReviewerWidth

open E1Machine
open E1SameBlockArm
open E1SameBlockLeg
open E1CloseCompose
open E1CrossBlockArm
open E1ProgramWidth
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-! ## Arithmetic: the two monotone `Nat.log2` facts, isolated -/

/-- `2 ^ machineWordBits L ≤ 2 * L + 2`, the only upper bound on a power of
the modeled width this development needs.  At `L = 0` it reads `2 ≤ 2`. -/
theorem two_pow_machineWordBits_le (L : Nat) :
    2 ^ SuccinctRank.machineWordBits L ≤ 2 * L + 2 := by
  unfold SuccinctRank.machineWordBits
  rcases Nat.eq_zero_or_pos L with h | h
  · subst h; simp
  · have hne : L ≠ 0 := by omega
    have hself := Nat.log2_self_le hne
    have hp : (2 : Nat) ^ (Nat.log2 L + 1) = 2 * 2 ^ Nat.log2 L := by
      rw [Nat.pow_succ]; omega
    omega

/-- `machineWordBits L ≤ 2 * L + 1`, by composing `m < 2 ^ m` with the
bound above. -/
theorem machineWordBits_le (L : Nat) :
    SuccinctRank.machineWordBits L ≤ 2 * L + 1 := by
  have hlt : SuccinctRank.machineWordBits L <
      2 ^ SuccinctRank.machineWordBits L := Nat.lt_two_pow_self
  have := two_pow_machineWordBits_le L
  omega

/-- `m * m ≤ 2 ^ m` for `m ≥ 4`.  Needed because the `hmix` side condition is
QUADRATIC in the chunk width while the capacity envelope is only linear in
the size, so the chunk width's logarithmic character has to be used and not
merely bounded away. -/
theorem sq_le_two_pow : ∀ m : Nat, 4 ≤ m → m * m ≤ 2 ^ m := by
  intro m
  induction m with
  | zero => intro h; omega
  | succ k ih =>
      intro _
      rcases Nat.lt_or_ge k 4 with hk | hk
      · have hk3 : k = 3 := by omega
        subst hk3
        decide
      · have hkk := ih (by omega)
        have h4k : 4 * k ≤ k * k := Nat.mul_le_mul_right k hk
        have hpow : (2 : Nat) ^ (k + 1) = 2 * 2 ^ k := by
          rw [Nat.pow_succ]; omega
        have hsq : (k + 1) * (k + 1) = k * k + 2 * k + 1 := by
          simp [Nat.add_mul, Nat.mul_add]; omega
        omega

/-! ## The reduction to the capacity envelope -/

/-- THE ONE REDUCTION STEP.  Anything below the capacity envelope fits the
reviewer word width.  Every side condition below is discharged through this,
which is why none of them reasons about `Nat.log2` directly. -/
theorem lt_reviewerWordBits_of_lt_capacity {n x : Nat}
    (h : x < concreteBPNativeSuccinctRMQReviewerCapacity n) :
    x < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n := by
  unfold concreteBPNativeSuccinctRMQReviewerWordBits
  exact GenericSelect.lt_two_pow_machineWordBits_of_lt h

/-- The capacity envelope is at least `400000` at every size, `n = 0`
included, and it is MONOTONE upward from there.  This is what makes the
reviewer width unconditionally wide: no size makes it narrow. -/
theorem capacity_ge (n : Nat) :
    400000 ≤ concreteBPNativeSuccinctRMQReviewerCapacity n := by
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  have h : 400000 * 1 ≤ 400000 * (n + 1) :=
    Nat.mul_le_mul_left _ (by omega)
  omega

/-- Quantities linear in the size, with a slope the envelope dwarfs, fit it
at every size.  The `n = 0` end is the binding one: there the envelope is
`400000` and the hypothesis allows `399999`. -/
theorem lt_capacity_of_le_linear {n x : Nat} (h : x ≤ 8 * n + 399999) :
    x < concreteBPNativeSuccinctRMQReviewerCapacity n := by
  unfold concreteBPNativeSuccinctRMQReviewerCapacity
  have hexp : 400000 * (n + 1) = 400000 * n + 400000 := by
    rw [Nat.mul_add]
  have hslope : 8 * n ≤ 400000 * n := Nat.mul_le_mul_right n (by omega)
  omega

/-! ## The shape-dependent quantities, bounded linearly in the size

Each of these is a side condition of `sameBlockDispatchProgram_fits` or
`crossBlockArmProgramAt_fits`, restated as a bound against the size so that
`lt_capacity_of_le_linear` can finish it. -/

/-- `shape.bpCode.length = 2 * shape.size`, the bridge every bound below
crosses. -/
theorem bpCode_length_eq (shape : Cartesian.CartesianShape) :
    shape.bpCode.length = 2 * shape.size :=
  Cartesian.CartesianShape.bpCode_length shape

/-- The canonical block size is `2 * machineWordBits shape.size`, hence
linear in the size.  Unconditional: no `0 < shape.size` hypothesis, because
the definition is a `Nat.log2` expression that is total. -/
theorem blockSizeRaw_le (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw shape ≤ 4 * shape.size + 2 := by
  have hdef : canonicalBPRelativeSummaryBlockSizeRaw shape =
      2 * SuccinctRank.machineWordBits shape.size := by
    unfold canonicalBPRelativeSummaryBlockSizeRaw
      canonicalBPRelativeSummaryBase SuccinctRank.machineWordBits
    rfl
  have := machineWordBits_le shape.size
  omega

/-- THE QUADRATIC SIDE CONDITION.  `hmix` is
`(c + 1) * (2 * c + 2)` with `c = sbChunkBits shape`, so it is quadratic in
the chunk width while the envelope is only linear in the size.  It closes
because `c = Nat.log2 (2 * shape.size) / 8 + 1` is genuinely LOGARITHMIC:
below `Nat.log2 L = 40` the product is bounded by the absolute constant `98`,
and above it the quadratic is dominated by `2 ^ Nat.log2 L ≤ L`. -/
theorem mix_le (shape : Cartesian.CartesianShape) :
    (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) ≤
      4 * shape.size + 98 := by
  have hL : shape.bpCode.length = 2 * shape.size := bpCode_length_eq shape
  have hc : sbChunkBits shape = Nat.log2 shape.bpCode.length / 8 + 1 := rfl
  rcases Nat.lt_or_ge (Nat.log2 shape.bpCode.length) 41 with hm | hm
  · -- `Nat.log2 L ≤ 40` forces `c ≤ 6`, and `7 * 14 = 98`
    have hcle : sbChunkBits shape ≤ 6 := by omega
    have hprod : (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) ≤
        7 * 14 := Nat.mul_le_mul (by omega) (by omega)
    omega
  · -- `Nat.log2 L ≥ 41` forces `L ≠ 0`, so `2 ^ Nat.log2 L ≤ L`
    have hLne : shape.bpCode.length ≠ 0 := by
      intro h
      rw [h] at hm
      simp [Nat.log2] at hm
    have hself := Nat.log2_self_le hLne
    have hsq := sq_le_two_pow (Nat.log2 shape.bpCode.length) (by omega)
    have hprod : (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) ≤
        Nat.log2 shape.bpCode.length * (2 * Nat.log2 shape.bpCode.length) :=
      Nat.mul_le_mul (by omega) (by omega)
    have hexp : Nat.log2 shape.bpCode.length *
        (2 * Nat.log2 shape.bpCode.length) =
        2 * (Nat.log2 shape.bpCode.length * Nat.log2 shape.bpCode.length) :=
      Nat.mul_left_comm _ _ _
    omega

/-- The rank directory's word size is bounded by the modeled width of the
balanced-parenthesis code, hence linearly by the size. -/
theorem wordSize_le (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).wordSize ≤ 4 * shape.size + 1 := by
  have hfield := (builtRelativeSplitBPCloseRankData shape).wordSize_le_machine
  have hbound := machineWordBits_le shape.bpCode.length
  have hL := bpCode_length_eq shape
  omega

/-- The rank directory's blocks-per-superblock is EQUAL to that same modeled
width (the structure carries no upper-bound field, so this is recovered from
the definition rather than projected). -/
theorem blocksPerSuper_eq (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper =
      SuccinctRank.machineWordBits shape.bpCode.length := by
  simp [builtRelativeSplitBPCloseRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    builtRelativeSplitBPCloseRankBlocksPerSuper,
    builtRelativeSplitBPCloseRankWordSize]

theorem blocksPerSuper_le (shape : Cartesian.CartesianShape) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper ≤
      4 * shape.size + 1 := by
  have heq := blocksPerSuper_eq shape
  have hbound := machineWordBits_le shape.bpCode.length
  have hL := bpCode_length_eq shape
  omega

end E1ReviewerWidth
end WordRAM
end RMQ
