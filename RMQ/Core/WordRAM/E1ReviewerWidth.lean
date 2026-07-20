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

/-! ### The model assumption, as a hypothesis on a parametric width

`concreteBPNativeSuccinctRMQReviewerCapacity n` is the query machine's
ADDRESS SPACE at input size `n`: every address the machine forms -- every
payload address it reads and every program address it branches to -- is
proved to lie strictly inside it.  It is linear in the input size
(`concreteBPNativeSuccinctRMQReviewerCapacity_linear`,
`ReviewerPhysical.lean:1497`).

The word-RAM model assumption the construction actually needs is therefore
the textbook one -- A SINGLE WORD CAN ADDRESS THE STRUCTURE:

  `concreteBPNativeSuccinctRMQReviewerCapacity n ≤ 2 ^ w`

and nothing else.  No lemma in the width development ever needs `w` to be
any PARTICULAR width; the concrete reviewer width is used only as a supply
of this one inequality, never as a source of information about `w`.  The
two lemmas below are what make that visible: `lt_two_pow_of_lt_capacity`
replaces `lt_reviewerWordBits_of_lt_capacity` when the width is a
parameter, and `capacity_le_two_pow_reviewerWordBits` is the witness that
the assumption is satisfiable.

Note the capacity lemmas above (`lt_capacity_of_le_linear`, and
`lt_capacity_of_le_mul` in `E1CanonicalInteriorWidth`) conclude `< capacity
n` and never mention a width, so they are reused verbatim under a
parametric `w`. -/

/-- The parametric-width counterpart of `lt_reviewerWordBits_of_lt_capacity`:
a quantity inside the address space fits ANY word that can address the
structure, not merely the concrete reviewer width.

This is the single point at which the width development touches the width,
which is why generalising it generalises the whole development. -/
theorem lt_two_pow_of_lt_capacity {n x w : Nat}
    (hcap : concreteBPNativeSuccinctRMQReviewerCapacity n ≤ 2 ^ w)
    (h : x < concreteBPNativeSuccinctRMQReviewerCapacity n) : x < 2 ^ w :=
  Nat.lt_of_lt_of_le h hcap

/-- **The concrete reviewer width satisfies the model assumption.** This is
the witness that the assumption is not vacuous, and it is the
instantiation every concrete corollary below uses. -/
theorem capacity_le_two_pow_reviewerWordBits (n : Nat) :
    concreteBPNativeSuccinctRMQReviewerCapacity n
      ≤ 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n :=
  Nat.le_of_lt
    (SuccinctRank.self_lt_two_pow_machineWordBits
      (concreteBPNativeSuccinctRMQReviewerCapacity n))

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

/-! ## The assembled program, and the certificate at the reviewer width -/

/-- The reviewer word width at a shape's own size, named once. -/
abbrev shapeWidth (shape : Cartesian.CartesianShape) : Nat :=
  concreteBPNativeSuccinctRMQReviewerWordBits shape.size

/-- The canonical block size, named once. -/
abbrev shapeBlockSize (shape : Cartesian.CartesianShape) : Nat :=
  canonicalBPRelativeSummaryBlockSizeRaw shape

/-- The fringe segment index the same-block leg's reads are logged at.  This
is `E1MachineValidate.lean:361`'s `legFringeSegment`, not a fresh choice. -/
abbrev shapeFringeSegment : Nat := 5

/-- THE ASSEMBLED CONCRETE VALID PATH: the same-block dispatch carrying the
cross-block arm as its cross arm, at canonical parameters.  This is the
largest program the tree actually assembles; the interior dispatch exists
only as a category log (`dispatchCats`, `E1InteriorDispatchCompose.lean:374`)
and has no instruction list to embed, which is why `interior` is `[]`. -/
def assembledValidPath (shape : Cartesian.CartesianShape) : List Instr :=
  sameBlockDispatchProgram shape shapeFringeSegment (shapeBlockSize shape)
    (crossBlockArmProgramAt shape shapeFringeSegment (shapeBlockSize shape)
      0 [])

@[simp] theorem assembledValidPath_length (shape : Cartesian.CartesianShape) :
    (assembledValidPath shape).length = 547 := by
  simp [assembledValidPath]

/-- EVERY SIDE CONDITION OF THE CROSS-BLOCK ARM'S CERTIFICATE, DISCHARGED at
the reviewer width.  Before this the seventeen premises had no witness
anywhere in the tree. -/
theorem crossArm_fits_reviewerWidth (shape : Cartesian.CartesianShape) :
    ∀ instr ∈ crossBlockArmProgramAt shape shapeFringeSegment
      (shapeBlockSize shape) 0 [],
      Instr.FieldsFit (shapeWidth shape) instr := by
  refine crossBlockArmProgramAt_fits shape
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (bpFringeChunkBits_pos _)
    (bpFringeChunkBits_le_machineWordBits _)
    (SuccinctRank.machineWordBits_pos _)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    ((builtRelativeSplitBPCloseRankData shape).wordSize_pos)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    ((builtRelativeSplitBPCloseRankData shape).blocksPerSuper_pos)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (by intro instr h; cases h)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
  · omega                                             -- hreg  : 84
  · simp [shapeFringeSegment]                         -- hseg  : 5
  · have := blockSizeRaw_le shape
    simp only [shapeBlockSize]; omega                 -- hbs
  · have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hLw
  · have := bpCode_length_eq shape; omega             -- hcode
  · have := two_pow_machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hpowL
  · have := mix_le shape; omega                       -- hmix
  · simp [concreteBPNativeRankCloseTraceSegmentBase]  -- hG    : 17 + 4
  · have := wordSize_le shape; omega                  -- hWS
  · have := blocksPerSuper_le shape; omega            -- hBPS
  · simp                                              -- hA    : 0 + 370 + 0

/-- EVERY INSTRUCTION OF THE ASSEMBLED VALID PATH fits the reviewer width, at
every shape.  No size hypothesis, no threshold, no parametric `w`. -/
theorem assembledValidPath_fits_reviewerWidth
    (shape : Cartesian.CartesianShape) :
    ∀ instr ∈ assembledValidPath shape,
      Instr.FieldsFit (shapeWidth shape) instr := by
  refine sameBlockDispatchProgram_fits shape
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (canonicalBPRelativeSummaryBlockSizeRaw_pos shape)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    ((builtRelativeSplitBPCloseRankData shape).wordSize_pos)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    ((builtRelativeSplitBPCloseRankData shape).blocksPerSuper_pos)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (crossArm_fits_reviewerWidth shape)
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
  · omega                                             -- hreg  : 74
  · simp [shapeFringeSegment]                         -- hseg  : 5
  · have := blockSizeRaw_le shape
    simp only [shapeBlockSize]; omega                 -- hbs
  · have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hLw
  · have := bpCode_length_eq shape; omega             -- hcode
  · have := two_pow_machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hpowL
  · have := mix_le shape; omega                       -- hmix
  · simp [concreteBPNativeRankCloseTraceSegmentBase]  -- hG    : 17 + 4
  · have := wordSize_le shape; omega                  -- hWS
  · have := blocksPerSuper_le shape; omega            -- hBPS
  · simp                                              -- hlen  : 4 + 370 + 171

/--
**THE WIDTH CERTIFICATE REQ-E1-02 ASKS FOR.**

Every instruction of the whole concrete query program -- guard prologue,
assembled valid path, invalid exit -- satisfies `Instr.FieldsFit` at the
modeled reviewer width, AT EVERY SHAPE.  There is no size hypothesis and no
parametric `w` left carrying undischarged premises.

`ProgramFits` is `E1Machine.lean:552` and quantifies over every instruction
of the program; `Instr.FieldsFit` is `E1Machine.lean:535` and has one arm per
constructor with no wildcard `True` arm, so this is constructor-exhaustive
and not a default.
-/
theorem programSkeleton_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) :
    ProgramFits (shapeWidth shape)
      (E1Query.programSkeleton shape.size (assembledValidPath shape)) := by
  refine E1Query.programSkeleton_fits
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear (by omega)))
    (lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear ?_))
    (Nat.le_of_lt (lt_reviewerWordBits_of_lt_capacity
      (lt_capacity_of_le_linear (by omega))))
    (assembledValidPath_fits_reviewerWidth shape)
  · simp

/-! ## Anti-vacuity: the OTHER width is refuted, not merely avoided

A certificate at a generous width proves nothing on its own if the width is
so wide that `ProgramFits` holds of anything.  The two theorems below are the
witness that it is not: at the size-indexed width the very same program FAILS
the very same predicate, and it fails on a named instruction. -/

/-- The guard's invalid-exit branch carries the target `555`, and that
instruction really is in the assembled program.  Named because the
refutation below turns on it. -/
theorem invalidBranch_mem (shape : Cartesian.CartesianShape) :
    Instr.brNZ E1Query.regG 555 ∈
      E1Query.programSkeleton shape.size (assembledValidPath shape) := by
  have hlen : (assembledValidPath shape).length = 547 :=
    assembledValidPath_length shape
  simp [E1Query.programSkeleton, E1Query.guardBlock, hlen]

/--
**THE SIZE-INDEXED WIDTH IS REFUTED, as a checked theorem.**

At `SuccinctRank.machineWordBits shape.size` the assembled program does NOT
fit, for every shape of size at most `255`.  The witness is the guard's own
invalid-exit branch `brNZ regG 555`: its target field is `555`, while the
modeled bound `2 ^ machineWordBits shape.size` is at most `512` there.

This is what makes `programSkeleton_fits_reviewerWordBits` non-vacuous.  The
reviewer width is not merely a width at which the proof happens to go
through; it is a width that DISCRIMINATES, since the same statement at the
other candidate width is false and provably so.

The bound `255` is an artifact of how cheaply the refutation can be stated,
not of where the failure stops.  Evaluation at canonical parameters shows
the failure continues at every larger size too, because from size `512`
upward the binding field becomes `2 ^ machineWordBits shape.bpCode.length`
with `shape.bpCode.length = 2 * shape.size`, which outruns
`2 ^ machineWordBits shape.size` at every size.  DD-20260719-144 records the
evaluation; only the `<= 255` window is machine-checked here.
-/
theorem programSkeleton_not_fits_machineWordBits
    (shape : Cartesian.CartesianShape) (hsmall : shape.size ≤ 255) :
    ¬ ProgramFits (SuccinctRank.machineWordBits shape.size)
        (E1Query.programSkeleton shape.size (assembledValidPath shape)) := by
  intro hfits
  have hmem := invalidBranch_mem shape
  have hfield := hfits _ hmem
  have hbound : 555 < 2 ^ SuccinctRank.machineWordBits shape.size := by
    simpa [Instr.FieldsFit] using hfield.2
  have hle := two_pow_machineWordBits_le shape.size
  omega

end E1ReviewerWidth
end WordRAM
end RMQ
