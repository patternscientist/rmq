import RMQ.Core.WordRAM.E1CloseLcaWidth
import RMQ.Core.WordRAM.E1SelectCloseWidth
import RMQ.Core.WordRAM.E1WholeQueryProgram

/-!
# Width accounting for the WHOLE-QUERY VALID PATH (REQ-E1-02)

The last composition layer.  `E1CloseLcaWidth.lean` certified the close/LCA
leg (4753 of 5646 instructions); this module adds the select prefix (813),
the join (6) and the output stage (64), and composes them.

## The shared width facts, named once

Every leaf below needs the same handful of shape-dependent bounds -- the
chunk width and its power, the code length, the rank directory's word size
and blocks-per-superblock.  `E1ReviewerWidth.lean` already proves each as a
LINEAR bound (`wordSize_le` `:203`, `blocksPerSuper_le` `:220`,
`blockSizeRaw_le` `:157`, `mix_le` `:174`, `bpCode_length_eq` `:151`), so
each is discharged here by the same capacity route rather than re-derived.

## The width is a PARAMETER

Every lemma in this module is stated at a parametric word width `w` under
the single hypothesis `WordAddressesStructure w shape.size` -- the word-RAM
model assumption that one machine word can address the structure.  Nothing
here needs `w` to be any particular width: the capacity bounds
(`lt_capacity_of_le_linear`, `lt_capacity_of_le_mul`) conclude
`< capacity shape.size` without mentioning a width at all, and
`lt_two_pow_of_lt_capacity` is the single step that crosses from the
capacity to the word.

`wholeQueryProgram_fits_reviewerWordBits` at the end of the module
instantiates this at the concrete reviewer width, which is the witness that
the assumption is satisfiable; `wholeQueryProgram_fits_logarithmicWidth`
records that the witnessing width is logarithmic in the input size.

DD-20260719-331, DD-20260719-332, DD-20260719-333.

`chunkPow_lt` is the one that is not a direct restatement:
`rankCloseBlock_fits` and the three select legs want `2 ^ c < 2 ^ w` for the
CHUNK width `c`, while `E1ReviewerWidth` bounds `2 ^ machineWordBits L`.
`bpFringeChunkBits_le_machineWordBits` (`E1FringeBridge.lean:82`) bridges
them by monotonicity of `2 ^ -`.

DD-20260719-304.
-/

namespace RMQ
namespace WordRAM
namespace E1WholeQueryPathWidth

open E1Machine
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1ReviewerWidth
open E1Query
open E1RankBlock
open E1SameBlockArm
open E1CloseLcaWidth
open E1SelectCloseWidth

/-! ## The shared width facts at the reviewer width -/

theorem code_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    shape.bpCode.length < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := bpCode_length_eq shape; omega))

theorem machineWordBits_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega))

theorem machineWordBitsPow_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    2 ^ SuccinctRank.machineWordBits shape.bpCode.length <
      2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := two_pow_machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega))

/-- `2 ^ c < 2 ^ w` for the CHUNK width, by monotonicity through
`bpFringeChunkBits_le_machineWordBits`. -/
theorem chunkPow_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    2 ^ bpFringeChunkBits shape.bpCode.length < 2 ^ w := by
  have hle : (2 : Nat) ^ bpFringeChunkBits shape.bpCode.length <=
      2 ^ SuccinctRank.machineWordBits shape.bpCode.length :=
    Nat.pow_le_pow_right (by omega)
      (bpFringeChunkBits_le_machineWordBits shape.bpCode.length)
  have := machineWordBitsPow_lt shape hcap
  omega

theorem chunkLin_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    2 * bpFringeChunkBits shape.bpCode.length + 2 < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := bpFringeChunkBits_le_machineWordBits shape.bpCode.length
    have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega))

theorem rankG_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    concreteBPNativeRankCloseTraceSegmentBase + 4 < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    simp [concreteBPNativeRankCloseTraceSegmentBase]))

theorem rankWS_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    (builtRelativeSplitBPCloseRankData shape).wordSize < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := wordSize_le shape; omega))

theorem rankBPS_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper <
      2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by
    have := blocksPerSuper_le shape; omega))

/-- The register ceiling of the whole-query glue.  `71` is `fRight`
(`E1SameBlockArm.lean:499`), the global maximum of the query register map. -/
theorem reg_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    (72 : Nat) < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by omega))

/-! ## The output stage -/

theorem wholeQueryRankSetup_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ wholeQueryRankSetup,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  intro instr hmem
  simp only [wholeQueryRankSetup, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨by simp only [rPos]; omega, by omega⟩
  · exact ⟨by simp only [rPos]; omega, by simp only [fRes]; omega,
      by simp only [rPos]; omega⟩

theorem wholeQueryPacketWrite_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ wholeQueryPacketWrite,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  intro instr hmem
  simp only [wholeQueryPacketWrite, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨by simp only [regOut]; omega, by simp only [rVal]; omega⟩
  · trivial

theorem wholeQueryRankLeg_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) {B : Nat}
    (hB : B + 60 < 2 ^ w) :
    ∀ instr ∈ wholeQueryRankLeg shape B,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  exact rankCloseBlock_fits (by omega) (rankG_lt shape hcap) (code_lt shape hcap)
    (bpFringeChunkBits_pos _)
    ((builtRelativeSplitBPCloseRankData shape).wordSize_pos) (rankWS_lt shape hcap)
    ((builtRelativeSplitBPCloseRankData shape).blocksPerSuper_pos)
    (rankBPS_lt shape hcap) (chunkPow_lt shape hcap) (chunkLin_lt shape hcap) hB

theorem wholeQueryOutputStage_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size)
    {B : Nat} (hB : B + 64 < 2 ^ w) :
    ∀ instr ∈ wholeQueryOutputStage shape B,
      Instr.FieldsFit w instr := by
  intro instr hmem
  simp only [wholeQueryOutputStage, List.mem_append] at hmem
  rcases hmem with h | h | h
  · exact wholeQueryRankSetup_fits shape hcap instr h
  · exact wholeQueryRankLeg_fits shape hcap (by omega) instr h
  · exact wholeQueryPacketWrite_fits shape hcap instr h

/-! ## The select glue -/

theorem selectLeftSetup_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ selectLeftSetup,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  intro instr hmem
  simp only [selectLeftSetup, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl
  exact ⟨by simp only [E1SelectBridge.xIdx]; omega,
    by simp only [regLeft]; omega⟩

theorem selectMidGlue_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ selectMidGlue,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  intro instr hmem
  simp only [selectMidGlue, List.mem_cons, List.not_mem_nil,
    or_false] at hmem
  rcases hmem with rfl | rfl
  · exact ⟨by simp only [regT1]; omega, by simp only [rVal]; omega⟩
  · exact ⟨by simp only [E1SelectBridge.xIdx]; omega,
      by simp only [regRight]; omega, by simp only [regT2]; omega⟩

theorem selectJoin_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) {noneExit : Nat}
    (hne : noneExit < 2 ^ w) :
    ∀ instr ∈ selectJoin noneExit,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  intro instr hmem
  simp only [selectJoin, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨by simp only [regG]; omega, by simp only [regT1]; omega,
      by simp only [regZero]; omega⟩
  · exact ⟨by simp only [regG]; omega, hne⟩
  · exact ⟨by simp only [regG]; omega, by simp only [rVal]; omega,
      by simp only [regZero]; omega⟩
  · exact ⟨by simp only [regG]; omega, hne⟩
  · exact ⟨by simp only [fClose]; omega, by simp only [regT1]; omega,
      by simp only [regT2]; omega⟩
  · exact ⟨by simp only [fRight]; omega, by simp only [rVal]; omega,
      by simp only [regT2]; omega⟩


/-! ## The select data's own quantities

E1-LaneM's residual 2 recorded that `SparseExceptionSelectData`
(`Source.lean:1693`) carries no `localSlotsPerSuper_pos` and no
`_le_machine`, so any bound on it must come from the CANONICAL BUILDER
(`Source.lean:2371`) rather than from a projection.  That is confirmed and is
what happens here: every bound below unfolds the builder (each bridge is
`rfl`, since the builder is a `where` instance) and then uses a lemma about
the underlying generic quantity.

`superStride` needs a case split the others do not.  Its bound comes from
`machineWordBits_sq_le_four_mul_self_of_pos` (`Arithmetic.lean:160`), which
has a real `0 < n` hypothesis, and `shape.bpCode.length = 2 * shape.size` is
ZERO at the empty shape.  There `superStride 0 = 1`, so the unconditional
bound carries a `+ 1`.
-/

theorem superStride_le (shape : Cartesian.CartesianShape) :
    GenericSelect.superStride shape.bpCode.length <= 8 * shape.size + 1 := by
  have hL := bpCode_length_eq shape
  rcases Nat.eq_zero_or_pos shape.bpCode.length with h | h
  · have hz : GenericSelect.superStride 0 = 1 := by
      unfold GenericSelect.superStride GenericSelect.wordBits
        SuccinctRank.machineWordBits
      simp
    rw [h]; omega
  · have hsq := GenericSelect.machineWordBits_sq_le_four_mul_self_of_pos h
    unfold GenericSelect.superStride GenericSelect.wordBits
    omega

theorem localStride_le (shape : Cartesian.CartesianShape) :
    GenericSelect.localStride shape.bpCode.length <= 8 * shape.size + 1 := by
  have h1 := GenericSelect.localStride_le_superStride shape.bpCode.length
  have h2 := superStride_le shape
  omega

/-- The bound E1-LaneM's residual 2 named as the one genuine gap.  It goes
through the GENERIC `selectLocalSlotsPerSuper_le_superStride`
(`DenseEntryTable.lean:650`), which needs both strides positive; the
canonical builder supplies both. -/
theorem localSlotsPerSuper_le (shape : Cartesian.CartesianShape) :
    GenericSelect.localSlotsPerSuper shape.bpCode.length
      <= 8 * shape.size + 1 := by
  have hbridge : GenericSelect.localSlotsPerSuper shape.bpCode.length =
      GenericSelect.selectLocalSlotsPerSuper
        (GenericSelect.superStride shape.bpCode.length)
        (GenericSelect.localStride shape.bpCode.length) := rfl
  have h := GenericSelect.selectLocalSlotsPerSuper_le_superStride
    (GenericSelect.superStride_pos shape.bpCode.length)
    (GenericSelect.localStride_pos shape.bpCode.length)
  have h2 := superStride_le shape
  omega

theorem longLen_le (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).longFlagBits.length <= 2 * shape.size := by
  have hbridge : (wholeQuerySelData shape).longFlagBits =
      GenericSelect.longSuperFlagBits shape.bpCode false := rfl
  have h := GenericSelect.longSuperFlagBits_length_le_length shape.bpCode false
  have hL := bpCode_length_eq shape
  rw [hbridge]; omega

theorem sparseLen_le (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).sparseDirectory.flagBits.length
      <= 2 * shape.size := by
  have hbridge : (wholeQuerySelData shape).sparseDirectory.flagBits =
      GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false := rfl
  have h := GenericSelect.sparseExceptionEffectiveFlagBits_length_le_length
    shape.bpCode false
  have hL := bpCode_length_eq shape
  rw [hbridge]; omega

theorem occurrenceCount_le (shape : Cartesian.CartesianShape) :
    GenericSelect.occurrenceCount shape.bpCode false <= 2 * shape.size := by
  have h := GenericSelect.occurrenceCount_le_length shape.bpCode false
  have hL := bpCode_length_eq shape
  omega

theorem selWordSize_le (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).wordSize <= 4 * shape.size + 1 := by
  have h := (wholeQuerySelData shape).wordSize_le_machine
  have h2 := machineWordBits_le shape.bpCode.length
  have hL := bpCode_length_eq shape
  omega

theorem longWS_le (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).longFlagRankData.wordSize
      <= 4 * shape.size + 1 := by
  have h := (wholeQuerySelData shape).longFlagRank_wordSize_le_machine
  have h2 := machineWordBits_le shape.bpCode.length
  have hL := bpCode_length_eq shape
  omega

theorem sparseWS_le (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).sparseDirectory.rankData.wordSize
      <= 4 * shape.size + 1 := by
  have h := (wholeQuerySelData shape).sparseDirectory.rank_wordSize_le_machine
  have h2 := machineWordBits_le shape.bpCode.length
  have hL := bpCode_length_eq shape
  omega

/-- Both flag-rank directories carry ONE block per superblock.  Neither
`longFlagRankBlocksPerSuper` (`Source.lean:351`) nor
`sparseExceptionEffectiveFlagRankBlocksPerSuper` (`FlagRank.lean:211`) had a
named equation anywhere in the tree; both are `rfl`. -/
theorem longBPS_eq (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).longFlagRankData.blocksPerSuper = 1 := rfl

theorem sparseBPS_eq (shape : Cartesian.CartesianShape) :
    (wholeQuerySelData shape).sparseDirectory.rankData.blocksPerSuper = 1 :=
  rfl

/-! ## The address ceiling

Every branch target in the executed program is at most `5644`
(`wholeQueryNoneExit`, `E1WholeQueryProgram.lean:532`), which is the
skeleton's own invalid-exit base.  One bound covers all of them. -/

theorem addr_lt (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    (5644 : Nat) < 2 ^ w :=
  lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by omega))

/-! ## The select leg, and the prefix -/

theorem wholeQuerySelectLeg_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) {A : Nat}
    (hA : A + 405 < 2 ^ w) :
    ∀ instr ∈ wholeQuerySelectLeg shape A,
      Instr.FieldsFit w instr := by
  have hreg := reg_lt shape hcap
  have hbig : (5644 : Nat) < 2 ^ w := addr_lt shape hcap
  -- The layout's fourteen segment fields are numeric literals
  -- (`Segments.lean:24`), but they are PROJECTIONS and therefore not reducible by
  -- `omega` until named.
  have eS1 : concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseOccurrence
      = 1 := rfl
  have eS2 : concreteBPNativeSelectCloseTraceSegmentLayout.superTable.baseWordIndex
      = 2 := rfl
  have eS3 : concreteBPNativeSelectCloseTraceSegmentLayout.superTable.rankBefore
      = 3 := rfl
  have eS4 : concreteBPNativeSelectCloseTraceSegmentLayout.superTable.firstOffset
      = 4 := rfl
  have eM1 : concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseOccurrence
      = 5 := rfl
  have eM2 : concreteBPNativeSelectCloseTraceSegmentLayout.localTable.baseWordIndex
      = 6 := rfl
  have eM3 : concreteBPNativeSelectCloseTraceSegmentLayout.localTable.rankBefore
      = 7 := rfl
  have eM4 : concreteBPNativeSelectCloseTraceSegmentLayout.localTable.firstOffset
      = 8 := rfl
  have eGL : concreteBPNativeSelectCloseTraceSegmentLayout.longFlagRankBase
      = 9 := rfl
  have eRL : concreteBPNativeSelectCloseTraceSegmentLayout.longRelativeBase
      = 12 := rfl
  have eGS : concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.rankBase
      = 13 := rfl
  have eRS :
      concreteBPNativeSelectCloseTraceSegmentLayout.sparseDirectory.relativeBase
      = 16 := rfl
  have eW : concreteBPNativeSelectCloseTraceSegmentLayout.bitWordBase = 0 := rfl
  have eST : concreteBPNativeSelectChunkTraceSegment = 22 := rfl
  -- The four stride fields reduce to their generic counterparts by `rfl`,
  -- the builder being a `where` instance; `omega` needs them named.
  have bSS : (wholeQuerySelData shape).superStride =
      GenericSelect.superStride shape.bpCode.length := rfl
  have bLSPS : (wholeQuerySelData shape).localSlotsPerSuper =
      GenericSelect.localSlotsPerSuper shape.bpCode.length := rfl
  have bLS : (wholeQuerySelData shape).localStride =
      GenericSelect.localStride shape.bpCode.length := rfl
  have bDLS : (wholeQuerySelData shape).sparseDirectory.localStride =
      GenericSelect.localStride shape.bpCode.length := rfl
  refine selectCloseBlock_fits (by omega) hA
    (bpFringeChunkBits_pos _)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (chunkPow_lt shape hcap) (chunkLin_lt shape hcap)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)
    (rankG_lt shape hcap) (by omega) (by omega)
    (GenericSelect.superStride_pos _)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (GenericSelect.localStride_pos _)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    ((wholeQuerySelData shape).wordSize_pos)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    (code_lt shape hcap)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    ((wholeQuerySelData shape).longFlagRankData.wordSize_pos)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    ((wholeQuerySelData shape).longFlagRankData.blocksPerSuper_pos)
    (by rw [longBPS_eq]; omega)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    ((wholeQuerySelData shape).sparseDirectory.rankData.wordSize_pos)
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear ?_))
    ((wholeQuerySelData shape).sparseDirectory.rankData.blocksPerSuper_pos)
    (by rw [sparseBPS_eq]; omega)
  · have := bpFringeChunkBits_le_machineWordBits shape.bpCode.length
    have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega            -- hc
  · have := occurrenceCount_le shape; omega          -- hOC
  · have := superStride_le shape; omega              -- hSS
  · have := localSlotsPerSuper_le shape; omega       -- hLSPS
  · have := localStride_le shape; omega              -- hLS
  · have := localStride_le shape; omega              -- hDLS
  · have := selWordSize_le shape; omega              -- hWS
  · have := longLen_le shape; omega                  -- hLLen
  · have := longWS_le shape; omega                   -- hLWS
  · have := sparseLen_le shape; omega                -- hSLen
  · have := sparseWS_le shape; omega                 -- hSWS

theorem wholeQuerySelectPrefix_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ wholeQuerySelectPrefix shape,
      Instr.FieldsFit w instr := by
  have hbig : (5644 : Nat) < 2 ^ w := addr_lt shape hcap
  intro instr hmem
  simp only [wholeQuerySelectPrefix, List.mem_append] at hmem
  rcases hmem with h | h | h | h
  · exact selectLeftSetup_fits shape hcap instr h
  · exact wholeQuerySelectLeg_fits shape hcap (by omega) instr h
  · exact selectMidGlue_fits shape hcap instr h
  · exact wholeQuerySelectLeg_fits shape hcap (by omega) instr h

/-! ## THE EXECUTED VALID PATH, AND THE PROGRAM -/

theorem wholeQueryValidPathThroughLca_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ wholeQueryValidPathThroughLca shape wholeQueryNoneExit,
      Instr.FieldsFit w instr := by
  have hbig : (5644 : Nat) < 2 ^ w := addr_lt shape hcap
  intro instr hmem
  simp only [wholeQueryValidPathThroughLca, List.mem_append] at hmem
  rcases hmem with h | h | h
  · exact wholeQuerySelectPrefix_fits shape hcap instr h
  · exact selectJoin_fits shape hcap (by simp only [wholeQueryNoneExit]; omega)
      instr h
  · exact closeLcaProgramAt_fits shape hcap (by omega) instr h

/-- **EVERY INSTRUCTION OF THE EXECUTED VALID PATH FITS.** -/
theorem wholeQueryValidPath_fits (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ∀ instr ∈ wholeQueryValidPath shape wholeQueryNoneExit,
      Instr.FieldsFit w instr := by
  have hbig : (5644 : Nat) < 2 ^ w := addr_lt shape hcap
  intro instr hmem
  simp only [wholeQueryValidPath, List.mem_append] at hmem
  rcases hmem with h | h
  · exact wholeQueryValidPathThroughLca_fits shape hcap instr h
  · exact wholeQueryOutputStage_fits shape hcap
      (by simp only [E1WholeQueryCloseLca.closeLcaExit]; omega) instr h

/--
**THE WIDTH CERTIFICATE, AT EVERY WORD THAT CAN ADDRESS THE STRUCTURE.**

The word-RAM statement: under the standard model assumption that a single
machine word can address the structure being queried, every instruction of
the executed whole-query program fits that word.  The width is a
PARAMETER; no particular width is named.

The hypothesis `WordAddressesStructure w shape.size` is
`concreteBPNativeSuccinctRMQReviewerCapacity shape.size ≤ 2 ^ w`, and the
capacity is linear in the input size
(`concreteBPNativeSuccinctRMQReviewerCapacity_linear`).  It is exactly the
two things any word-RAM word must accommodate, and nothing more:

* the largest **payload address** the machine reads -- the directories'
  strides, word sizes and table offsets, each proved linear in
  `shape.size` by a width-free lemma; and
* the largest **program address** it branches to -- `5644`, which is the
  program's own largest encoded field.  That one is a CONSTANT,
  independent of `n`: the program has a fixed `5646` instructions at every
  input size, so its address space does not grow.

Because the assumption is the only thing the development knows about `w`,
a reader may discharge it at whatever word size their model fixes.
`wholeQueryProgram_fits_reviewerWordBits` below discharges it at the
concrete reviewer width, and `wholeQueryProgram_fits_logarithmicWidth`
records that this width is logarithmic in the input size.
-/
theorem wholeQueryProgram_fits_of_wordAddressesStructure
    (shape : Cartesian.CartesianShape) {w : Nat}
    (hcap : WordAddressesStructure w shape.size) :
    ProgramFits w (wholeQueryProgram shape shape.size) := by
  have hbig : (5644 : Nat) < 2 ^ w := addr_lt shape hcap
  refine programSkeleton_fits
    (lt_two_pow_of_lt_capacity hcap (lt_capacity_of_le_linear (by omega)))
    ?_ (by omega) (wholeQueryValidPath_fits shape hcap)
  · simpa using hbig

/--
**THE WIDTH CERTIFICATE REQ-E1-02 ASKS FOR, ABOUT THE PROGRAM THAT ACTUALLY
EXECUTES** -- and the witness that the model assumption above is
SATISFIABLE, at a width this development exhibits rather than assumes.

Every instruction of `wholeQueryProgram shape shape.size` -- guard prologue,
the 5636-instruction valid path, invalid exit -- satisfies `Instr.FieldsFit`
at the modeled reviewer width `concreteBPNativeSuccinctRMQReviewerWordBits`,
AT EVERY SHAPE.  No size hypothesis, no threshold, no parametric `w`, and no
premise about the interior, the select block or the composition.

`wholeQueryProgram shape n` is DEFINITIONALLY
`programSkeleton n (wholeQueryValidPath shape wholeQueryNoneExit)`
(`E1WholeQueryProgram.lean:876`), which is exactly what
`wholeQueryMachineAgrees_of_bounds` (`E1WholeQueryAgreement.lean:68`) runs.
This is the sibling of `programSkeleton_fits_reviewerWordBits`
(`E1ReviewerWidth.lean:349`), which is about `assembledValidPath` -- a
DIFFERENT program, of length `547` against this one's `5636`, related to it
by no lemma.

`ProgramFits` is `E1Machine.lean:552` and quantifies over every instruction;
`Instr.FieldsFit` is `E1Machine.lean:535` and has one arm per constructor
with no wildcard `True` arm, so this is constructor-exhaustive and not a
default.
-/
theorem wholeQueryProgram_fits_reviewerWordBits
    (shape : Cartesian.CartesianShape) :
    ProgramFits (shapeWidth shape) (wholeQueryProgram shape shape.size) :=
  wholeQueryProgram_fits_of_wordAddressesStructure shape
    (capacity_le_two_pow_reviewerWordBits shape.size)

/-- **The certificate at any word at least as wide**, by monotonicity
(`ProgramFits.mono`, `E1Machine.lean`).  A reader who prefers to fix a
word size -- 64 bits, say -- and check it dominates the reviewer width
gets the certificate at their own width with no re-verification. -/
theorem wholeQueryProgram_fits_of_reviewerWordBits_le
    (shape : Cartesian.CartesianShape) {w : Nat}
    (hw : shapeWidth shape ≤ w) :
    ProgramFits w (wholeQueryProgram shape shape.size) :=
  (wholeQueryProgram_fits_reviewerWordBits shape).mono hw

/--
**THE MODEL ASSUMPTION IS SATISFIED AT A WIDTH LOGARITHMIC IN THE INPUT
SIZE.**

This is the single statement the succinct-data-structure literature's
`w = Θ(log n)` phrasing is asking for, and it is the one sentence a reader
would otherwise have to assemble from two places: there EXISTS a word
width `w`, bounded by `20 * (log2 (n + 2) + 1)`, at which the executed
whole-query program's every instruction fits.

The witness is the reviewer width itself; the logarithmic bound is
`concreteBPNativeSuccinctRMQReviewerWordBits_le_log`
(`ReviewerPhysical.lean`, published as `succinctRMQReviewerWordBitsLogarithmic`).

The existential is not a weakening: `wholeQueryProgram_fits_reviewerWordBits`
above names the witness explicitly.  The `∃` is here only so that the
width bound and the fitting claim appear in ONE proposition.
-/
theorem wholeQueryProgram_fits_logarithmicWidth
    (shape : Cartesian.CartesianShape) :
    ∃ w : Nat,
      w ≤ 20 * (Nat.log2 (shape.size + 2) + 1) ∧
        ProgramFits w (wholeQueryProgram shape shape.size) :=
  ⟨shapeWidth shape,
    concreteBPNativeSuccinctRMQReviewerWordBits_le_log shape.size,
    wholeQueryProgram_fits_reviewerWordBits shape⟩

end E1WholeQueryPathWidth
end WordRAM
end RMQ
