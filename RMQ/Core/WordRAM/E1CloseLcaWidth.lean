import RMQ.Core.WordRAM.E1CanonicalInteriorWidth
import RMQ.Core.WordRAM.E1WholeQueryCloseLca

/-!
# Width accounting for the CLOSE/LCA LEG (REQ-E1-02)

`closeLcaProgramAt` (`E1WholeQueryCloseLca.lean:119`, 4753 instructions) is
the largest single component of the executed whole-query program, and before
this module it had no `FieldsFit` lemma.  Its three parts each had a
parametric certificate whose premises had no witness at this instantiation:

* `closeDispatch_fits` (`E1CloseDispatch.lean:106`) -- already existed;
* `crossBlockArmProgramAt_fits` (`E1CrossBlockArm.lean:913`) -- existed with
  seventeen premises, of which the last, `hinterior`, was OWED and had no
  witness anywhere until `canonicalInteriorDispatchBlock_fits`
  (DD-20260719-301) supplied one;
* `sameBlockLegProgramAt_fits` (`E1ProgramWidth.lean:57`) -- already existed.

## The reuse, and the one thing that could not be reused

`crossArm_fits_reviewerWidth` (`E1ReviewerWidth.lean:261`) discharges the
same seventeen premises, but for `crossBlockArmProgramAt shape
shapeFringeSegment (shapeBlockSize shape) 0 []` -- the ASSEMBLED path's cross
arm, at segment `5`, base `0`, and with `interior = []`, whose `hinterior` is
`by intro instr h; cases h`.  The executed leg's cross arm is at segment
`concreteBPNativeFringeChunkTraceSegment = 21` (`Segments.lean:79`), base
`A + 4`, and carries 4204 real instructions.  The two are not instances of
one another, so the fifteen shape-dependent side conditions are re-discharged
here by the same route while `hinterior` and `hA` are genuinely new.

DD-20260719-303.
-/

namespace RMQ
namespace WordRAM
namespace E1CloseLcaWidth

open E1Machine
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1ReviewerWidth
open E1CanonicalInteriorWidth
open E1CloseDispatch
open E1ProgramWidth
open E1InteriorDispatchCompose
open E1WholeQueryCloseLca

/-- **THE EXECUTED CROSS ARM FITS** -- all 4574 instructions, interior
included.  This is the first consumer of `canonicalInteriorDispatchBlock_fits`
and the reason `hinterior` stopped being an owed premise. -/
theorem closeLcaCrossArm_fits (shape : Cartesian.CartesianShape) {A : Nat}
    (hA : A + 4578 < 2 ^ shapeWidth shape) :
    ∀ instr ∈ closeLcaCrossArm shape A,
      Instr.FieldsFit (shapeWidth shape) instr := by
  have hseg : concreteBPNativeFringeChunkTraceSegment = 21 := rfl
  refine E1CrossBlockArm.crossBlockArmProgramAt_fits shape
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
    (canonicalInteriorDispatchBlock_fits shape (by
      simpa [canonicalInteriorDispatchBlock_length] using
        (by omega : A + 4 + 176 + 4204 < 2 ^ shapeWidth shape)))
    (by simpa [canonicalInteriorDispatchBlock_length] using hA)
  · omega                                             -- hreg  : 84
  · omega                                             -- hseg  : 21
  · have := blockSizeRaw_le shape; omega              -- hbs
  · have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hLw
  · have := bpCode_length_eq shape; omega             -- hcode
  · have := two_pow_machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hpowL
  · have := mix_le shape; omega                       -- hmix
  · simp [concreteBPNativeRankCloseTraceSegmentBase]  -- hG    : 17 + 4
  · have := wordSize_le shape; omega                  -- hWS
  · have := blocksPerSuper_le shape; omega            -- hBPS

/-- **THE EXECUTED SAME-BLOCK ARM FITS** -- all 173 instructions. -/
theorem closeLcaSameArm_fits (shape : Cartesian.CartesianShape) {A : Nat}
    (hA : A + 4751 < 2 ^ shapeWidth shape) :
    ∀ instr ∈ closeLcaSameArm shape A,
      Instr.FieldsFit (shapeWidth shape) instr := by
  have hseg : concreteBPNativeFringeChunkTraceSegment = 21 := rfl
  refine sameBlockLegProgramAt_fits shape
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
    (by omega)
  · omega                                             -- hreg  : 74
  · omega                                             -- hseg  : 21
  · have := blockSizeRaw_le shape; omega              -- hbs
  · have := machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hLw
  · have := bpCode_length_eq shape; omega             -- hcode
  · have := two_pow_machineWordBits_le shape.bpCode.length
    have := bpCode_length_eq shape; omega             -- hpowL
  · have := mix_le shape; omega                       -- hmix
  · simp [concreteBPNativeRankCloseTraceSegmentBase]  -- hG    : 17 + 4
  · have := wordSize_le shape; omega                  -- hWS
  · have := blocksPerSuper_le shape; omega            -- hBPS

/-- **THE WHOLE CLOSE/LCA LEG FITS** -- all 4753 instructions: dispatch,
terminated cross arm (interior included), and same-block arm. -/
theorem closeLcaProgramAt_fits (shape : Cartesian.CartesianShape) {A : Nat}
    (hA : A + 4753 < 2 ^ shapeWidth shape) :
    ∀ instr ∈ closeLcaProgramAt shape A,
      Instr.FieldsFit (shapeWidth shape) instr := by
  intro instr hmem
  have hbs : canonicalBPRelativeSummaryBlockSizeRaw shape <
      2 ^ shapeWidth shape :=
    lt_reviewerWordBits_of_lt_capacity (lt_capacity_of_le_linear (by
      have := blockSizeRaw_le shape; omega))
  have hw74 : (74 : Nat) < 2 ^ shapeWidth shape := by omega
  simp only [closeLcaProgramAt, crossArmTerminated, jumpTo,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with h | (h | (rfl | rfl)) | h
  · exact closeDispatch_fits _ _ _
      (canonicalBPRelativeSummaryBlockSizeRaw_pos shape) hbs (by omega) hw74
      instr h
  · exact closeLcaCrossArm_fits shape (by omega) instr h
  · exact ⟨by simp only [dSame]; omega, by omega⟩
  · exact ⟨by simp only [dSame]; omega, by simp only [closeLcaExit]; omega⟩
  · exact closeLcaSameArm_fits shape (by omega) instr h

end E1CloseLcaWidth
end WordRAM
end RMQ
