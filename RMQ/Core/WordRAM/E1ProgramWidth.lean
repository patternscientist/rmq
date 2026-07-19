import RMQ.Core.WordRAM.E1CandMerge3

/-!
# E1 amended machine: WHOLE-PROGRAM width certificates (M3d-7)

Matrix row REQ-E1-02 asks for constructor-exhaustive width accounting on
the instructions the machine actually executes.  Every SEGMENT of the
same-block leg has carried its own certificate since M3d-6
(`windowAddr_fits`, `rankSeedPos_fits`, `rankCloseBlock_fits`,
`rankSeedFinish_fits`, `windowRange_fits`, `fringeArmPrologue_fits`,
`fringeLoopBody_fits`, `fringeCandGlobal_fits`, `sameBlockClose_fits`,
`closeDispatch_fits`), but no certificate ranged over a WHOLE PROGRAM.
This module closes that gap for `sameBlockLegProgramAt` and
`sameBlockDispatchProgram`, and for the new `candMerge3` block.

This is assembly, not new mathematics: the content is collecting the
segments' hypotheses into one signature and dispatching `List.mem_append`
(with `or_assoc` in the simp set, per the M3d-3 flattening gotcha).  What
it buys is that the certificate now quantifies over the program a run
actually fetches from, so a segment omitted from the layout cannot escape
the accounting.

The single `B`-dependent hypothesis `B + 171 < 2 ^ w` is what forces the
four rebased internal addresses to fit: `rankCloseBlock` at `B + 5`
(needing `B + 65`), the fold body at `B + 97` (needing `B + 164`), and
`fringeCandGlobal` at `B + 164` (needing `B + 171`).
-/

namespace RMQ
namespace WordRAM
namespace E1ProgramWidth

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open E1RankBlock
open E1SameBlockArm
open E1SameBlockLeg
open E1CloseDispatch
open E1CloseCompose
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-! ## The same-block leg -/

/--
CONSTRUCTOR-EXHAUSTIVE WIDTH CERTIFICATE FOR THE WHOLE SAME-BLOCK LEG.

Every one of the 173 instructions of `sameBlockLegProgramAt` satisfies
`Instr.FieldsFit w`.  The predicate is `Instr.FieldsFit`
(`E1Machine.lean:503`), which has one arm per constructor and no wildcard
arm returning `True`; each segment lemma discharges its own constructors'
field conjunctions, and `divConst`'s positivity arm is discharged from the
route facts rather than assumed.
-/
theorem sameBlockLegProgramAt_fits
    (shape : Cartesian.CartesianShape)
    {w fringeSegment blockSize B : Nat}
    (hreg : 74 < 2 ^ w)
    (hseg : fringeSegment < 2 ^ w)
    (hbspos : 0 < blockSize) (hbs : blockSize < 2 ^ w)
    (hcpos : 0 < sbChunkBits shape)
    (hcL : sbChunkBits shape ≤
      SuccinctRank.machineWordBits shape.bpCode.length)
    (hLpos : 0 < SuccinctRank.machineWordBits shape.bpCode.length)
    (hLw : SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w)
    (hcode : shape.bpCode.length < 2 ^ w)
    (hpowL : 2 ^ SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w)
    (hmix : (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) < 2 ^ w)
    (hG : concreteBPNativeRankCloseTraceSegmentBase + 4 < 2 ^ w)
    (hWSpos : 0 < (builtRelativeSplitBPCloseRankData shape).wordSize)
    (hWS : (builtRelativeSplitBPCloseRankData shape).wordSize < 2 ^ w)
    (hBPSpos : 0 < (builtRelativeSplitBPCloseRankData shape).blocksPerSuper)
    (hBPS : (builtRelativeSplitBPCloseRankData shape).blocksPerSuper < 2 ^ w)
    (hB : B + 171 < 2 ^ w) :
    ∀ instr ∈ sameBlockLegProgramAt shape fringeSegment blockSize B,
      Instr.FieldsFit w instr := by
  -- derived side facts
  have hlin : 2 * sbChunkBits shape + 2 < 2 ^ w := by
    have hle : 2 * sbChunkBits shape + 2 ≤
        (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hpowc : 2 ^ sbChunkBits shape < 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hcL
    omega
  have hcw : sbChunkBits shape < 2 ^ w := by omega
  -- the fold body, whose four segments the leg lists separately
  have hbody : ∀ instr ∈ fringeLoopBody fringeSegment (sbChunkBits shape)
      (SuccinctRank.machineWordBits shape.bpCode.length) (B + 97),
      Instr.FieldsFit w instr :=
    fringeLoopBody_fits (by omega) hseg hcpos hcL hpowL hmix (by omega)
  intro instr hinstr
  simp only [sameBlockLegProgramAt, List.mem_append, List.mem_singleton,
    or_assoc] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact windowAddr_fits w blockSize _ (by omega) hbspos hbs hLpos hLw
      instr h
  · exact rankSeedPos_fits w (by omega) instr h
  · exact rankCloseBlock_fits (w := w) (B := B + 5)
      (G := concreteBPNativeRankCloseTraceSegmentBase)
      (c := sbChunkBits shape) (L := shape.bpCode.length)
      (WS := (builtRelativeSplitBPCloseRankData shape).wordSize)
      (BPS := (builtRelativeSplitBPCloseRankData shape).blocksPerSuper)
      (by omega) hG hcode hcpos hWSpos hWS hBPSpos hBPS hpowc hlin
      (by omega) instr h
  · exact rankSeedFinish_fits w (by omega) instr h
  · exact windowRange_fits w (by omega) instr h
  · exact fringeArmPrologue_fits (by omega) hcpos hcw instr h
  · exact hbody instr (List.mem_append.mpr (Or.inl h))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h))))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inl h))))))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inr h))))))
  · -- the fold back edge
    subst h
    refine ⟨?_, by omega⟩
    show (52 : Nat) < 2 ^ w
    omega
  · exact fringeCandGlobal_fits w (B + 164) (by omega) (by omega) instr h
  · exact sameBlockClose_fits w (by omega) instr h

/-! ## The dispatch composite -/

/--
CONSTRUCTOR-EXHAUSTIVE WIDTH CERTIFICATE FOR THE WHOLE DISPATCH
COMPOSITE.

`sameBlockDispatchProgram` is the four-instruction dispatch, then the
cross arm, then the same-block leg hosted at `4 + crossArm.length`.  The
cross arm is a parameter, so its instructions are carried as a hypothesis
-- this is what lets the certificate be stated before the cross-block arm
is assembled, and what will force the cross arm to be certified when it
is.
-/
theorem sameBlockDispatchProgram_fits
    (shape : Cartesian.CartesianShape)
    {w fringeSegment blockSize : Nat} {crossArm : List Instr}
    (hreg : 74 < 2 ^ w)
    (hseg : fringeSegment < 2 ^ w)
    (hbspos : 0 < blockSize) (hbs : blockSize < 2 ^ w)
    (hcpos : 0 < sbChunkBits shape)
    (hcL : sbChunkBits shape ≤
      SuccinctRank.machineWordBits shape.bpCode.length)
    (hLpos : 0 < SuccinctRank.machineWordBits shape.bpCode.length)
    (hLw : SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w)
    (hcode : shape.bpCode.length < 2 ^ w)
    (hpowL : 2 ^ SuccinctRank.machineWordBits shape.bpCode.length < 2 ^ w)
    (hmix : (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) < 2 ^ w)
    (hG : concreteBPNativeRankCloseTraceSegmentBase + 4 < 2 ^ w)
    (hWSpos : 0 < (builtRelativeSplitBPCloseRankData shape).wordSize)
    (hWS : (builtRelativeSplitBPCloseRankData shape).wordSize < 2 ^ w)
    (hBPSpos : 0 < (builtRelativeSplitBPCloseRankData shape).blocksPerSuper)
    (hBPS : (builtRelativeSplitBPCloseRankData shape).blocksPerSuper < 2 ^ w)
    (hcross : ∀ instr ∈ crossArm, Instr.FieldsFit w instr)
    (hlen : 4 + crossArm.length + 171 < 2 ^ w) :
    ∀ instr ∈ sameBlockDispatchProgram shape fringeSegment blockSize
      crossArm, Instr.FieldsFit w instr := by
  have hleg := sameBlockLegProgramAt_fits shape (B := 4 + crossArm.length)
    hreg hseg hbspos hbs hcpos hcL hLpos hLw hcode hpowL hmix hG hWSpos
    hWS hBPSpos hBPS hlen
  intro instr hinstr
  simp only [sameBlockDispatchProgram, closeDispatchProgram,
    List.mem_append] at hinstr
  rcases hinstr with h | h | h
  · exact closeDispatch_fits w blockSize (4 + crossArm.length) hbspos hbs
      (by omega) (by omega) instr h
  · exact hcross instr h
  · exact hleg instr h

/-! ## The three-way merge block

Restated at the whole-block level for uniformity with the two above; the
block's own certificate is `E1CandMerge3.candMerge3_fits`. -/

/-- The merge block's width certificate, in the whole-program idiom. -/
theorem candMerge3Program_fits {w E : Nat}
    (hreg : 84 < 2 ^ w) (hE : E + 14 < 2 ^ w) :
    ∀ instr ∈ E1CandMerge3.candMerge3 E, Instr.FieldsFit w instr :=
  E1CandMerge3.candMerge3_fits w E hE hreg

end E1ProgramWidth
end WordRAM
end RMQ
