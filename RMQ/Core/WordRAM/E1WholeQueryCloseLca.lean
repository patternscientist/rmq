import RMQ.Core.WordRAM.E1WholeQueryLcaLeg
import RMQ.Core.WordRAM.E1InteriorDispatchCompose
import RMQ.Core.WordRAM.E1CloseCompose

/-!
# E1 whole-query glue: the close/LCA leg as ONE REBASABLE PROGRAM, terminated

## Two defects this module repairs, both of them live at its base commit

**(1) The cross arm had no terminator wired.**  `crossArmTerminated` and
`crossArmTerminated_converges` (`E1CloseDispatch.lean:625`/`:649`) existed, but
only against the module's own two-instruction stub `unterminatedCrossArm`.  No
composition applied them to a REAL cross arm.  Without the terminator the cross
arm's exit PC lands exactly on the same-block leg's base and control falls
through into the wrong leg - the defect
`unterminatedCrossArm_falls_through` (`:469`) proves.  Here the terminator is
applied to `crossBlockArmProgramAt` at its canonical interior.

**(2) The close/LCA composition was pinned to base `0`.**
`closeDispatchProgram` (`E1CloseDispatch.lean:~700`) writes its branch target as
`4 + crossArm.length`, which is the same-block arm's ABSOLUTE address only when
the program is hosted at `0`; `sameBlockDispatchProgram_runsTo`
(`E1CloseCompose.lean:95`) accordingly runs from `⟨regs, 0, false⟩`.  In the
whole query the close/LCA leg sits AFTER the guard and both select legs, at a
base that is not `0`, so that composition could not be used at all.  This
module rebases the dispatch the way `sameBlockLegProgramAt` rebased the
same-block leg: every target is computed from the host base `A`.

Both repairs are in one module because they interact: the terminator's target
is an absolute address, so it could not be written correctly until the layout
was parametric in `A`.

## The layout, computed and not asserted

    A                dispatch                         4
    A + 4            cross arm                     4574
    A + 4578         terminator (jumpTo dSame)        2
    A + 4580         same-block leg                 173
    A + 4753         exit - BOTH arms converge here

The cross arm is `370 + interior.length` (`crossBlockArmProgramAt_length`,
`E1CrossBlockArm.lean:809`) with the canonical interior at `4204`
(`canonicalInteriorDispatchBlock_length`,
`E1InteriorDispatchCompose.lean:103`), so `4574`.  Every one of these numbers
is derived by `simp`/`decide` from the component length lemmas below, never
written into a `runsTo` by hand.

## PRESERVATION IS NOW SYMMETRIC ACROSS BOTH ARMS (E1-LaneA3)

BOTH `closeLcaProgramAt_runsTo_same` and `_runsTo_cross` export
`∀ r, CloseLegUntouched r → regsF r = regs r`.

This header previously recorded the opposite, and the correction is worth
keeping visible.  The asymmetry was never a fact about this leg or about
what the cross arm's code writes -- the cross arm's own write set has
always been disjoint from `{0..7} ∪ {28}`.  It was a fact about the
INTERFACE: `crossBlockArmProgramAt_runsTo`'s `hInterior` promised only
`fClose`/`fRight`/`mLV`/`mLP` across the mid-arm interior hole, so the arm
could not promise a caller more than its own hypothesis promised it.
Widening `hInterior` with a fifth conjunct (DD-20260719-160) removed the
hole, and the clause then threaded with no change to any instruction.

Consequently the `hCrossPres` escape hatch this header used to advertise is
no longer needed, and no consumer should reintroduce it as a hypothesis.
-/

namespace RMQ
namespace WordRAM
namespace E1WholeQueryCloseLca

open E1Machine
open E1CloseDispatch
open E1SameBlockLeg
open E1SameBlockArm
open E1InteriorDispatchCompose
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-! ## The three pieces, each at its computed base -/

/-- The real cross-block arm at its host base `A + 4`, carrying the canonical
interior dispatch block.  The interior's own base `A + 4 + 176` is the one
`crossBlockArm_withCanonicalInterior_runsTo` demands. -/
def closeLcaCrossArm (shape : Cartesian.CartesianShape) (A : Nat) :
    List Instr :=
  E1CrossBlockArm.crossBlockArmProgramAt shape
    concreteBPNativeFringeChunkTraceSegment
    (canonicalBPRelativeSummaryBlockSizeRaw shape) (A + 4)
    (canonicalInteriorDispatchBlock shape (A + 4 + 176))

@[simp] theorem closeLcaCrossArm_length (shape : Cartesian.CartesianShape)
    (A : Nat) : (closeLcaCrossArm shape A).length = 4574 := by
  simp [closeLcaCrossArm]

/-- The same-block leg at its host base `A + 4580`, rebased by
`sameBlockLegProgramAt`. -/
def closeLcaSameArm (shape : Cartesian.CartesianShape) (A : Nat) :
    List Instr :=
  sameBlockLegProgramAt shape concreteBPNativeFringeChunkTraceSegment
    (canonicalBPRelativeSummaryBlockSizeRaw shape) (A + 4580)

@[simp] theorem closeLcaSameArm_length (shape : Cartesian.CartesianShape)
    (A : Nat) : (closeLcaSameArm shape A).length = 173 := by
  simp [closeLcaSameArm]

/-- The address both arms converge at. -/
def closeLcaExit (A : Nat) : Nat := A + 4753

/-! ## The composed leg -/

/--
THE CLOSE/LCA LEG, ONE PROGRAM, REBASABLE AND TERMINATED.

The dispatch's branch target and the terminator's jump target are both
computed from `A`, so hosting this at any base is sound.  The cross arm is
suffixed with `jumpTo dSame (closeLcaExit A)`, which is what stops it falling
into the same-block leg.
-/
def closeLcaProgramAt (shape : Cartesian.CartesianShape) (A : Nat) :
    List Instr :=
  closeDispatch (canonicalBPRelativeSummaryBlockSizeRaw shape) (A + 4580) ++
    (crossArmTerminated (closeLcaCrossArm shape A) (closeLcaExit A) ++
      closeLcaSameArm shape A)

@[simp] theorem closeLcaProgramAt_length (shape : Cartesian.CartesianShape)
    (A : Nat) : (closeLcaProgramAt shape A).length = 4753 := by
  simp [closeLcaProgramAt, crossArmTerminated]

/-- The exit is exactly the end of the program: both arms converge at the
first address past the leg.  Stated as an executed equality so a layout drift
stops the build. -/
theorem closeLcaExit_eq_end (shape : Cartesian.CartesianShape) (A : Nat) :
    closeLcaExit A = A + (closeLcaProgramAt shape A).length := by
  simp [closeLcaExit]

/-! ## Hosting: every sub-block's base is forced by the preceding lengths -/

/-- All four hosting facts at once, each offset computed by
`append_left`/`append_right` rather than asserted. -/
theorem closeLcaProgramAt_hosts (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {A : Nat}
    (hHost : HostedAt program A (closeLcaProgramAt shape A)) :
    HostedAt program A
        (closeDispatch (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (A + 4580)) ∧
      HostedAt program (A + 4) (closeLcaCrossArm shape A) ∧
      HostedAt program (A + 4578) (jumpTo dSame (closeLcaExit A)) ∧
      HostedAt program (A + 4580) (closeLcaSameArm shape A) := by
  have hd : HostedAt program A
      (closeDispatch (canonicalBPRelativeSummaryBlockSizeRaw shape)
        (A + 4580)) := hHost.append_left
  have hrest := hHost.append_right
  have hrest' : HostedAt program (A + 4)
      (crossArmTerminated (closeLcaCrossArm shape A) (closeLcaExit A) ++
        closeLcaSameArm shape A) := by
    simpa using hrest
  have hterm : HostedAt program (A + 4)
      (crossArmTerminated (closeLcaCrossArm shape A) (closeLcaExit A)) :=
    hrest'.append_left
  have hcross : HostedAt program (A + 4) (closeLcaCrossArm shape A) := by
    have := hterm.append_left (code₂ := jumpTo dSame (closeLcaExit A))
    simpa [crossArmTerminated] using this
  have hjump : HostedAt program (A + 4578) (jumpTo dSame (closeLcaExit A)) := by
    have := hterm.append_right (code₁ := closeLcaCrossArm shape A)
      (code₂ := jumpTo dSame (closeLcaExit A))
    have harith : A + 4 + (closeLcaCrossArm shape A).length = A + 4578 := by
      simp
    rw [harith] at this
    simpa [crossArmTerminated] using this
  have hsame : HostedAt program (A + 4580) (closeLcaSameArm shape A) := by
    have := hrest'.append_right
    have harith :
        A + 4 +
            (crossArmTerminated (closeLcaCrossArm shape A)
              (closeLcaExit A)).length = A + 4580 := by
      simp [crossArmTerminated]
    rw [harith] at this
    exact this
  exact ⟨hd, hcross, hjump, hsame⟩

/-! ## The two arms, executed -/

/--
SAME-BLOCK ARM, END TO END, at an arbitrary host base.

The branch is taken, the whole terminated cross arm is stepped over, and the
same-block leg runs at `A + 4580`.  The receipt is the route's same-block arm
object and the value lands in `fRes`.  `CloseLegUntouched` survives, because
both the dispatch and the same-block leg export it.
-/
theorem closeLcaProgramAt_runsTo_same (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {A leftClose rightClose : Nat}
    (hHost : HostedAt program A (closeLcaProgramAt shape A))
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, A, false⟩ ⟨regsF, closeLcaExit A, false⟩
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
          rightClose).trace
        (closeDispatchCats ++
          sameBlockLegCats shape concreteBPNativeFringeChunkTraceSegment
            (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
            rightClose) ∧
      some (regsF fRes) =
        (SuccinctClose.ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose
          rightClose).value ∧
      (∀ r, CloseLegUntouched r → regsF r = regs r) := by
  obtain ⟨hd, _hcross, _hjump, hsameArm⟩ := closeLcaProgramAt_hosts shape hHost
  obtain ⟨regs', hrunD, hcl', hri', hpresD⟩ :=
    closeDispatch_runsTo_same (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hd regs leftClose rightClose hClose hRight hsame
  obtain ⟨regsF, hrunL, hval, hpresL⟩ :=
    sameBlockLegProgramAt_runsTo_canonical shape hsameArm regs' hcl' hri'
  refine ⟨regsF, ?_, hval, ?_⟩
  · have htrans := hrunD.trans hrunL
    have hpc : A + 4580 + 173 = closeLcaExit A := by
      simp [closeLcaExit]
    rw [hpc] at htrans
    exact htrans
  · intro r hr
    rw [hpresL r hr, hpresD r (by
      refine ⟨?_, ?_, ?_⟩ <;>
        rcases hr with h | h <;> omega)]

/--
CROSS-BLOCK ARM, END TO END, at an arbitrary host base — WITH THE TERMINATOR
DOING ITS JOB.

The branch is not taken, the cross arm runs at `A + 4`, and the appended
`jumpTo` carries control PAST the same-block leg to the shared exit.  Without
the terminator the arm would end at `A + 4578` and fall into the same-block
leg's code; the exit PC here is `closeLcaExit A = A + 4753`, which is the
same-block arm's END, so the two arms converge instead of one running the
other.

PRESERVATION IS NOW SYMMETRIC WITH THE SAME-BLOCK TWIN (E1-LaneA3,
DD-20260719-161).  This arm exports the same `CloseLegUntouched` clause,
because `crossBlockArmProgramAt_runsTo` now does.  The three links are the
dispatch prefix (`CloseDispatchUntouched`, `≠72 ≠73 ≠74`), the arm itself,
and the terminator's `dSame` write (`74`) -- all outside the band.

This is what the module header previously recorded as impossible; the
asymmetry was never a fact about this leg, only about the arm's interface.
-/
theorem closeLcaProgramAt_runsTo_cross (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {A leftClose rightClose : Nat}
    (hHost : HostedAt program A (closeLcaProgramAt shape A))
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
          rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, A, false⟩ ⟨regsF, closeLcaExit A, false⟩
        (E1CrossBlockArm.crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨dispatchRouteValue shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1),
            dispatchEvents shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1)⟩
          leftClose rightClose).trace
        (closeDispatchCats ++
          (E1CrossBlockArm.crossBlockArmCats shape
            concreteBPNativeFringeChunkTraceSegment
            (canonicalBPRelativeSummaryBlockSizeRaw shape)
            (dispatchCats shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
            (dispatchRouteValue shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
            leftClose rightClose ++
            [Category.registerWrite, Category.branch])) ∧
      some (regsF fRes) =
        (E1CrossBlockArm.crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨dispatchRouteValue shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1),
            dispatchEvents shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1)⟩
          leftClose rightClose).value ∧
      (∀ r, CloseLegUntouched r → regsF r = regs r) := by
  obtain ⟨hd, hcrossArm, hjump, _hsameArm⟩ :=
    closeLcaProgramAt_hosts shape hHost
  obtain ⟨regs', hrunD, hcl', hri', hpresD⟩ :=
    closeDispatch_runsTo_cross (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hd regs leftClose rightClose hClose hRight hcross
  obtain ⟨regsA, hrunA, hval, hpresA⟩ :=
    crossBlockArm_withCanonicalInterior_runsTo shape
      (A := A + 4) hcrossArm regs' hcl' hri'
  -- the arm ends at `A + 4 + 370 + 4204 = A + 4578`, the terminator's base
  have hArmPc : A + 4 + 370 +
      (canonicalInteriorDispatchBlock shape (A + 4 + 176)).length =
        A + 4578 := by simp
  rw [hArmPc] at hrunA
  have hjrun :=
    jumpTo_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (A := A + 4578) hjump regsA
  refine ⟨regsA.write dSame 1, ?_, ?_, ?_⟩
  · have htrans := (hrunD.trans hrunA).trans hjrun
    simpa [List.append_assoc] using htrans
  · rw [RegFile.write_other _ _ (by decide : fRes ≠ dSame)]
    exact hval
  · -- band survives: terminator writes `dSame` (74), arm preserves the band,
    -- dispatch prefix touches only `72..74`
    intro r hr
    have hr' : r ≤ 7 ∨ r = 28 := hr
    have hne : r ≠ dSame := by show r ≠ 74; omega
    rw [RegFile.write_other _ _ hne, hpresA r hr,
      hpresD r (by refine ⟨?_, ?_, ?_⟩ <;> omega)]

end E1WholeQueryCloseLca
end WordRAM
end RMQ
