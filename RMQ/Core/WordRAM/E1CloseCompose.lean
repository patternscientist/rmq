import RMQ.Core.WordRAM.E1CloseDispatch

/-!
# E1 amended machine: DISPATCH ∘ SAME-BLOCK LEG (M3d-6)

`E1CloseDispatch` encodes the route's top-level `if`; `E1SameBlockLeg`
simulates the route's `then` branch.  This module puts them in ONE
program and runs the composite end to end on the same-block case.

## What had to be built first

`sameBlockLegProgram` (`E1SameBlockLeg.lean:447`) is a witness only at
base `0`: four of its internal addresses -- the `rankCloseBlock` segment
base `5`, `fringeMerge 97`, the `brNZ fCnt 97` fold back edge, and
`fringeCandGlobal 164` -- are ABSOLUTE.  Behind a four-instruction
dispatch the leg no longer starts at `0`, so those addresses are wrong by
exactly the host base.  `sameBlockLegProgramAt B`
(`E1SameBlockLeg.lean`, M3d-6 section) rebases all four; the simulation
theorem `sameBlockLeg_runsTo_canonical` needed no change, having already
been stated with hypotheses at `A + k`.

## The composite

    0                     closeDispatch blockSize (4 + crossArm.length)
    4                     crossArm                    (fall-through)
    4 + crossArm.length   sameBlockLegProgramAt ... (4 + crossArm.length)

The same-block target is COMPUTED from the cross arm's length, never
asserted, and the leg's internal targets are computed from that same
address.  An off-by-one in either makes this module fail to typecheck.

`crossArm` stays a parameter because the cross-block arm is not finished
(its interior leg is blocked -- M3d-3 section 2).  Nothing here depends on
the cross arm's contents, only on its LENGTH, so the finished cross arm
drops into this same layout without disturbing the same-block result.

## Scope, stated honestly

This composes ONE of the route's two branches with the dispatch that
selects it.  It is NOT a whole-query simulation and discharges no matrix
row; every row REQ-E1-01..11 is whole-query scoped and remains OPEN.
-/

namespace RMQ
namespace WordRAM
namespace E1CloseCompose

open E1Machine
open E1CloseDispatch
open E1SameBlockLeg
open E1FringeFoldBlock
open E1FringeArmBlock
open E1SameBlockArm
open E1RankBlock
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-- The dispatch hosting the rebased same-block leg as its taken-branch
arm.  The leg is rebased to the address the layout puts it at, so the
argument to `sameBlockLegProgramAt` and the branch target computed by
`closeDispatchProgram` are the SAME expression. -/
def sameBlockDispatchProgram (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize : Nat) (crossArm : List Instr) : List Instr :=
  closeDispatchProgram blockSize crossArm
    (sameBlockLegProgramAt shape fringeSegment blockSize
      (4 + crossArm.length))

@[simp] theorem sameBlockDispatchProgram_length
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize : Nat) (crossArm : List Instr) :
    (sameBlockDispatchProgram shape fringeSegment blockSize crossArm).length =
      4 + crossArm.length + 173 := by
  simp [sameBlockDispatchProgram]

/-- Category log of the composite same-block path: the dispatch's four
ticks followed by the leg's. -/
def sameBlockDispatchCats (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose rightClose : Nat) : List Category :=
  closeDispatchCats ++
    sameBlockLegCats shape fringeSegment blockSize leftClose rightClose

/--
THE DISPATCH COMPOSED WITH THE SAME-BLOCK LEG.

On the route's OWN same-block condition, the composite program runs from
`0` to `4 + crossArm.length + 173` reproducing the route's same-block
trace and value.  The branch is taken, the cross arm is stepped over, and
the leg executes at its nonzero host base.

The `blockSize` scrutinised by the dispatch and the `blockSize` the leg
computes with are the SAME variable, so there is no machine-side notion of
"same block" that could drift from the route's.
-/
theorem sameBlockDispatchProgram_runsTo
    (shape : Cartesian.CartesianShape)
    {fringeSegment blockSize leftClose rightClose : Nat}
    {crossArm : List Instr}
    (hc : sbChunkBits shape ≤ SuccinctRank.machineWordBits shape.bpCode.length)
    (h0 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h1 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h2 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hsame : blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (sameBlockDispatchProgram shape fringeSegment blockSize crossArm)
          ⟨regs, 0, false⟩
          ⟨regsF, 4 + crossArm.length + 173, false⟩
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).trace
        (sameBlockDispatchCats shape fringeSegment blockSize leftClose
          rightClose) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).value := by
  obtain ⟨hD, -, hLeg⟩ :=
    closeDispatchProgram_hosts blockSize crossArm
      (sameBlockLegProgramAt shape fringeSegment blockSize
        (4 + crossArm.length))
  obtain ⟨regs', hrunD, hcl', hri', -⟩ :=
    closeDispatch_runsTo_same (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hD regs leftClose rightClose hClose hRight hsame
  obtain ⟨regsF, hrunL, hval⟩ :=
    sameBlockLegProgramAt_runsTo_canonical shape hLeg hc h0 h1 h2 regs'
      hcl' hri'
  refine ⟨regsF, ?_, hval⟩
  have htrans := hrunD.trans hrunL
  simpa [sameBlockDispatchProgram, sameBlockDispatchCats] using htrans

/-! ## ANTI-VACUITY: the leg really does run off base zero

The theorem above is parametric in `crossArm`, and a reader is entitled to
ask whether the "nonzero base" is ever actually nonzero.  Instantiating
`crossArm` at the dispatch module's own two-instruction witness pins the
leg's host base to `6` and its exit to `179`, both CONCRETE numerals.

This is the specific defect the M3d-6 delegation named: at base `0` the
old layout typechecks by accident, because `0 + 97 = 97`.  At base `6` the
internal targets are `103` and `170`, and nothing would typecheck if
`sameBlockLegProgramAt` had left them absolute.
-/

/-- The composite with the dispatch module's witness cross arm: the leg is
hosted at `6`, not `0`, and the run ends at `179`. -/
theorem sameBlockDispatchProgram_runsTo_witnessCross
    (shape : Cartesian.CartesianShape)
    {fringeSegment blockSize leftClose rightClose : Nat}
    (hc : sbChunkBits shape ≤ SuccinctRank.machineWordBits shape.bpCode.length)
    (h0 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h1 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (h2 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hsame : blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (sameBlockDispatchProgram shape fringeSegment blockSize
            witnessCrossArm)
          ⟨regs, 0, false⟩ ⟨regsF, 179, false⟩
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).trace
        (sameBlockDispatchCats shape fringeSegment blockSize leftClose
          rightClose) ∧
      some (regsF fRes) =
        (bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          blockSize leftClose rightClose).value := by
  have h :=
    sameBlockDispatchProgram_runsTo shape (fringeSegment := fringeSegment)
      (crossArm := witnessCrossArm) hc h0 h1 h2 regs hClose hRight hsame
  simpa [witnessCrossArm] using h

/-- The leg's host base under the witness cross arm is `6`, and its
internal fold back edge therefore targets `103`.  Stated as an executable
equality so the layout arithmetic is CHECKED rather than described in a
comment. -/
theorem witnessCross_legBase_eq_six :
    4 + witnessCrossArm.length = 6 := by decide

end E1CloseCompose
end WordRAM
end RMQ
