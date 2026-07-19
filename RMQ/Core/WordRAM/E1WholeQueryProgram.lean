import RMQ.Core.WordRAM.E1WholeQueryCloseLca
import RMQ.Core.WordRAM.E1SelectCanonical
import RMQ.Core.WordRAM.E1WholeQueryPublic

/-!
# E1 amended machine: THE WHOLE-QUERY PROGRAM

## What did not exist before this module

No definition anywhere composed the query's legs into one runnable program.
`programSkeleton` (`E1QueryProgram.lean:136`) took `validPath` as a
PARAMETER; `WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) named the
agreement the glue owes; every leg had its own `runsTo`.  Nothing joined them.
This module supplies the `validPath`.

## The layout, at the skeleton's own valid-path base `8`

    8      selectLeftSetup      1     xIdx := regLeft
    9      select leg         405     left select, answer packet in rVal
    414    selectMidGlue        2     stash left packet; xIdx := regRight - 1
    416    select leg         405     right select, answer packet in rVal
    821    selectJoin           6     miss dispatch + packet decode into
                                      fClose / fRight
    827    close/LCA leg     4753     `closeLcaProgramAt`, both arms
    5580   ...

Everything up to `5580` is defined and hosted here.  What is EXECUTED here is
`8 .. 821` — see the honest scope note at the end.

## The register plumbing, and which registers are actually dead

The guard's accepting exit (`guardAcceptRegs`, `E1QueryProgram.lean:591`)
leaves `regLeft = left`, `regRight = right`, `regZero = 0`, `regN = n`,
`regT1 = 1`, `regT2 = 1`, `regG = 0`.  The select leg preserves exactly
`r ≤ 7 ∨ r = 28` (`selectCloseBlock_runsTo_canonical`,
`E1SelectCanonical.lean:212`), so anything stashed below `8` survives a select.

**Which of `0..7` are dead after the guard, worked out rather than inherited.**
An earlier coordinator note said "only `5,6,7` are dead". That is
UNDER-COUNTED. Reading `guardBlock` (`E1QueryProgram.lean:110`), `regZero` (3)
is read only by the two `natEq regG _ regZero` instructions and `regN` (4)
only by `natLe regT2 regRight regN` — all three inside the guard block, all
executed before pc `8`. Nothing in the valid path reads either. So the dead
set after the guard is **`{3,4,5,6,7}`, five registers, not three**. Live
across the valid path are only `regLeft` (0, until the left select's setup),
`regRight` (1, until the right select's setup) and `regOut` (2, written last).

This module uses two of them and exploits a third fact:

* `regT1` (5) carries the LEFT select's answer packet across the right select;
* `regT2` (6) is **already `1`** on the accepting path, so the `right - 1` the
  route's second select needs is one `sub` with no constant load. That is not
  a trick — `guardAcceptRegs` pins it, and `guardAcceptRegs_operands`
  (`:710`) is the theorem that says so.

`xIdx` (28) is the select's INPUT and is preserved across a select, so it is
not available as a stash slot; it is rewritten before each leg.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open E1SelectDispatch
open E1SelectBridge
open E1RankBlock
open E1SameBlockArm
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-! ## The select leg at the canonical instantiation

`selData` is `private` in `E1SelectCanonical`, so the accepted select data is
spelled out here exactly as that module spells it.  Writing it any other way
would produce a block whose hosting hypothesis
`selectCloseBlock_runsTo_canonical` cannot discharge.
-/

/-- The accepted select-close data at a shape. -/
def wholeQuerySelData (shape : Cartesian.CartesianShape) :
    GenericSelect.SparseExceptionSelectData shape.bpCode false
      (GenericSelect.sparseExceptionEffectiveFlagRankSuperOverhead
        shape.bpCode false)
      (GenericSelect.sparseExceptionEffectiveFlagRankBlockOverhead
        shape.bpCode false) :=
  GenericSelect.sparseExceptionSelectData shape.bpCode false

/-- One select-close leg, hosted at base `A`. -/
def wholeQuerySelectLeg (shape : Cartesian.CartesianShape) (A : Nat) :
    List Instr :=
  selectCloseBlockAt (wholeQuerySelData shape)
    concreteBPNativeSelectCloseTraceSegmentLayout A
    concreteBPNativeRankCloseTraceSegmentBase
    concreteBPNativeSelectChunkTraceSegment
    (bpFringeChunkBits shape.bpCode.length)

@[simp] theorem wholeQuerySelectLeg_length (shape : Cartesian.CartesianShape)
    (A : Nat) : (wholeQuerySelectLeg shape A).length = 405 := by
  simp [wholeQuerySelectLeg, selectCloseBlockAt]

/-! ## The three glue blocks -/

/-- Set the select input to the query's LEFT endpoint. -/
def selectLeftSetup : List Instr := [ .move xIdx regLeft ]

@[simp] theorem selectLeftSetup_length : selectLeftSetup.length = 1 := rfl

/-- Stash the left select's answer PACKET in `regT1`, then set the select
input to `regRight - 1`, which is the index the route's second select uses.
`regT2` already holds `1` on the accepting path, so no constant load is
needed. -/
def selectMidGlue : List Instr :=
  [ .move regT1 rVal
  , .sub xIdx regRight regT2 ]

@[simp] theorem selectMidGlue_length : selectMidGlue.length = 2 := rfl

/--
The select join: dispatch on whether either select MISSED, and on the
both-hit path decode the two answer packets into the close registers.

The two `natEq`/`brNZ` pairs are the machine's counterpart of the route's
first two `Option` scrutinees (`E1RouteDecomposition.lean:223`).  The two
`sub`s undo `decodePacket`'s option shift: a packet `c + 1` decodes to close
`c`, and `regT2` is the pinned `1`.
-/
def selectJoin (noneExit : Nat) : List Instr :=
  [ .natEq regG regT1 regZero
  , .brNZ regG noneExit
  , .natEq regG rVal regZero
  , .brNZ regG noneExit
  , .sub fClose regT1 regT2
  , .sub fRight rVal regT2 ]

@[simp] theorem selectJoin_length (noneExit : Nat) :
    (selectJoin noneExit).length = 6 := rfl

/-! ## The composed valid path -/

/-- The select PREFIX of the valid path: setup, left leg, glue, right leg.
Hosted at the skeleton's valid-path base `8`, it occupies `8 .. 821`. -/
def wholeQuerySelectPrefix (shape : Cartesian.CartesianShape) : List Instr :=
  selectLeftSetup ++
    (wholeQuerySelectLeg shape 9 ++
      (selectMidGlue ++ wholeQuerySelectLeg shape 416))

@[simp] theorem wholeQuerySelectPrefix_length
    (shape : Cartesian.CartesianShape) :
    (wholeQuerySelectPrefix shape).length = 813 := by
  simp [wholeQuerySelectPrefix]

/-- The valid path through the close/LCA leg: the select prefix, the join,
and the terminated close/LCA leg at its computed base `827`. -/
def wholeQueryValidPathThroughLca (shape : Cartesian.CartesianShape)
    (noneExit : Nat) : List Instr :=
  wholeQuerySelectPrefix shape ++
    (selectJoin noneExit ++ E1WholeQueryCloseLca.closeLcaProgramAt shape 827)

@[simp] theorem wholeQueryValidPathThroughLca_length
    (shape : Cartesian.CartesianShape) (noneExit : Nat) :
    (wholeQueryValidPathThroughLca shape noneExit).length = 5572 := by
  simp [wholeQueryValidPathThroughLca]

/-- The close/LCA leg's host base is `8 + 813 + 6 = 827`, which is the base
the definition passes to `closeLcaProgramAt`.  Stated as an executed equality
so that a change to any earlier stage's length breaks the build instead of
silently mis-basing the leg's internal branch targets. -/
theorem closeLca_base_is_827 (shape : Cartesian.CartesianShape)
    (noneExit : Nat) :
    8 + (wholeQuerySelectPrefix shape).length +
        (selectJoin noneExit).length = 827 := by
  simp

/-! ## Hosting inside the skeleton -/

/-- The skeleton hosts each select-prefix stage at the base the layout
computes for it.  Every offset comes from `append_left`/`append_right`, so an
off-by-one anywhere in the chain fails to typecheck. -/
theorem wholeQuerySelectPrefix_hosts (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program}
    (hHost : HostedAt program 8 (wholeQuerySelectPrefix shape)) :
    HostedAt program 8 selectLeftSetup ∧
      HostedAt program 9 (wholeQuerySelectLeg shape 9) ∧
      HostedAt program 414 selectMidGlue ∧
      HostedAt program 416 (wholeQuerySelectLeg shape 416) := by
  have h1 : HostedAt program 8 selectLeftSetup := hHost.append_left
  have hrest := hHost.append_right (code₁ := selectLeftSetup)
  have hrest' : HostedAt program 9
      (wholeQuerySelectLeg shape 9 ++
        (selectMidGlue ++ wholeQuerySelectLeg shape 416)) := by
    simpa using hrest
  have h2 : HostedAt program 9 (wholeQuerySelectLeg shape 9) :=
    hrest'.append_left
  have hrest2 := hrest'.append_right (code₁ := wholeQuerySelectLeg shape 9)
  have hrest2' : HostedAt program 414
      (selectMidGlue ++ wholeQuerySelectLeg shape 416) := by
    simpa using hrest2
  have h3 : HostedAt program 414 selectMidGlue := hrest2'.append_left
  have h4 : HostedAt program 416 (wholeQuerySelectLeg shape 416) := by
    have := hrest2'.append_right (code₁ := selectMidGlue)
    simpa using this
  exact ⟨h1, h2, h3, h4⟩

/-- The valid path hosts the close/LCA leg at `827`. -/
theorem wholeQueryValidPathThroughLca_hosts_closeLca
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {noneExit : Nat}
    (hHost : HostedAt program 8 (wholeQueryValidPathThroughLca shape noneExit)) :
    HostedAt program 8 (wholeQuerySelectPrefix shape) ∧
      HostedAt program 821 (selectJoin noneExit) ∧
      HostedAt program 827
        (E1WholeQueryCloseLca.closeLcaProgramAt shape 827) := by
  have h1 : HostedAt program 8 (wholeQuerySelectPrefix shape) :=
    hHost.append_left
  have hrest := hHost.append_right (code₁ := wholeQuerySelectPrefix shape)
  have hrest' : HostedAt program 821
      (selectJoin noneExit ++
        E1WholeQueryCloseLca.closeLcaProgramAt shape 827) := by
    simpa using hrest
  have h2 : HostedAt program 821 (selectJoin noneExit) := hrest'.append_left
  have h3 : HostedAt program 827
      (E1WholeQueryCloseLca.closeLcaProgramAt shape 827) := by
    have := hrest'.append_right (code₁ := selectJoin noneExit)
    simpa using this
  exact ⟨h1, h2, h3⟩

/-! ## THE SELECT PREFIX, EXECUTED

The guard's accepting fall-through composed with both select legs, on the
CONCRETE skeleton, at every shape and every valid range.  No sampling, no
readiness guard, no size threshold.
-/

/--
BOTH SELECT LEGS RUN, AND THEIR RECEIPT IS THE ROUTE'S.

From the query start state, on any valid range, the skeleton hosting this
valid path runs from the guard through both select legs to pc `821`, emitting
POSITIONALLY the concatenation of the two select legs' route traces at `left`
and `right - 1` — which is exactly `wholeQueryBranchTrace` on both of the
route's select-miss branches (`E1WholeQueryObjects.lean:169`).

The two answer packets are left where the join reads them: the LEFT one in
`regT1`, the RIGHT one in `rVal`, both under `decodePacket`.

`hn` is the skeleton's size constant premise, discharged by the caller from
`ValidRange`; it is not decorative — without it the guard rejects.
-/
theorem wholeQuerySelectPrefix_runsTo (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {n left right : Nat}
    (hguard : HostedAt program 0 (guardBlock n (8 + (813 : Nat))))
    (hprefix : HostedAt program 8 (wholeQuerySelectPrefix shape))
    (hlt : left < right) (hbound : right ≤ n) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          (initialState left right) ⟨regsF, 821, false⟩
        ((concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape
            (right - 1)).trace)
        (guardAcceptCats ++
          ([Category.registerWrite] ++
            (selectCloseCats (wholeQuerySelData shape)
              concreteBPNativeSelectCloseTraceSegmentLayout
              concreteBPNativeRankCloseTraceSegmentBase
              concreteBPNativeSelectChunkTraceSegment
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (bpFringeChunkBits shape.bpCode.length) left ++
              ([Category.registerWrite, Category.arithmetic] ++
                selectCloseCats (wholeQuerySelData shape)
                  concreteBPNativeSelectCloseTraceSegmentLayout
                  concreteBPNativeRankCloseTraceSegmentBase
                  concreteBPNativeSelectChunkTraceSegment
                  (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                  (bpFringeChunkBits shape.bpCode.length) (right - 1))))) ∧
      decodePacket (regsF regT1) =
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value ∧
      decodePacket (regsF rVal) =
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).value := by
  obtain ⟨hsetup, hleg1, hmid, hleg2⟩ := wholeQuerySelectPrefix_hosts shape hprefix
  -- the guard accepts and falls through to pc 8
  have hg := guard_accept_of_valid
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) hguard hlt hbound
  -- pc 8: xIdx := regLeft
  have hf8 : program[8]? = some (.move xIdx regLeft) := hsetup.head
  have hs8 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨guardAcceptRegs n left right, 8, false⟩
      ⟨(guardAcceptRegs n left right).write xIdx
        (guardAcceptRegs n left right regLeft), 9, false⟩
      [] [Category.registerWrite] :=
    RunsTo.move (s := ⟨guardAcceptRegs n left right, 8, false⟩) rfl hf8
  have hleftVal : (guardAcceptRegs n left right) regLeft = left :=
    (guardAcceptRegs_operands n left right).1
  rw [hleftVal] at hs8
  -- the LEFT select leg
  obtain ⟨regs1, hrun1, hval1, hpres1⟩ :=
    E1SelectCanonical.selectCloseBlock_runsTo_canonical shape (A := 9) hleg1
      ((guardAcceptRegs n left right).write xIdx left) left
      (by simp [RegFile.write])
  -- pc 414: stash the left packet, set xIdx := regRight - 1
  have hf414 : program[414]? = some (.move regT1 rVal) := hmid.head
  have hf415 : program[415]? = some (.sub xIdx regRight regT2) :=
    (hmid.tail).head
  have hs414 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regs1, 414, false⟩ ⟨regs1.write regT1 (regs1 rVal), 415, false⟩
      [] [Category.registerWrite] :=
    RunsTo.move (s := ⟨regs1, 414, false⟩) rfl hf414
  have hs415 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regs1.write regT1 (regs1 rVal), 415, false⟩
      ⟨(regs1.write regT1 (regs1 rVal)).write xIdx
        ((regs1.write regT1 (regs1 rVal)) regRight -
          (regs1.write regT1 (regs1 rVal)) regT2), 416, false⟩
      [] [Category.arithmetic] :=
    RunsTo.sub (s := ⟨regs1.write regT1 (regs1 rVal), 415, false⟩) rfl hf415
  -- `regRight` and `regT2` both survive the left select (`r ≤ 7`)
  have hRightSurv : regs1 regRight = right := by
    rw [hpres1 regRight (by decide)]
    simp [RegFile.write, regRight, xIdx]
    exact (guardAcceptRegs_operands n left right).2.1
  have hOneSurv : regs1 regT2 = 1 := by
    rw [hpres1 regT2 (by decide)]
    simp [RegFile.write, regT2, xIdx, guardAcceptRegs, initialRegs,
      regLeft, regRight, regZero, regN, regT1, regG]
  have hIdx2 : ((regs1.write regT1 (regs1 rVal)).write xIdx
      ((regs1.write regT1 (regs1 rVal)) regRight -
        (regs1.write regT1 (regs1 rVal)) regT2)) xIdx = right - 1 := by
    simp [RegFile.write, regT1, xIdx, regRight, regT2] at *
    rw [hRightSurv, hOneSurv]
  -- the RIGHT select leg
  obtain ⟨regs2, hrun2, hval2, hpres2⟩ :=
    E1SelectCanonical.selectCloseBlock_runsTo_canonical shape (A := 416) hleg2
      ((regs1.write regT1 (regs1 rVal)).write xIdx
        ((regs1.write regT1 (regs1 rVal)) regRight -
          (regs1.write regT1 (regs1 rVal)) regT2)) (right - 1) hIdx2
  refine ⟨regs2, ?_, ?_, hval2⟩
  · have htrans :=
      ((((hg.trans hs8).trans hrun1).trans hs414).trans hs415).trans hrun2
    have hpc : (416 : Nat) + 405 = 821 := by decide
    rw [hpc] at htrans
    simpa [List.append_assoc] using htrans
  · -- the LEFT packet survives the right select in `regT1`
    rw [hpres2 regT1 (by decide)]
    simp [RegFile.write, regT1, xIdx]
    exact hval1

/-! ## SCOPE, STATED HONESTLY

What is EXECUTED above is the guard and both select legs — pc `0` to `821`.
The close/LCA leg is DEFINED and HOSTED at `827` (`closeLcaProgramAt`, both
arms executed in `E1WholeQueryCloseLca`), and the join between them is
defined, but the join's own simulation and the rank/output stages are NOT
executed here, so `WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) is
NOT discharged by this module.

Two obligations block the remainder, and neither is a matter of assembly
effort:

1. **The cross arm exports no preservation clause**
   (`crossBlockArmProgramAt_runsTo`, `E1CrossBlockArm.lean:1181`, deliberately
   — see its header at `:1143`). Every register fact the rank and output
   stages need would have to be carried across it, and nothing currently
   entitles a caller to do that.
2. **The cross-block arm's interior object is not reconciled with the route's.**
   `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`) yields the interior as
   `if leftBlock + 1 < rightBlock then concreteBPRelativeRmmInteriorRangeMin… else pure none`,
   while `crossBlockArm_withCanonicalInterior_runsTo` produces
   `⟨dispatchRouteValue …, dispatchEvents …⟩`. Those are not the same term and
   no theorem in the tree identifies them.

Both are recorded rather than worked around. A composition that assumed either
would be a witness constructed FOR a premise rather than found at the target.
-/

end E1Query
end WordRAM
end RMQ
