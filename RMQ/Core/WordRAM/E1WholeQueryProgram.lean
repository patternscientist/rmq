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

/-! ## THE MISSING OUTPUT STAGE, AS AN EXECUTED FACT RATHER THAN A TODO

`programSkeleton`'s own docstring (`E1QueryProgram.lean:130`) says "the valid
path ends by writing `regOut` and halting".  THIS VALID PATH DOES NEITHER:
there is no `.halt` and no write to `regOut` anywhere in
`wholeQueryValidPathThroughLca`.

That is not merely an absence, and the difference matters enough to pin with a
theorem.  The close/LCA leg's exit pc is `closeLcaExit 827 = 5580`, and the
skeleton places `invalidExitBlock` at `8 + validPath.length`, which is ALSO
`5580`.  So the valid path does not stop at its exit — it FALLS THROUGH into
`invalidExitBlock`, whose two instructions are `.const regOut 0` and `.halt`.
`regOut = 0` is the NONE packet.

**Consequently the composed program, as it currently stands, would halt
carrying `none` for every valid query, including those whose route value is
`some`.**  Nothing proved in this module or in `E1WholeQueryCloseLca` is
wrong — no theorem here claims the whole path runs, and the legs' own
`runsTo`s stop at their exits.  But a reader who assumed the remaining work
was "compose the executed legs" would be composing toward a program that
answers `none` unconditionally, and the composition would fail at
`WholeQueryMachineAgrees`'s value clause rather than anywhere near the code
responsible.

An output stage must therefore be BUILT, and the valid path's length will
change when it lands, which moves `invalidExitBlock` with it.

**THE STAGE IS BUILT BELOW (E1-LaneA5, DD-20260719-180), AND THIS THEOREM IS
RETAINED AS THE RECORD OF WHAT THE REPAIR PREVENTS.**  It is a true statement
about `wholeQueryValidPathThroughLca`, which is still the definition of the
path THROUGH the close/LCA leg; the repaired path is `wholeQueryValidPath`,
which appends `wholeQueryOutputStage` and is 64 instructions longer, so its
exit address is no longer the leg's.  `wholeQueryValidPath_exit_is_not_invalidExit`
is the repaired counterpart, and `wholeQueryOutputStage_runsTo` EXECUTES the
repaired path from this very address to a halt that is not the `none`
writer's.

Retaining both is deliberate: the defect and its repair are pinned by
theorems that would both break if the layout drifted, so neither the
coincidence nor its absence can become silent. -/
theorem wholeQueryValidPath_exit_is_invalidExit
    (shape : Cartesian.CartesianShape) (noneExit : Nat) :
    E1WholeQueryCloseLca.closeLcaExit 827 =
      8 + (wholeQueryValidPathThroughLca shape noneExit).length := by
  simp [E1WholeQueryCloseLca.closeLcaExit]

/-- The skeleton really does host `.const regOut 0; .halt` at the address the
valid path exits to — so the fall-through above is a fact about the composed
program, not about the arithmetic alone.

RETAINED AS THE RECORD OF THE DEFECT (E1-LaneA5).  It is stated about
`wholeQueryValidPathThroughLca`, the path that stops at the close/LCA leg.
Under the repaired path `wholeQueryValidPath` the same address hosts the
output stage's first instruction instead, which
`wholeQueryValidPath_hosts_outputStage` proves and
`wholeQueryProgram_at_closeLcaExit_is_not_noneWriter` states as the direct
contradiction of this theorem's conclusion. -/
theorem wholeQueryValidPath_falls_into_noneWriter
    (shape : Cartesian.CartesianShape) (n noneExit : Nat) :
    HostedAt (programSkeleton n (wholeQueryValidPathThroughLca shape noneExit))
        (E1WholeQueryCloseLca.closeLcaExit 827) invalidExitBlock := by
  rw [wholeQueryValidPath_exit_is_invalidExit shape noneExit]
  exact programSkeleton_hosts_invalidExit n _

/-! ## THE OUTPUT STAGE — THE REPAIR

The stage that was missing is not "write `regOut` and halt".  The route's
`.full` value is
`some ((concreteBPNativeRankCloseWordTraceResultAtSegment shape … (answerClose + 1)).value - 1)`
(`wholeQueryBranchValue`, `E1RouteDecomposition.lean:330`), so between the
close/LCA leg's answer in `fRes` and the output packet there is a RANK LEG.
An output stage that packaged `fRes` directly would halt at the right address
carrying the wrong number — the same class of defect as the three address
coincidences, one level up.

    5580   rank setup      2    rPos := fRes + 1
    5582   rank leg       60    `rankCloseBlock` at the canonical rank data
    5642   packet write    2    regOut := rVal ; halt
    5644   ...                  `invalidExitBlock` starts HERE, one past the halt

`regOut := rVal` is exact rather than approximate, and the reason is worth
stating: the packet convention is `decodePacket (v + 1) = some v` and the
route's value is `rank.value - 1`, so the register that must be written is the
rank value ITSELF — the option shift is already carried by the convention.  No
increment and no decrement appears in the stage, and that is a consequence of
the two conventions agreeing, not a coincidence to be checked at runtime.
-/

/-- Rank setup: the rank leg reads its position from `rPos`, and the route
indexes the rank leg at `answerClose + 1` where `answerClose` is the close/LCA
leg's answer in `fRes`.  Two instructions because the ISA has no
add-immediate; the `.add` reads `rPos` in its own pre-state, where the
preceding `.const` has left `1`. -/
def wholeQueryRankSetup : List Instr :=
  [ .const rPos 1
  , .add rPos fRes rPos ]

@[simp] theorem wholeQueryRankSetup_length :
    wholeQueryRankSetup.length = 2 := rfl

/-- The rank-close leg at the canonical rank data, hosted at base `B`.
Spelled exactly as `rankCloseBlock_runsTo_canonical` (`E1RankCanonical.lean:257`)
demands, so that its hosting hypothesis is discharged by `rfl`. -/
def wholeQueryRankLeg (shape : Cartesian.CartesianShape) (B : Nat) :
    List Instr :=
  rankCloseBlock B concreteBPNativeRankCloseTraceSegmentBase
    (bpFringeChunkBits shape.bpCode.length)
    shape.bpCode.length
    (builtRelativeSplitBPCloseRankData shape).wordSize
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper

@[simp] theorem wholeQueryRankLeg_length (shape : Cartesian.CartesianShape)
    (B : Nat) : (wholeQueryRankLeg shape B).length = 60 := rfl

/-- The packet write and the halt: `regOut := rVal`, then stop. -/
def wholeQueryPacketWrite : List Instr :=
  [ .move regOut rVal
  , .halt ]

@[simp] theorem wholeQueryPacketWrite_length :
    wholeQueryPacketWrite.length = 2 := rfl

/-- THE OUTPUT STAGE, hosted at base `B`: rank setup, rank leg, packet write
and halt. -/
def wholeQueryOutputStage (shape : Cartesian.CartesianShape) (B : Nat) :
    List Instr :=
  wholeQueryRankSetup ++
    (wholeQueryRankLeg shape (B + 2) ++ wholeQueryPacketWrite)

@[simp] theorem wholeQueryOutputStage_length
    (shape : Cartesian.CartesianShape) (B : Nat) :
    (wholeQueryOutputStage shape B).length = 64 := by
  simp [wholeQueryOutputStage]

/-! ## The repaired valid path -/

/-- THE REPAIRED VALID PATH: the path through the close/LCA leg, followed by
the output stage at the leg's own exit address.  The base handed to
`wholeQueryOutputStage` is COMPUTED from the leg's exit rather than written
down, so a length drift anywhere earlier moves the stage with it. -/
def wholeQueryValidPath (shape : Cartesian.CartesianShape) (noneExit : Nat) :
    List Instr :=
  wholeQueryValidPathThroughLca shape noneExit ++
    wholeQueryOutputStage shape (E1WholeQueryCloseLca.closeLcaExit 827)

@[simp] theorem wholeQueryValidPath_length
    (shape : Cartesian.CartesianShape) (noneExit : Nat) :
    (wholeQueryValidPath shape noneExit).length = 5636 := by
  simp [wholeQueryValidPath]

/-- The address the select join's two miss branches jump to: the skeleton's
own invalid exit, which writes the `none` packet and halts.  The two
select-miss branches and the guard's two reject branches therefore share one
`none` writer. -/
def wholeQueryNoneExit : Nat := 5644

/-- The `none` exit really IS the skeleton's invalid-exit base under the
repaired path.  An executed equality, so that adding or removing one
instruction anywhere in the valid path breaks the build rather than silently
sending the miss branches into the middle of the output stage. -/
theorem wholeQueryNoneExit_is_invalidExit_base
    (shape : Cartesian.CartesianShape) :
    8 + (wholeQueryValidPath shape wholeQueryNoneExit).length =
      wholeQueryNoneExit := by
  simp [wholeQueryNoneExit]

/-! ## Hosting the repaired path -/

/-- The repaired path hosts the through-LCA prefix at `8` and the output stage
at the close/LCA leg's exit `5580`, every offset computed by
`append_left`/`append_right`. -/
theorem wholeQueryValidPath_hosts_outputStage
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {noneExit : Nat}
    (hHost : HostedAt program 8 (wholeQueryValidPath shape noneExit)) :
    HostedAt program 8 (wholeQueryValidPathThroughLca shape noneExit) ∧
      HostedAt program (E1WholeQueryCloseLca.closeLcaExit 827)
        (wholeQueryOutputStage shape
          (E1WholeQueryCloseLca.closeLcaExit 827)) := by
  refine ⟨hHost.append_left, ?_⟩
  have hrest := hHost.append_right
    (code₁ := wholeQueryValidPathThroughLca shape noneExit)
  have harith : 8 + (wholeQueryValidPathThroughLca shape noneExit).length =
      E1WholeQueryCloseLca.closeLcaExit 827 := by
    simp [E1WholeQueryCloseLca.closeLcaExit]
  rw [harith] at hrest
  exact hrest

/-- The output stage's three sub-blocks, each at its computed base. -/
theorem wholeQueryOutputStage_hosts (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {B : Nat}
    (hHost : HostedAt program B (wholeQueryOutputStage shape B)) :
    HostedAt program B wholeQueryRankSetup ∧
      HostedAt program (B + 2) (wholeQueryRankLeg shape (B + 2)) ∧
      HostedAt program (B + 62) wholeQueryPacketWrite := by
  have h1 : HostedAt program B wholeQueryRankSetup := hHost.append_left
  have hrest := hHost.append_right (code₁ := wholeQueryRankSetup)
  have hrest' : HostedAt program (B + 2)
      (wholeQueryRankLeg shape (B + 2) ++ wholeQueryPacketWrite) := by
    simpa using hrest
  refine ⟨h1, hrest'.append_left, ?_⟩
  have := hrest'.append_right (code₁ := wholeQueryRankLeg shape (B + 2))
  have harith : B + 2 + (wholeQueryRankLeg shape (B + 2)).length = B + 62 := by
    simp
  rw [harith] at this
  exact this

/-! ## THE OUTPUT STAGE, EXECUTED

Rule 3: the address coincidence was found by arithmetic, so the repair is
confirmed by EXECUTION, not by a layout argument.
-/

/--
THE OUTPUT STAGE RUNS, FROM THE EXACT ADDRESS THAT USED TO FALL THROUGH.

From `⟨regs, B, false⟩` the stage sets `rPos := fRes + 1`, runs the canonical
rank leg, copies its value into `regOut` and HALTS at `B + 63`.  The receipt is
the route's rank-leg trace at `regs fRes + 1` — which is the position the
route's `.full` branch indexes the rank leg at — and the category log is the
frozen `rankCloseHitCats` bracketed by the stage's own four instructions.

Universally quantified in `shape`, `B` and the incoming register file: no
sampling, no readiness guard, no size threshold.
-/
theorem wholeQueryOutputStage_runsTo (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {B : Nat}
    (hHost : HostedAt program B (wholeQueryOutputStage shape B))
    (regs : RegFile) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, B, false⟩ ⟨regsF, B + 63, true⟩
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs fRes + 1)).trace
        ([Category.registerWrite, Category.arithmetic] ++
          (rankCloseHitCats
              (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
                ((builtRelativeSplitBPCloseRankData shape).wordOffset
                  (regs fRes + 1))) ++
            [Category.registerWrite, Category.control])) ∧
      regsF regOut =
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs fRes + 1)).value := by
  obtain ⟨hsetup, hleg, hwrite⟩ := wholeQueryOutputStage_hosts shape hHost
  -- pc B: rPos := 1
  have hf0 : program[B]? = some (.const rPos 1) := hsetup.head
  have hs0 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regs, B, false⟩ ⟨regs.write rPos 1, B + 1, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs, B, false⟩) rfl hf0
  -- pc B + 1: rPos := fRes + rPos, and `fRes ≠ rPos` so the first operand
  -- is still the close/LCA leg's answer
  have hf1 : program[B + 1]? = some (.add rPos fRes rPos) := (hsetup.tail).head
  have hs1 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regs.write rPos 1, B + 1, false⟩
      ⟨(regs.write rPos 1).write rPos
        ((regs.write rPos 1) fRes + (regs.write rPos 1) rPos), B + 2, false⟩
      [] [Category.arithmetic] :=
    RunsTo.add (s := ⟨regs.write rPos 1, B + 1, false⟩) rfl hf1
  -- the register file entering the rank leg carries `fRes + 1` in `rPos`
  have hpos : ((regs.write rPos 1).write rPos
      ((regs.write rPos 1) fRes + (regs.write rPos 1) rPos)) rPos =
      regs fRes + 1 := by
    simp [RegFile.write, rPos, fRes]
  obtain ⟨regsR, hrunR, hval, _hpresR⟩ :=
    rankCloseBlock_runsTo_canonical shape (B := B + 2) hleg
      ((regs.write rPos 1).write rPos
        ((regs.write rPos 1) fRes + (regs.write rPos 1) rPos))
  rw [hpos] at hrunR hval
  -- pc B + 62: regOut := rVal
  have hf62 : program[B + 62]? = some (.move regOut rVal) := hwrite.head
  have hs62 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regsR, B + 62, false⟩
      ⟨regsR.write regOut (regsR rVal), B + 63, false⟩ []
      [Category.registerWrite] :=
    RunsTo.move (s := ⟨regsR, B + 62, false⟩) rfl hf62
  -- pc B + 63: halt
  have hf63 : program[B + 63]? = some .halt := (hwrite.tail).head
  have hs63 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regsR.write regOut (regsR rVal), B + 63, false⟩
      ⟨regsR.write regOut (regsR rVal), B + 63, true⟩ [] [Category.control] :=
    RunsTo.halt (s := ⟨regsR.write regOut (regsR rVal), B + 63, false⟩) rfl hf63
  refine ⟨regsR.write regOut (regsR rVal), ?_, ?_⟩
  · have hpc : B + 2 + 60 = B + 62 := by omega
    rw [hpc] at hrunR
    have htrans := (((hs0.trans hs1).trans hrunR).trans hs62).trans hs63
    simpa [List.append_assoc] using htrans
  · rw [RegFile.write_same]
    exact hval

/-! ## THE REPAIR, CONFIRMED — three independent ways

The brief for this lane was explicit that a layout argument is not evidence
here, three address coincidences over.  So the repair is confirmed at three
levels, in increasing strength: the ADDRESSES differ, the INSTRUCTION at the
old exit is not the `none` writer's, and the machine EXECUTES from that
address to a halt strictly before the `none` writer's first instruction.

The third subsumes the first two.  All three are kept because each fails
differently under a future layout drift, and the campaign's experience is that
the check which happens to survive a refactor is the one that catches the next
defect.
-/

/-- THE WHOLE-QUERY PROGRAM: the skeleton at the repaired valid path, with the
select join's miss branches wired to the skeleton's own `none` writer. -/
def wholeQueryProgram (shape : Cartesian.CartesianShape) (n : Nat) :
    E1Machine.Program :=
  programSkeleton n (wholeQueryValidPath shape wholeQueryNoneExit)

/-- LEVEL 1 — ADDRESSES.  The close/LCA leg's exit is no longer the invalid
exit's base: `5580` against `5644`.  This is the direct negation of
`wholeQueryValidPath_exit_is_invalidExit`'s conclusion, with the repaired path
in place of the through-LCA one. -/
theorem wholeQueryValidPath_exit_is_not_invalidExit
    (shape : Cartesian.CartesianShape) :
    E1WholeQueryCloseLca.closeLcaExit 827 ≠
      8 + (wholeQueryValidPath shape wholeQueryNoneExit).length := by
  simp [E1WholeQueryCloseLca.closeLcaExit]

/-- LEVEL 2 — INSTRUCTION CONTENT.  At the address the close/LCA leg exits to,
the repaired program holds the output stage's first instruction, and that
instruction is not the one `invalidExitBlock` begins with.

An address argument alone would not settle this: two different blocks can
begin at two different addresses and still both be `none` writers.  This says
the code actually reached is the rank setup. -/
theorem wholeQueryProgram_at_closeLcaExit_is_not_noneWriter
    (shape : Cartesian.CartesianShape) (n : Nat) :
    (wholeQueryProgram shape n)[E1WholeQueryCloseLca.closeLcaExit 827]? =
        some (.const rPos 1) ∧
      some (Instr.const rPos 1) ≠ invalidExitBlock.head? := by
  refine ⟨?_, by decide⟩
  have hvp : HostedAt (wholeQueryProgram shape n) 8
      (wholeQueryValidPath shape wholeQueryNoneExit) :=
    programSkeleton_hosts_validPath n _
  obtain ⟨_, hout⟩ := wholeQueryValidPath_hosts_outputStage shape hvp
  exact (wholeQueryOutputStage_hosts shape hout).1.head

/--
LEVEL 3 — EXECUTION.  THE REPAIRED VALID PATH DOES NOT REACH THE `none`
WRITER.

From the close/LCA leg's exit — the exact address that used to fall into
`.const regOut 0; .halt` — the repaired program RUNS to a HALTED state at pc
`5643`, while `invalidExitBlock`'s two instructions sit at `5644` and `5645`.
The machine stops one instruction before the `none` writer begins.

`RunsTo` is exact-fuel (`E1MachineCalculus.lean:96`), so this is not a
reachability estimate: every step between `5580` and the halt is enumerated by
the derivation, and none of them is at `5644`.

The output clause is what carries content where the addresses would not.  The
`none` writer's whole effect is `regOut := 0`; this run's `regOut` is a ROUTE
OBJECT — the rank leg's value at the position the route's `.full` branch
indexes.  So the repair is visible in the answer, not only in the layout.
-/
theorem wholeQueryValidPath_does_not_reach_noneWriter
    (shape : Cartesian.CartesianShape) (n : Nat) (regs : RegFile) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n)
          ⟨regs, E1WholeQueryCloseLca.closeLcaExit 827, false⟩
          ⟨regsF, 5643, true⟩
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs fRes + 1)).trace
        ([Category.registerWrite, Category.arithmetic] ++
          (rankCloseHitCats
              (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
                ((builtRelativeSplitBPCloseRankData shape).wordOffset
                  (regs fRes + 1))) ++
            [Category.registerWrite, Category.control])) ∧
      (5643 : Nat) <
        8 + (wholeQueryValidPath shape wholeQueryNoneExit).length ∧
      regsF regOut =
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (regs fRes + 1)).value := by
  have hvp : HostedAt (wholeQueryProgram shape n) 8
      (wholeQueryValidPath shape wholeQueryNoneExit) :=
    programSkeleton_hosts_validPath n _
  obtain ⟨_, hout⟩ := wholeQueryValidPath_hosts_outputStage shape hvp
  obtain ⟨regsF, hrun, hval⟩ := wholeQueryOutputStage_runsTo shape hout regs
  have hpc : E1WholeQueryCloseLca.closeLcaExit 827 + 63 = 5643 := by
    simp [E1WholeQueryCloseLca.closeLcaExit]
  rw [hpc] at hrun
  exact ⟨regsF, hrun, by simp, hval⟩

/--
WHAT THE REPAIR DOES *NOT* DECIDE, AS AN IFF.

Modelled on `lcaNone_impostor` (`E1WholeQueryCats.lean`): the honest way to
record a receipt's blind spot is to state the exact condition under which the
repaired program's output coincides with the `none` writer's, rather than to
assert the coincidence never happens.

The output stage writes `regOut := rank.value`, and the `none` writer writes
`regOut := 0`.  So the two agree EXACTLY when the rank leg's value is zero.
This lane does not prove that never happens, and does not need to: the two
paths are distinguished by their RECEIPTS and by their halt addresses in every
case, including that one.  What this theorem forbids is a future consumer
concluding "the output stage always answers `some`" from the layout repair
alone — it does not, and the condition is named here. -/
theorem wholeQueryOutput_agrees_with_noneWriter_iff
    (shape : Cartesian.CartesianShape) {regsF : RegFile} {pos : Nat}
    (hout : regsF regOut =
      (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos).value) :
    decodePacket (regsF regOut) = none ↔
      (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos).value
        = 0 := by
  rw [hout]
  constructor
  · intro h
    by_cases hz :
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape pos).value
          = 0
    · exact hz
    · exact absurd h (by simp [decodePacket, hz])
  · intro h
    rw [h]
    rfl

/-! ## SCOPE, STATED HONESTLY

What is EXECUTED above is the guard and both select legs — pc `0` to `821`.
The close/LCA leg is DEFINED and HOSTED at `827` (`closeLcaProgramAt`, both
arms executed in `E1WholeQueryCloseLca`), and the join between them is
defined, but the join's own simulation and the rank/output stages are NOT
executed here, so `WholeQueryMachineAgrees` (`E1WholeQueryPublic.lean:114`) is
NOT discharged by this module.

Of the two obligations this note previously listed as blocking, the FIRST IS
NOW CLEARED and the second stands.

1. **CLEARED (E1-LaneA3, DD-20260719-160).** `crossBlockArmProgramAt_runsTo`
   (`E1CrossBlockArm.lean:1199`) now exports
   `∀ r, CloseLegUntouched r → regsF r = regs r`, and so does
   `closeLcaProgramAt_runsTo_cross` (`E1WholeQueryCloseLca.lean:258`),
   matching its same-block twin at `:191`. Register facts may now be carried
   across BOTH dispatch arms.

2. **STANDS. The cross-block arm's interior object is not reconciled with the
   route's.** `crossBlockArmSpec_eq` (`E1CrossBlockArm.lean:181`) yields the
   interior as
   `if leftBlock + 1 < rightBlock then concreteBPRelativeRmmInteriorRangeMin… else pure none`,
   while `crossBlockArm_withCanonicalInterior_runsTo`
   (`E1InteriorDispatchCompose.lean:1291`) produces
   `⟨dispatchRouteValue …, dispatchEvents …⟩`. Those are not the same term and
   no theorem in the tree identifies them.

   **The gap is on the TRACE side only, and that is the load-bearing fact for
   whoever takes it.** The VALUE side is already route-linked:
   `dispatchRouteValue` (`E1InteriorDispatchCompose.lean:381`) is by
   definition a `.value` projection of the route's own
   `canonicalRelativeRmmInteriorRangeMinComputation`, and the whole
   `twoSpanValue_*_eq_routeValue` ladder
   (`E1InteriorTwoSpan.lean:1085`, `:1123`) links the machine's values to the
   route's. But `dispatchEvents` (`:194`) is built from `twoSpanEvents`
   (`E1InteriorTwoSpan.lean:212`), which is a FREESTANDING list of events —
   grepped, and it is never once equated to any computation's `.reads`. Every
   theorem mentioning it supplies it as a `RunsTo` receipt argument.

   So the missing ladder is three lemmas, at
   `spanEvents`, `twoSpanEvents` and `dispatchEvents` level, each equating a
   machine event list to `(…Computation …).run … |>.reads.map
   (TraceEvent.readWord segment ·.1 ·.2)`. The precedent to copy is
   `minCandidateMachineTrace_eq_routeReads`
   (`E1InteriorMinCandidate.lean:1296`), which does exactly this one rung
   lower, resting on `:1172`, `:1210` and `:1273`. The five-way `if` in
   `dispatchEvents` branches on the SAME guards as
   `interiorRangeMin_of_count_zero` (`E1InteriorDispatch.lean:456`) through
   `interiorRangeMin_of_cross` (`:516`), which are full computation
   equalities, so `.reads` follows from them by congruence.

   Budget a segment/store reconciliation too: the machine side is fixed at
   `(canonicalSummaryLayout shape).segment` with
   `concreteBPNativeSuccinctRMQGlobalReadStore shape`, while the route object
   is parametric in `segments.canonicalComponent` and `store`.

This is recorded rather than worked around. A composition that assumed it
would be a witness constructed FOR a premise rather than found at the target.
-/

end E1Query
end WordRAM
end RMQ
