import RMQ.Core.WordRAM.E1FringeArmProgram
import RMQ.Core.WordRAM.E1ProgramWidth

/-!
# E1 amended machine: the CROSS-BLOCK arm, parameterized over the interior (M3d-8)

The cross-block close object
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
(`ChargedFringeTrace.lean:1144`) sequences FIVE sub-computations:

    leftSeed  ->  leftArm  ->  INTERIOR  ->  rightSeed  ->  rightArm  -> merge

with the two seeds NON-ADJACENT: the interior sits between the left arm
and the right seed, so the right seed cannot be hoisted next to the left
one without disturbing receipt order.

## The interior is a PARAMETER, deliberately

Worker B7 (`claude/b7-charged-sparse-level`) is charging the interior's
sparse level.  When it lands, the interior sub-computation's TRACE changes
(new reads) and the route literal moves `207 -> 210`.  Everything in this
module is therefore stated over the interior as an ABSTRACT input --
`crossBlockArmSpec` takes the interior's whole `TraceResult` as an
argument, and `crossBlockArmProgramAt` takes its instruction list as a
hole.  When B7 lands, only the INSTANTIATION changes; no definition,
statement or proof here does.

`crossBlockArmSpec_eq` is the hinge: it exhibits the accepted route object
as `crossBlockArmSpec` applied to the interior's current contents.  That
is the one place the interior appears concretely, and it is one `rfl`-shaped
rewrite.

## FINDING: `windowRange` is NOT reusable by either cross arm

`E1SameBlockArm.windowRange` (`:447`) computes the SAME-BLOCK window
range: its high endpoint is driven by `rightClose - leftClose + 1`, the
span between the two query endpoints inside one block.  Both cross-block
arms need different ranges, read off `fringeLeg_trace_eq_leftArm`
(`E1FringeArmBlock.lean:618`) and `_rightArm` (`:647`):

* the LEFT arm runs from `leftClose + 1` to the END OF THE LEFT BLOCK,
  count `blockStartOf blockSize leftBlock + blockSize - leftClose`;
* the RIGHT arm runs from `blockStartOf blockSize rightBlock` to
  `rightClose + 1`, start `blockStartOf blockSize rightBlock` rather than
  `leftClose + 1`.

Neither is `windowRange`'s arithmetic, so this module supplies
`crossLeftRange` and `crossRightRange`.  Both are computed by the machine
from `fClose` with `divConst`/`mulConst` by the per-shape program constant
`blockSize` (`blockOfClose blockSize c = c / blockSize` and
`blockStartOf blockSize b = b * blockSize`, `BlockLocal.lean:864,868`) --
no route value is copied in.

Earlier surveys of the cross-block path omitted this; the M3d-7 resume
point listed the range preambles as reusable.  They are not.

## Layout at host base `A`, interior of length `n`

    A          windowAddr blockSize L                     4    left window address
    A+4        rankSeedPos                                1  ┐
    A+5        rankCloseBlock (A+5) ...                  60  ├ left seed leg
    A+65       rankSeedFinish                             3  ┘
    A+68       crossLeftRange blockSize                  10    left window range
    A+78       fringeArmProgramAt S c L (A+78)           95    LEFT ARM
    A+173      crossStashLeft                             3    bias -> mLV/mLP
    A+176      <INTERIOR HOLE>                            n
    A+176+n    crossRepoint                               1    fClose := fRight
    A+177+n    windowAddr blockSize L                     4    right window address
    A+181+n    rankSeedPos                                1  ┐
    A+182+n    rankCloseBlock (A+182+n) ...              60  ├ right seed leg
    A+242+n    rankSeedFinish                             3  ┘
    A+245+n    crossRightRange blockSize                 10    right window range
    A+255+n    fringeArmProgramAt S c L (A+255+n)        95    RIGHT ARM
    A+350+n    crossStashRight                            3    bias -> mRV/mRP
    A+353+n    candMerge3 (A+353+n)                      16    THREE-WAY MERGE
    A+369+n                                                    cross arm exit

Only the two seed legs, the two arms and the interior emit receipts, and
they appear in exactly the route's order, so the composite receipt is the
route's -- the address/range preambles, the stashes, the repoint and the
merge are all read-free.

## Scope, stated honestly

This module delivers the LAYOUT (program, hosting decomposition, width
certificate) and the route-side INTERFACE.  The composed simulation
theorem is NOT here: it needs the interior's own `RunsTo`, which is
blocked (M3d-3 section 2).  Section `Remaining` at the foot of this file
records the exact residual obligations.  No matrix row is closed.
-/

namespace RMQ
namespace WordRAM
namespace E1CrossBlockArm

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open E1FringeArmProgram
open E1SameBlockArm
open E1SameBlockLeg
open E1RankBlock
open E1CandMerge3
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

private theorem hostedAt_step {program : E1Machine.Program} {base : Nat}
    {code₁ code₂ : List Instr} {n : Nat}
    (h : HostedAt program base (code₁ ++ code₂))
    (hn : base + code₁.length = n) :
    HostedAt program n code₂ := hn ▸ h.append_right

/-! ## The route-side interface, with the interior abstracted -/

/--
THE CROSS-BLOCK CLOSE OBJECT WITH THE INTERIOR AS AN ABSTRACT INPUT.

`interior` supplies the middle sub-computation's `TraceResult` -- its
value (an optional candidate) and its trace -- and nothing else about it
is used.  The two seeds, the two arms, the merge and the close projection
are the route's own.

This is the form every machine-side statement about the cross-block arm
should be written against, so that B7's change to the interior is an
argument change rather than a restatement.
-/
def crossBlockArmSpec (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (interior : WordRAM.TraceResult (Option (Nat × Nat)))
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
  let leftSeed :=
    localBPSeedFromRankCloseTraceResult shape rankCloseTrace blockSize
      leftClose
  let left :=
    bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore
      shape store fringeSegment blockSize leftClose leftSeed.value
  let rightSeed :=
    localBPSeedFromRankCloseTraceResult shape rankCloseTrace blockSize
      rightClose
  let right :=
    bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore
      shape store fringeSegment blockSize rightClose rightSeed.value
  { value :=
      bpCandidateClose?
        (bpCandidateMerge3? left.value interior.value right.value)
  , trace :=
      leftSeed.trace ++
        (left.trace ++
          (interior.trace ++ (rightSeed.trace ++ right.trace))) }

/--
THE HINGE.  The accepted cross-block object IS `crossBlockArmSpec` applied
to the interior's current contents.

This is the ONLY place in the machine-side development where the interior
appears concretely.  When B7 changes the interior's trace, this theorem's
statement changes in its `interior` argument and nowhere else; every
consequent stated over `crossBlockArmSpec` is untouched.
-/
theorem crossBlockArmSpec_eq (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (segments : BPRelativeRmmInteriorTraceSegments)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (leftClose rightClose : Nat) :
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
        shape rankCloseTrace segments fringeSegment store leftClose
        rightClose =
      crossBlockArmSpec shape rankCloseTrace fringeSegment store
        (if blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose + 1 <
            blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              rightClose then
          concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
            shape segments store
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
              leftClose + 1)
            (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
                rightClose -
              blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape)
                leftClose - 1)
        else
          WordRAM.TraceResult.pure none)
        leftClose rightClose := by
  unfold
    bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
    crossBlockArmSpec
  simp [WordRAM.TraceResult.bind, WordRAM.TraceResult.map]

/-- The interior contributes to the composite receipt in exactly one
place, and the guard's ELSE branch contributes nothing.  This is what
makes "the interior is a hole" a checked statement rather than a picture. -/
theorem crossBlockArmSpec_trace_of_interior_pure
    (shape : Cartesian.CartesianShape)
    (rankCloseTrace : Nat -> WordRAM.TraceResult Nat)
    (fringeSegment : Nat) (store : WordRAM.ReadStore)
    (middle? : Option (Nat × Nat)) (leftClose rightClose : Nat) :
    (crossBlockArmSpec shape rankCloseTrace fringeSegment store
        (WordRAM.TraceResult.pure middle?) leftClose rightClose).trace =
      (crossBlockArmSpec shape rankCloseTrace fringeSegment store
        (WordRAM.TraceResult.pure none) leftClose rightClose).trace := by
  simp [crossBlockArmSpec, WordRAM.TraceResult.pure]

/-! ## The four new segments -/

/--
LEFT cross-block window range at base `Q` (ten instructions, exit
`Q + 10`).  Computes the left fringe arm's `fStart`/`fLo`/`fHi` from
`fClose` (the left close) and the window bit base `fBB`.

The high endpoint runs to the END OF THE LEFT BLOCK: the route's count is
`blockStartOf blockSize leftBlock + blockSize - leftClose`, which the
machine forms as `(leftClose / blockSize + 1) * blockSize - leftClose`.
`windowRange`'s `rightClose - leftClose + 1` is the same-block span and is
WRONG here.
-/
def crossLeftRange (blockSize : Nat) : List Instr :=
  [ .const fT 1                     -- Q+0
  , .add fStart fClose fT           -- Q+1  start  = leftClose + 1
  , .sub fLo fStart fBB             -- Q+2  relLo  = start - base
  , .divConst fU fClose blockSize   -- Q+3  leftBlock
  , .add fU fU fT                   -- Q+4  leftBlock + 1
  , .mulConst fU fU blockSize       -- Q+5  block end
  , .sub fU fU fClose               -- Q+6  count
  , .add fHi fStart fU              -- Q+7  start + count
  , .sub fHi fHi fT                 -- Q+8  ... - 1
  , .sub fHi fHi fBB ]              -- Q+9  relHi = ... - base

@[simp] theorem crossLeftRange_length (blockSize : Nat) :
    (crossLeftRange blockSize).length = 10 := rfl

/-- Category log of the left range preamble: one register write, one
division, one multiplication, seven further arithmetic ticks.  No read,
no branch. -/
def crossLeftRangeCats : List Category :=
  (crossLeftRange 1).map Instr.category

@[simp] theorem crossLeftRangeCats_length :
    crossLeftRangeCats.length = 10 := rfl

theorem crossLeftRange_cats (blockSize : Nat) :
    (crossLeftRange blockSize).map Instr.category = crossLeftRangeCats := by
  simp [crossLeftRange, crossLeftRangeCats, Instr.category]

theorem crossLeftRange_straight (blockSize : Nat) :
    ∀ instr ∈ crossLeftRange blockSize, instr.isStraight = true := by
  intro instr hi
  simp only [crossLeftRange, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Constructor-exhaustive width certificate for the left range preamble.
The `divConst` arm's positivity obligation is discharged from `hbspos`,
never assumed. -/
theorem crossLeftRange_fits (w blockSize : Nat) (hw : 70 < 2 ^ w)
    (hbspos : 0 < blockSize) (hbs : blockSize < 2 ^ w) :
    ∀ instr ∈ crossLeftRange blockSize, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  simp only [crossLeftRange, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;>
    simp only [Instr.FieldsFit, fT, fStart, fClose, fLo, fBB, fU, fHi] <;>
    omega

/--
RIGHT cross-block window range at base `R` (ten instructions, exit
`R + 10`).  Computes the right fringe arm's `fStart`/`fLo`/`fHi` from
`fClose` (which the repoint has set to the RIGHT close) and `fBB`.

The start is `blockStartOf blockSize rightBlock`, not `leftClose + 1`, and
the high endpoint is formed the route's way -- `blockStart + (rightClose -
blockStart + 2) - 1 - base` -- step by step, rather than by the
algebraically equal but structurally different `rightClose + 1 - base`.
-/
def crossRightRange (blockSize : Nat) : List Instr :=
  [ .const fT 1                          -- R+0
  , .divConst fStart fClose blockSize    -- R+1  rightBlock
  , .mulConst fStart fStart blockSize    -- R+2  start = blockStart
  , .sub fLo fStart fBB                  -- R+3  relLo = start - base
  , .sub fU fClose fStart                -- R+4  rightClose - blockStart
  , .add fU fU fT                        -- R+5  ... + 1
  , .add fU fU fT                        -- R+6  ... + 2
  , .add fHi fStart fU                   -- R+7  blockStart + that
  , .sub fHi fHi fT                      -- R+8  ... - 1
  , .sub fHi fHi fBB ]                   -- R+9  relHi = ... - base

@[simp] theorem crossRightRange_length (blockSize : Nat) :
    (crossRightRange blockSize).length = 10 := rfl

/-- Category log of the right range preamble. -/
def crossRightRangeCats : List Category :=
  (crossRightRange 1).map Instr.category

@[simp] theorem crossRightRangeCats_length :
    crossRightRangeCats.length = 10 := rfl

theorem crossRightRange_cats (blockSize : Nat) :
    (crossRightRange blockSize).map Instr.category =
      crossRightRangeCats := by
  simp [crossRightRange, crossRightRangeCats, Instr.category]

theorem crossRightRange_straight (blockSize : Nat) :
    ∀ instr ∈ crossRightRange blockSize, instr.isStraight = true := by
  intro instr hi
  simp only [crossRightRange, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rfl

/-- Constructor-exhaustive width certificate for the right range preamble. -/
theorem crossRightRange_fits (w blockSize : Nat) (hw : 70 < 2 ^ w)
    (hbspos : 0 < blockSize) (hbs : blockSize < 2 ^ w) :
    ∀ instr ∈ crossRightRange blockSize, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  simp only [crossRightRange, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl <;>
    simp only [Instr.FieldsFit, fT, fStart, fClose, fLo, fBB, fU, fHi] <;>
    omega

/--
LEFT STASH (three instructions): move the left arm's result out of the
shared arm registers `fRV`/`fRP` into the merge's left slot, applying the
house `+1` BIAS on the way.

The bias is not optional bookkeeping: `candMerge3_runsTo`
(`E1CandMerge3.lean:718`) requires `regs mLV = lv + 1`, and that
hypothesis is exactly the route fact `bpFringeCandGlobal_isSome`
(`E1CandMerge3.lean:84`) -- the arms' results are occupied by
construction.  The stash pins its own unit constant in `mT` rather than
reading `fOne`, for the same reason `fringeCandGlobal` does (the fold's
preservation certificate does not cover `fOne`).
-/
def crossStashLeft : List Instr :=
  [ .const mT 1
  , .add mLV fRV mT
  , .move mLP fRP ]

@[simp] theorem crossStashLeft_length : crossStashLeft.length = 3 := rfl

/-- RIGHT STASH (three instructions): the same for the merge's right slot. -/
def crossStashRight : List Instr :=
  [ .const mT 1
  , .add mRV fRV mT
  , .move mRP fRP ]

@[simp] theorem crossStashRight_length : crossStashRight.length = 3 := rfl

/-- Category log of either stash: a register write, an arithmetic tick and
a register write.  Read-free and branch-free. -/
def crossStashCats : List Category :=
  [.registerWrite, .arithmetic, .registerWrite]

theorem crossStashLeft_cats :
    crossStashLeft.map Instr.category = crossStashCats := rfl

theorem crossStashRight_cats :
    crossStashRight.map Instr.category = crossStashCats := rfl

theorem crossStashLeft_straight :
    ∀ instr ∈ crossStashLeft, instr.isStraight = true := by
  intro instr hi
  simp only [crossStashLeft, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem crossStashRight_straight :
    ∀ instr ∈ crossStashRight, instr.isStraight = true := by
  intro instr hi
  simp only [crossStashRight, List.mem_cons, List.not_mem_nil,
    or_false] at hi
  rcases hi with rfl | rfl | rfl <;> rfl

theorem crossStashLeft_fits (w : Nat) (hw : 84 < 2 ^ w) :
    ∀ instr ∈ crossStashLeft, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  simp only [crossStashLeft, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, mT, mLV, mLP, fRV, fRP] <;> omega

theorem crossStashRight_fits (w : Nat) (hw : 84 < 2 ^ w) :
    ∀ instr ∈ crossStashRight, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  simp only [crossStashRight, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl | rfl | rfl <;>
    simp only [Instr.FieldsFit, mT, mRV, mRP, fRV, fRP] <;> omega

/-- REPOINT (one instruction): retarget the shared close register at the
RIGHT close, so that the right window address and range preambles -- which
both read `fClose` -- compute the right arm's window rather than a second
copy of the left one. -/
def crossRepoint : List Instr := [ .move fClose fRight ]

@[simp] theorem crossRepoint_length : crossRepoint.length = 1 := rfl

/-- Category log of the repoint. -/
def crossRepointCats : List Category := [.registerWrite]

theorem crossRepoint_cats :
    crossRepoint.map Instr.category = crossRepointCats := rfl

theorem crossRepoint_fits (w : Nat) (hw : 71 < 2 ^ w) :
    ∀ instr ∈ crossRepoint, Instr.FieldsFit w instr := by
  intro instr hinstr
  simp only [crossRepoint, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl
  -- `fClose`/`fRight` are abbrevs and opaque to `omega` (M3d-4 gotcha)
  simp only [Instr.FieldsFit, fClose, fRight]
  omega

/-! ## The five-segment layout, with the interior as a hole -/

/-- The left seed leg's rank-close block, at the base the layout puts it. -/
private def crossRankBlock (shape : Cartesian.CartesianShape) (base : Nat) :
    List Instr :=
  rankCloseBlock base concreteBPNativeRankCloseTraceSegmentBase
    (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
    (builtRelativeSplitBPCloseRankData shape).wordSize
    (builtRelativeSplitBPCloseRankData shape).blocksPerSuper

@[simp] private theorem crossRankBlock_length
    (shape : Cartesian.CartesianShape) (base : Nat) :
    (crossRankBlock shape base).length = 60 := by
  simp [crossRankBlock]

/--
THE CROSS-BLOCK ARM LAID OUT FOR HOST BASE `A`, WITH A HOLE FOR THE
INTERIOR.

`interior` is an arbitrary instruction list.  Nothing in this definition
or in any theorem about it depends on the interior's CONTENTS -- only on
its LENGTH, through the addresses of everything after it.  That is what
lets the layout be built, hosted and width-certified before the interior
leg exists, and what will let B7's interior drop in without disturbing
anything here.

Every internal address is `A`-relative and computed from the preceding
segments' lengths: the two rank blocks' own segment bases, the two arms'
bases (each `fringeArmProgramAt` being itself base-parametric, M3d-8), and
the merge's base.  An off-by-one anywhere makes
`crossBlockArmProgramAt_hosts` fail to typecheck.
-/
def crossBlockArmProgramAt (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize A : Nat) (interior : List Instr) :
    List Instr :=
  windowAddr blockSize (SuccinctRank.machineWordBits shape.bpCode.length) ++
    (rankSeedPos ++
      (crossRankBlock shape (A + 5) ++
        (rankSeedFinish ++
          (crossLeftRange blockSize ++
            (fringeArmProgramAt fringeSegment (sbChunkBits shape)
                (SuccinctRank.machineWordBits shape.bpCode.length)
                (A + 78) ++
              (crossStashLeft ++
                (interior ++
                  (crossRepoint ++
                    (windowAddr blockSize
                        (SuccinctRank.machineWordBits shape.bpCode.length) ++
                      (rankSeedPos ++
                        (crossRankBlock shape (A + 182 + interior.length) ++
                          (rankSeedFinish ++
                            (crossRightRange blockSize ++
                              (fringeArmProgramAt fringeSegment
                                  (sbChunkBits shape)
                                  (SuccinctRank.machineWordBits
                                    shape.bpCode.length)
                                  (A + 255 + interior.length) ++
                                (crossStashRight ++
                                  candMerge3
                                    (A + 353 +
                                      interior.length))))))))))))))))

@[simp] theorem crossBlockArmProgramAt_length
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize A : Nat) (interior : List Instr) :
    (crossBlockArmProgramAt shape fringeSegment blockSize A interior).length =
      369 + interior.length := by
  simp [crossBlockArmProgramAt]
  omega

/--
EVERY SEGMENT'S HOSTING FACT, from the single assumption that the layout
is hosted at `A`.

The addresses after the hole are `interior.length`-dependent and are
FORCED by the preceding segments, so the layout table in the module header
is checked rather than asserted.  In particular the two arms are hosted at
`A + 78` and `A + 255 + n` and each is given its OWN base as the argument
to `fringeArmProgramAt`, which is what makes both arms' internal branch
targets correct simultaneously -- the defect that a base-pinned arm form
would have reintroduced.
-/
theorem crossBlockArmProgramAt_hosts (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program}
    (fringeSegment blockSize A : Nat) (interior : List Instr)
    (hHost : HostedAt program A
      (crossBlockArmProgramAt shape fringeSegment blockSize A interior)) :
    HostedAt program A
        (windowAddr blockSize
          (SuccinctRank.machineWordBits shape.bpCode.length)) ∧
      HostedAt program (A + 4) rankSeedPos ∧
      HostedAt program (A + 5) (crossRankBlock shape (A + 5)) ∧
      HostedAt program (A + 65) rankSeedFinish ∧
      HostedAt program (A + 68) (crossLeftRange blockSize) ∧
      HostedAt program (A + 78)
        (fringeArmProgramAt fringeSegment (sbChunkBits shape)
          (SuccinctRank.machineWordBits shape.bpCode.length) (A + 78)) ∧
      HostedAt program (A + 173) crossStashLeft ∧
      HostedAt program (A + 176) interior ∧
      HostedAt program (A + 176 + interior.length) crossRepoint ∧
      HostedAt program (A + 177 + interior.length)
        (windowAddr blockSize
          (SuccinctRank.machineWordBits shape.bpCode.length)) ∧
      HostedAt program (A + 181 + interior.length) rankSeedPos ∧
      HostedAt program (A + 182 + interior.length)
        (crossRankBlock shape (A + 182 + interior.length)) ∧
      HostedAt program (A + 242 + interior.length) rankSeedFinish ∧
      HostedAt program (A + 245 + interior.length)
        (crossRightRange blockSize) ∧
      HostedAt program (A + 255 + interior.length)
        (fringeArmProgramAt fringeSegment (sbChunkBits shape)
          (SuccinctRank.machineWordBits shape.bpCode.length)
          (A + 255 + interior.length)) ∧
      HostedAt program (A + 350 + interior.length) crossStashRight ∧
      HostedAt program (A + 353 + interior.length)
        (candMerge3 (A + 353 + interior.length)) := by
  rw [crossBlockArmProgramAt] at hHost
  have h1 := hostedAt_step (n := A + 4) hHost (by simp)
  have h2 := hostedAt_step (n := A + 5) h1 (by simp)
  have h3 := hostedAt_step (n := A + 65) h2 (by simp)
  have h4 := hostedAt_step (n := A + 68) h3 (by simp)
  have h5 := hostedAt_step (n := A + 78) h4 (by simp)
  have h6 := hostedAt_step (n := A + 173) h5 (by simp)
  have h7 := hostedAt_step (n := A + 176) h6 (by simp)
  have h8 := hostedAt_step (n := A + 176 + interior.length) h7 (by simp)
  have h9 := hostedAt_step (n := A + 177 + interior.length) h8 (by
    simp; omega)
  have h10 := hostedAt_step (n := A + 181 + interior.length) h9 (by
    simp; omega)
  have h11 := hostedAt_step (n := A + 182 + interior.length) h10 (by
    simp; omega)
  have h12 := hostedAt_step (n := A + 242 + interior.length) h11 (by
    simp; omega)
  have h13 := hostedAt_step (n := A + 245 + interior.length) h12 (by
    simp; omega)
  have h14 := hostedAt_step (n := A + 255 + interior.length) h13 (by
    simp; omega)
  have h15 := hostedAt_step (n := A + 350 + interior.length) h14 (by
    simp; omega)
  have h16 := hostedAt_step (n := A + 353 + interior.length) h15 (by
    simp; omega)
  exact ⟨hHost.append_left, h1.append_left, h2.append_left,
    h3.append_left, h4.append_left, h5.append_left, h6.append_left,
    h7.append_left, h8.append_left, h9.append_left, h10.append_left,
    h11.append_left, h12.append_left, h13.append_left, h14.append_left,
    h15.append_left, h16⟩

/-! ## Width certificate -/

/--
CONSTRUCTOR-EXHAUSTIVE WIDTH CERTIFICATE FOR THE WHOLE CROSS-BLOCK ARM.

The interior's instructions are carried as a HYPOTHESIS (`hinterior`),
exactly as `sameBlockDispatchProgram_fits` (`E1ProgramWidth.lean:141`)
carries the cross arm: this is what lets the certificate be stated before
the interior exists, and what will FORCE the interior to be certified when
it lands.

The `interior.length`-dependent hypothesis `hA` is what bounds the two
`A`-relative arm bases and the merge base; the two `divConst`s in the range
preambles get their positivity from `hbspos`, and no divisor anywhere is
assumed positive without a route fact behind it.
-/
theorem crossBlockArmProgramAt_fits (shape : Cartesian.CartesianShape)
    {w fringeSegment blockSize A : Nat} {interior : List Instr}
    (hreg : 84 < 2 ^ w)
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
    (hinterior : ∀ instr ∈ interior, Instr.FieldsFit w instr)
    (hA : A + 369 + interior.length < 2 ^ w) :
    ∀ instr ∈ crossBlockArmProgramAt shape fringeSegment blockSize A
      interior, Instr.FieldsFit w instr := by
  have hlin : 2 * sbChunkBits shape + 2 < 2 ^ w := by
    have hle : 2 * sbChunkBits shape + 2 ≤
        (sbChunkBits shape + 1) * (2 * sbChunkBits shape + 2) :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hpowc : 2 ^ sbChunkBits shape < 2 ^ w := by
    have := Nat.pow_le_pow_right (by omega : 0 < 2) hcL
    omega
  have harmL := fringeArmProgramAt_fits (w := w) (S := fringeSegment)
    (c := sbChunkBits shape)
    (L := SuccinctRank.machineWordBits shape.bpCode.length) (A := A + 78)
    (by omega) hseg hcpos hcL hpowL hmix (by omega)
  have harmR := fringeArmProgramAt_fits (w := w) (S := fringeSegment)
    (c := sbChunkBits shape)
    (L := SuccinctRank.machineWordBits shape.bpCode.length)
    (A := A + 255 + interior.length)
    (by omega) hseg hcpos hcL hpowL hmix (by omega)
  have hrankL : ∀ instr ∈ crossRankBlock shape (A + 5),
      Instr.FieldsFit w instr := by
    intro instr h
    exact rankCloseBlock_fits (w := w) (B := A + 5)
      (G := concreteBPNativeRankCloseTraceSegmentBase)
      (c := sbChunkBits shape) (L := shape.bpCode.length)
      (WS := (builtRelativeSplitBPCloseRankData shape).wordSize)
      (BPS := (builtRelativeSplitBPCloseRankData shape).blocksPerSuper)
      (by omega) hG hcode hcpos hWSpos hWS hBPSpos hBPS hpowc hlin
      (by omega) instr h
  have hrankR : ∀ instr ∈ crossRankBlock shape (A + 182 + interior.length),
      Instr.FieldsFit w instr := by
    intro instr h
    exact rankCloseBlock_fits (w := w) (B := A + 182 + interior.length)
      (G := concreteBPNativeRankCloseTraceSegmentBase)
      (c := sbChunkBits shape) (L := shape.bpCode.length)
      (WS := (builtRelativeSplitBPCloseRankData shape).wordSize)
      (BPS := (builtRelativeSplitBPCloseRankData shape).blocksPerSuper)
      (by omega) hG hcode hcpos hWSpos hWS hBPSpos hBPS hpowc hlin
      (by omega) instr h
  intro instr hinstr
  simp only [crossBlockArmProgramAt, List.mem_append] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h | h
    | h | h | h
  · exact windowAddr_fits w blockSize _ (by omega) hbspos hbs hLpos hLw
      instr h
  · exact rankSeedPos_fits w (by omega) instr h
  · exact hrankL instr h
  · exact rankSeedFinish_fits w (by omega) instr h
  · exact crossLeftRange_fits w blockSize (by omega) hbspos hbs instr h
  · exact harmL instr h
  · exact crossStashLeft_fits w hreg instr h
  · exact hinterior instr h
  · exact crossRepoint_fits w (by omega) instr h
  · exact windowAddr_fits w blockSize _ (by omega) hbspos hbs hLpos hLw
      instr h
  · exact rankSeedPos_fits w (by omega) instr h
  · exact hrankR instr h
  · exact rankSeedFinish_fits w (by omega) instr h
  · exact crossRightRange_fits w blockSize (by omega) hbspos hbs instr h
  · exact harmR instr h
  · exact crossStashRight_fits w hreg instr h
  · exact candMerge3_fits w (A + 353 + interior.length) (by omega)
      (by omega) instr h

/-! ## Remaining (NOT implemented here)

What this module does NOT have, stated precisely so the next session does
not have to rediscover it:

1. `crossLeftRange_runsTo` / `crossRightRange_runsTo` -- the two range
   preambles' simulations, against `sbStart`-style route abbreviations for
   the LEFT-FRINGE and RIGHT-FRINGE ranges read off
   `fringeLeg_trace_eq_leftArm` / `_rightArm`.  Both blocks are
   straight-line, so `RunsTo.straight` plus a `straight_eval`-style macro
   applies directly; the route-side obligations are
   `(leftClose / blockSize + 1) * blockSize - leftClose =
   blockStartOf blockSize (blockOfClose blockSize leftClose) + blockSize -
   leftClose` (true by `blockStartOf`/`blockOfClose` unfolding plus
   `Nat.succ_mul`) and its right-hand analogue.
2. `crossStashLeft_runsTo` / `crossStashRight_runsTo` -- three
   instructions each, `RunsTo.straight`.
3. The composed `crossBlockArmProgramAt_runsTo`, stated over
   `crossBlockArmSpec` with the interior's `RunsTo` as a HYPOTHESIS
   (abstract entry/exit, trace, cats, and the two-register post-condition
   `regs mMV` biased / `regs mMP` positional, per the M3d-7 section 6
   contract).  This is composition, but it must thread register
   preservation across ~370 instructions: the binding new obligation is
   that the LEFT stash's `mLV`/`mLP` survive the interior, the right seed
   leg, the right range preamble and the right arm.  `mLV = 75` and
   `mLP = 76` sit above every existing block's write set, so each block's
   existing preservation clause should already cover them -- but
   `fringeArmProgramAt` inherits `fringeArm_runsTo`, which states NO
   preservation clause at all.  That is the one certificate that must be
   ADDED before the composition can be written, and it is a strengthening
   of an existing theorem rather than new simulation.
4. Nothing here closes or weakens any matrix row; all of REQ-E1-01..11 are
   whole-query scoped and remain OPEN.
-/

end E1CrossBlockArm
end WordRAM
end RMQ
