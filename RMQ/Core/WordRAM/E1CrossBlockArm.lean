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
    A+353+n    crossPinOne                                1    fOne := 1
    A+354+n    candMerge3 (A+354+n)                      16    THREE-WAY MERGE
    A+370+n                                                    cross arm exit

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

/--
Retarget a run's exit pc along a proved equation.

Needed because the cross-block layout's addresses carry the VARIABLE
`interior.length`: `A + 176 + n + 1` and `A + 177 + n` are equal but NOT
definitionally so, whereas the all-literal offsets of the same-block leg
compose without help.  This is the whole reason the composition below
normalises every segment's exit rather than fixing the pc once at the end
the way `sameBlockLeg_runsTo_canonical` does.
-/
private theorem runsTo_pc_congr {store : ReadStore}
    {program : E1Machine.Program} {regs regs' : RegFile} {p q q' : Nat}
    {ev : List WordRAM.TraceEvent} {cats : List Category}
    (h : RunsTo store program ⟨regs, p, false⟩ ⟨regs', q, false⟩ ev cats)
    (hq : q = q') :
    RunsTo store program ⟨regs, p, false⟩ ⟨regs', q', false⟩ ev cats := hq ▸ h

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

/--
UNIT PIN (one instruction), between the right stash and the merge.

`candMerge3_runsTo` (`E1CandMerge3.lean:718`) requires `regs fOne = 1`,
and NOTHING between the arm entry and the merge guarantees it: `fOne` is
register 40, inside the fold bank `40 .. 62`, so it fails
`FringeArmUntouched` and the arms are entitled to clobber it.  The fold's
own certificate takes `fOne = 1` as a hypothesis and does not restate it
as a conclusion.

This is the THIRD instance of the same pattern in this development --
`fringeCandGlobal` pins its own `fT`, both stashes pin their own `mT`,
and now the merge's unit is re-pinned here -- and it is deliberate in the
same way: one register write is cheaper than strengthening a 66-instruction
loop's invariant, and it keeps the segments composable exactly as written.

Kept as its own segment rather than appended to `crossStashRight`, so the
two stashes stay symmetric and the pin's reason for existing stays legible.
-/
def crossPinOne : List Instr := [ .const fOne 1 ]

@[simp] theorem crossPinOne_length : crossPinOne.length = 1 := rfl

/-- Category log of the unit pin. -/
def crossPinOneCats : List Category := [.registerWrite]

theorem crossPinOne_cats :
    crossPinOne.map Instr.category = crossPinOneCats := rfl

theorem crossPinOne_fits (w : Nat) (hw : 40 < 2 ^ w) :
    ∀ instr ∈ crossPinOne, Instr.FieldsFit w instr := by
  intro instr hinstr
  simp only [crossPinOne, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with rfl
  simp only [Instr.FieldsFit, fOne]
  omega

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

/-! ## Segment simulations

The five read-free segments above, each run by `RunsTo.straight`.  The two
range preambles state their outputs in the ROUTE's own spelling
(`blockStartOf`/`blockOfClose`), not the machine's fused arithmetic, so
that the composition below can feed them straight into
`fringeArmProgramAt_runsTo` with no bridging step in between.
-/

/-- The machine's fused block-end form IS the route's `blockStartOf` of
the NEXT block.  `Nat.succ_mul` is the whole content, but the two
spellings are structurally different and this is the only lemma that
connects them -- the machine does not copy the route's value, it
recomputes it from `fClose` by `divConst`/`mulConst`. -/
theorem cross_blockEnd_eq (blockSize close : Nat) :
    (close / blockSize + 1) * blockSize =
      blockStartOf blockSize (blockOfClose blockSize close) + blockSize := by
  simp [blockStartOf, blockOfClose, Nat.succ_mul]

/-- The machine's `divConst`-then-`mulConst` pair IS the route's
`blockStartOf (blockOfClose ...)`. -/
theorem cross_blockStart_eq (blockSize close : Nat) :
    close / blockSize * blockSize =
      blockStartOf blockSize (blockOfClose blockSize close) := by
  simp [blockStartOf, blockOfClose]

/-- Either cross-block range preamble writes only `fLo` (50), `fHi` (51),
`fT` (60), `fU` (61) and `fStart` (66).  Stated in NUMERALS, not the
register abbrevs, so `omega` can use it (the recurring M3d-4 gotcha). -/
abbrev CrossRangeUntouched (r : Nat) : Prop :=
  r ≠ 50 ∧ r ≠ 51 ∧ r ≠ 60 ∧ r ≠ 61 ∧ r ≠ 66

/-- Exact simulation of the LEFT range preamble: no receipt, ten ticks,
and the three range registers the left arm demands, in the route's own
spelling. -/
theorem crossLeftRange_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q blockSize : Nat}
    (hHost : HostedAt program Q (crossLeftRange blockSize))
    (regs : RegFile) (leftClose base : Nat)
    (hClose : regs fClose = leftClose) (hBB : regs fBB = base) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 10, false⟩ []
        crossLeftRangeCats ∧
      regs' fStart = leftClose + 1 ∧
      regs' fLo = leftClose + 1 - base ∧
      regs' fHi =
        leftClose + 1 +
          (blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize - leftClose) - 1 - base ∧
      (∀ r, CrossRangeUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store (crossLeftRange blockSize)
    (crossLeftRange_straight blockSize) Q hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store (crossLeftRange blockSize) regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store (crossLeftRange blockSize) regs = [] := by
    straight_eval [crossLeftRange]
  rw [hreads, crossLeftRange_cats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    straight_eval [crossLeftRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose]
  · rw [<- hregsW]
    straight_eval [crossLeftRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose, hBB]
  · rw [<- hregsW, <- cross_blockEnd_eq]
    straight_eval [crossLeftRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose, hBB]
  · intro r hr
    obtain ⟨h50, h51, h60, h61, h66⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [crossLeftRange, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl <;>
      straight_writes [fT, fU, fLo, fHi, fStart] <;> omega

/-- Exact simulation of the RIGHT range preamble.  Its start is the right
block's START, not `leftClose + 1`; that difference is the whole reason
`E1SameBlockArm.windowRange` is not reusable here. -/
theorem crossRightRange_runsTo
    (store : ReadStore) {program : E1Machine.Program} {R blockSize : Nat}
    (hHost : HostedAt program R (crossRightRange blockSize))
    (regs : RegFile) (rightClose base : Nat)
    (hClose : regs fClose = rightClose) (hBB : regs fBB = base) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, R, false⟩ ⟨regs', R + 10, false⟩ []
        crossRightRangeCats ∧
      regs' fStart =
        blockStartOf blockSize (blockOfClose blockSize rightClose) ∧
      regs' fLo =
        blockStartOf blockSize (blockOfClose blockSize rightClose) - base ∧
      regs' fHi =
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
          (rightClose -
            blockStartOf blockSize (blockOfClose blockSize rightClose) + 2)
          - 1 - base ∧
      (∀ r, CrossRangeUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store (crossRightRange blockSize)
    (crossRightRange_straight blockSize) R hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store (crossRightRange blockSize) regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store (crossRightRange blockSize) regs = [] := by
    straight_eval [crossRightRange]
  rw [hreads, crossRightRange_cats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_, ?_⟩
  · rw [<- hregsW, <- cross_blockStart_eq]
    straight_eval [crossRightRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose]
  · rw [<- hregsW, <- cross_blockStart_eq]
    straight_eval [crossRightRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose, hBB]
  · rw [<- hregsW, <- cross_blockStart_eq]
    straight_eval [crossRightRange, fT, fU, fLo, fHi, fStart, fClose,
      fBB] <;> simp [hClose, hBB]
  · intro r hr
    obtain ⟨h50, h51, h60, h61, h66⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [crossRightRange, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl <;>
      straight_writes [fT, fU, fLo, fHi, fStart] <;> omega

/-- The left stash writes only `mT` (83), `mLV` (75) and `mLP` (76). -/
abbrev CrossStashLeftUntouched (r : Nat) : Prop :=
  r ≠ 83 ∧ r ≠ 75 ∧ r ≠ 76

/-- The right stash writes only `mT` (83), `mRV` (79) and `mRP` (80). -/
abbrev CrossStashRightUntouched (r : Nat) : Prop :=
  r ≠ 83 ∧ r ≠ 79 ∧ r ≠ 80

/-- Exact simulation of the LEFT stash: the arm's result pair moved into
the merge's left slot with the house `+1` bias on the value. -/
theorem crossStashLeft_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q crossStashLeft) (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 3, false⟩ []
        crossStashCats ∧
      regs' mLV = regs fRV + 1 ∧
      regs' mLP = regs fRP ∧
      (∀ r, CrossStashLeftUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store crossStashLeft crossStashLeft_straight
    Q hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store crossStashLeft regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store crossStashLeft regs = [] := by
    straight_eval [crossStashLeft]
  rw [hreads, crossStashLeft_cats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    straight_eval [crossStashLeft, mT, mLV, mLP, fRV, fRP]
  · rw [<- hregsW]
    straight_eval [crossStashLeft, mT, mLV, mLP, fRV, fRP]
  · intro r hr
    obtain ⟨h83, h75, h76⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [crossStashLeft, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      straight_writes [mT, mLV, mLP] <;> omega

/-- Exact simulation of the RIGHT stash. -/
theorem crossStashRight_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q crossStashRight) (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 3, false⟩ []
        crossStashCats ∧
      regs' mRV = regs fRV + 1 ∧
      regs' mRP = regs fRP ∧
      (∀ r, CrossStashRightUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store crossStashRight
    crossStashRight_straight Q hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store crossStashRight regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store crossStashRight regs = [] := by
    straight_eval [crossStashRight]
  rw [hreads, crossStashRight_cats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_, ?_⟩
  · rw [<- hregsW]
    straight_eval [crossStashRight, mT, mRV, mRP, fRV, fRP]
  · rw [<- hregsW]
    straight_eval [crossStashRight, mT, mRV, mRP, fRV, fRP]
  · intro r hr
    obtain ⟨h83, h79, h80⟩ := hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [crossStashRight, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl | rfl | rfl <;>
      straight_writes [mT, mRV, mRP] <;> omega

/-- The unit pin writes only `fOne` (40). -/
abbrev CrossPinOneUntouched (r : Nat) : Prop := r ≠ 40

/-- Exact simulation of the unit pin: one tick, no receipt, `fOne = 1`. -/
theorem crossPinOne_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q crossPinOne) (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 1, false⟩ []
        crossPinOneCats ∧
      regs' fOne = 1 ∧
      (∀ r, CrossPinOneUntouched r → regs' r = regs r) := by
  have hf0 : program[Q]? = some (.const fOne 1) := by
    have := hHost 0 (by decide)
    simpa [crossPinOne] using this
  refine ⟨regs.write fOne 1, ?_, ?_, ?_⟩
  · have s0 : RunsTo store program ⟨regs, Q, false⟩
        ⟨regs.write fOne 1, Q + 1, false⟩ [] [.registerWrite] :=
      RunsTo.const (s := ⟨regs, Q, false⟩) rfl hf0
    simpa [crossPinOneCats] using s0
  · simp [RegFile.write]
  · intro r hr
    simp [RegFile.write, fOne, hr]

/-- The repoint writes only `fClose` (70). -/
abbrev CrossRepointUntouched (r : Nat) : Prop := r ≠ 70

/-- Exact simulation of the repoint: one tick, no receipt, `fClose`
retargeted at the right close. -/
theorem crossRepoint_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q crossRepoint) (regs : RegFile) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 1, false⟩ []
        crossRepointCats ∧
      regs' fClose = regs fRight ∧
      (∀ r, CrossRepointUntouched r → regs' r = regs r) := by
  have hstraight : ∀ instr ∈ crossRepoint, instr.isStraight = true := by
    intro instr hi
    simp only [crossRepoint, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl
    rfl
  have hrun := RunsTo.straight store crossRepoint hstraight Q hHost regs
  obtain ⟨regsW, hregsW⟩ :
      ∃ x, straightRegs store crossRepoint regs = x := ⟨_, rfl⟩
  rw [hregsW] at hrun
  have hreads : straightReads store crossRepoint regs = [] := by
    straight_eval [crossRepoint]
  rw [hreads, crossRepoint_cats] at hrun
  refine ⟨regsW, by simpa using hrun, ?_, ?_⟩
  · rw [<- hregsW]
    straight_eval [crossRepoint, fClose, fRight]
  · intro r hr
    rw [<- hregsW]
    apply straightRegs_preserves
    intro i hi
    simp only [crossRepoint, List.mem_cons, List.not_mem_nil,
      or_false] at hi
    rcases hi with rfl
    straight_writes [fClose]
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
                                  (crossPinOne ++
                                    candMerge3
                                      (A + 354 +
                                        interior.length)))))))))))))))))

@[simp] theorem crossBlockArmProgramAt_length
    (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize A : Nat) (interior : List Instr) :
    (crossBlockArmProgramAt shape fringeSegment blockSize A interior).length =
      370 + interior.length := by
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
      HostedAt program (A + 353 + interior.length) crossPinOne ∧
      HostedAt program (A + 354 + interior.length)
        (candMerge3 (A + 354 + interior.length)) := by
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
  have h17 := hostedAt_step (n := A + 354 + interior.length) h16 (by
    simp; omega)
  exact ⟨hHost.append_left, h1.append_left, h2.append_left,
    h3.append_left, h4.append_left, h5.append_left, h6.append_left,
    h7.append_left, h8.append_left, h9.append_left, h10.append_left,
    h11.append_left, h12.append_left, h13.append_left, h14.append_left,
    h15.append_left, h16.append_left, h17⟩

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
    (hA : A + 370 + interior.length < 2 ^ w) :
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
    | h | h | h | h
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
  · exact crossPinOne_fits w (by omega) instr h
  · exact candMerge3_fits w (A + 354 + interior.length) (by omega)
      (by omega) instr h

/-! ## The composed cross-block arm, over an ABSTRACT interior

The two arms' window ranges, named so the statements below stay readable.
Each is the ROUTE's own expression, read off `leftArm_value_eq` /
`rightArm_value_eq` (`E1FringeArmBlock.lean:1062`/`:1093`).
-/

/-- The LEFT cross arm's window-relative low endpoint. -/
abbrev crossLeftRelLo (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  leftClose + 1 - localBPWindowBase shape blockSize leftClose

/-- The LEFT cross arm's window-relative high endpoint: the fringe runs to
the END OF THE LEFT BLOCK. -/
abbrev crossLeftRelHi (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Nat :=
  leftClose + 1 +
    (blockStartOf blockSize (blockOfClose blockSize leftClose) + blockSize -
      leftClose) - 1 - localBPWindowBase shape blockSize leftClose

/-- The RIGHT cross arm's window-relative low endpoint: the fringe starts
at the RIGHT BLOCK'S START. -/
abbrev crossRightRelLo (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) : Nat :=
  blockStartOf blockSize (blockOfClose blockSize rightClose) -
    localBPWindowBase shape blockSize rightClose

/-- The RIGHT cross arm's window-relative high endpoint. -/
abbrev crossRightRelHi (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) : Nat :=
  blockStartOf blockSize (blockOfClose blockSize rightClose) +
    (rightClose - blockStartOf blockSize (blockOfClose blockSize rightClose) +
      2) - 1 - localBPWindowBase shape blockSize rightClose

/-- The accepted LEFT cross arm object at the canonical store and seed. -/
abbrev crossLeftArm (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  bpChunkedLeftFringeCandidateSeededTraceResultAtSegmentWithStore shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) fringeSegment
    blockSize leftClose (canonicalSeed shape blockSize leftClose)

/-- The accepted RIGHT cross arm object at the canonical store and seed. -/
abbrev crossRightArm (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize rightClose : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat)) :=
  bpChunkedRightFringeCandidateSeededTraceResultAtSegmentWithStore shape
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) fringeSegment
    blockSize rightClose (canonicalSeed shape blockSize rightClose)

/-- Category log of the LEFT arm, indexed by route-side data throughout. -/
abbrev crossLeftArmCats (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize leftClose : Nat) : List Category :=
  fringeArmCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    fringeSegment (sbChunkBits shape)
    (windowBitsOfStore (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize leftClose))
    (crossLeftRelLo shape blockSize leftClose)
    (crossLeftRelHi shape blockSize leftClose)
    (canonicalSeed shape blockSize leftClose)
    (Nat.min (crossLeftRelHi shape blockSize leftClose /
      sbChunkBits shape + 1) 33)

/-- Category log of the RIGHT arm. -/
abbrev crossRightArmCats (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize rightClose : Nat) : List Category :=
  fringeArmCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    fringeSegment (sbChunkBits shape)
    (windowBitsOfStore (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape blockSize rightClose))
    (crossRightRelLo shape blockSize rightClose)
    (crossRightRelHi shape blockSize rightClose)
    (canonicalSeed shape blockSize rightClose)
    (Nat.min (crossRightRelHi shape blockSize rightClose /
      sbChunkBits shape + 1) 33)

/--
CATEGORY LOG OF THE WHOLE CROSS-BLOCK ARM.

Every component is a FUNCTION of route-side data -- the two seed legs'
route-indexed logs, the two arms' route-indexed logs, and the merge's log
on the route's OWN three candidates -- with the interior's log carried as
a PARAMETER.  No numeral is asserted anywhere.

The merge arm is selected by `.getD (0, 0)` on the arms' values, which is
not a defaulting hack: both arms answer `some` unconditionally
(`bpFringeCandGlobal_isSome`, `E1CandMerge3.lean:84`), so the default is
unreachable and the proof discharges it by rewriting with the arms' own
value clauses.
-/
def crossBlockArmCats (shape : Cartesian.CartesianShape)
    (fringeSegment blockSize : Nat) (interiorCats : List Category)
    (interiorValue : Option (Nat × Nat)) (leftClose rightClose : Nat) :
    List Category :=
  windowAddrCats ++
    (rankSeedLegCats shape (sbBB shape blockSize leftClose) ++
      (crossLeftRangeCats ++
        (crossLeftArmCats shape fringeSegment blockSize leftClose ++
          (crossStashCats ++
            (interiorCats ++
              (crossRepointCats ++
                (windowAddrCats ++
                  (rankSeedLegCats shape (sbBB shape blockSize rightClose) ++
                    (crossRightRangeCats ++
                      (crossRightArmCats shape fringeSegment blockSize
                          rightClose ++
                        (crossStashCats ++
                          (crossPinOneCats ++
                            candMerge3Cats
                              ((crossLeftArm shape fringeSegment blockSize
                                leftClose).value.getD (0, 0))
                              interiorValue
                              ((crossRightArm shape fringeSegment blockSize
                                rightClose).value.getD
                                  (0, 0))))))))))))))

/--
EXACT SIMULATION OF THE WHOLE CROSS-BLOCK ARM AT THE CANONICAL STORE,
WITH THE INTERIOR AS AN ABSTRACT HYPOTHESIS.

Receipts are POSITIONALLY EQUAL -- a `List` equality, not a multiset or
membership claim -- to `crossBlockArmSpec`'s trace at the supplied
interior, and `fRes` carries its `.value`.

## The interior is a hypothesis, not a pin

`hInterior` supplies the interior leg's own `RunsTo` at ITS OWN base
`A + 176`, for any entry register file that carries the two query
operands.  Its trace, categories and value are PARAMETERS.  Nothing in
this theorem's statement or proof depends on the interior's contents, so
worker B7's change to the interior (new reads, route literal `207 -> 210`)
instantiates this theorem differently and does not restate it.

The interior's four preservation obligations are exactly what the
composition consumes downstream and nothing more: the two query operands
`fClose`/`fRight` (the repoint and the right preambles recompute
everything else), and the left stash's merge slots `mLV`/`mLP`, which must
survive to the merge some 194 instructions later.

RECORDED, NOT PAPERED OVER: if the interior leg turns out to need pinned
machine inputs beyond the two query operands, `hInterior`'s antecedent
gains those conjuncts and this proof gains the matching obligation to
establish them at `A + 176`.  That is a hypothesis change, not a
restatement, and the four preservation clauses are unaffected.
-/
theorem crossBlockArmProgramAt_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {A fringeSegment leftClose rightClose : Nat}
    {interior : List Instr} {interiorTrace : List WordRAM.TraceEvent}
    {interiorCats : List Category} {interiorValue : Option (Nat × Nat)}
    (hc : sbChunkBits shape ≤
      SuccinctRank.machineWordBits shape.bpCode.length)
    (hHost : HostedAt program A
      (crossBlockArmProgramAt shape fringeSegment
        (canonicalBPRelativeSummaryBlockSizeRaw shape) A interior))
    (hL0 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hL1 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hL2 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR0 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR1 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR2 : (readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hInterior : ∀ regsS : RegFile, regsS fClose = leftClose →
      regsS fRight = rightClose →
      ∃ regsI : RegFile,
        RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
            ⟨regsS, A + 176, false⟩
            ⟨regsI, A + 176 + interior.length, false⟩
          interiorTrace interiorCats ∧
        bestOfRegs (regsI mMV) (regsI mMP) = interiorValue ∧
        regsI fClose = regsS fClose ∧ regsI fRight = regsS fRight ∧
        regsI mLV = regsS mLV ∧ regsI mLP = regsS mLP)
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, A, false⟩
          ⟨regsF, A + 370 + interior.length, false⟩
        (crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨interiorValue, interiorTrace⟩ leftClose rightClose).trace
        (crossBlockArmCats shape fringeSegment
          (canonicalBPRelativeSummaryBlockSizeRaw shape) interiorCats
          interiorValue leftClose rightClose) ∧
      some (regsF fRes) =
        (crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨interiorValue, interiorTrace⟩ leftClose rightClose).value := by
  obtain ⟨q0, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, q13, q14,
    q15, q16, q17⟩ :=
    crossBlockArmProgramAt_hosts shape fringeSegment (canonicalBPRelativeSummaryBlockSizeRaw shape) A interior hHost
  -- 1. LEFT window address preamble
  obtain ⟨r1, hrun1, hbase1, hbb1, hpres1⟩ :=
    windowAddr_runsTo_route shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) q0 regs leftClose hClose
  -- 2. LEFT seed leg
  obtain ⟨r2, hrun2, hacc2, hseed2, hb2, hbb2, hcl2, hri2, hpres2⟩ :=
    rankSeedLeg_runsTo_canonical shape (blockSize := (canonicalBPRelativeSummaryBlockSizeRaw shape))
      (leftClose := leftClose) q1 q2 q3 r1 hbb1
  -- 3. LEFT range preamble
  obtain ⟨r3, hrun3, hstart3, hlo3, hhi3, hpres3⟩ :=
    crossLeftRange_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q4 r2 leftClose (sbBB shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
      (by rw [hcl2, hpres1 fClose (by decide)]; exact hClose)
      (by rw [hbb2]; exact hbb1)
  -- 4. LEFT ARM
  obtain ⟨r4, hrun4, hval4, hpres4⟩ :=
    fringeArmProgramAt_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) hc q5
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose) (sbBB shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
      (crossLeftRelLo shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
      (crossLeftRelHi shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose)
      (canonicalSeed shape (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose) (leftClose + 1) hL0 hL1 hL2 r3
      (by rw [hpres3 fBase (by decide), hb2]; exact hbase1)
      hlo3 hhi3
      (by rw [hpres3 fAcc (by decide)]; exact hacc2)
      (by rw [hpres3 fBB (by decide), hbb2]; exact hbb1)
      (by rw [hpres3 fSeed (by decide)]; exact hseed2)
      hstart3
  -- 5. LEFT stash
  obtain ⟨r5, hrun5, hlv5, hlp5, hpres5⟩ := crossStashLeft_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q6 r4
  -- 6. THE INTERIOR (hypothesis)
  obtain ⟨r6, hrun6, hmid6, hcl6, hri6, hlv6, hlp6⟩ :=
    hInterior r5
      (by
        rw [hpres5 fClose (by decide), hpres4 fClose (by decide),
          hpres3 fClose (by decide), hcl2, hpres1 fClose (by decide)]
        exact hClose)
      (by
        rw [hpres5 fRight (by decide), hpres4 fRight (by decide),
          hpres3 fRight (by decide), hri2, hpres1 fRight (by decide)]
        exact hRight)
  -- 7. repoint: fClose := fRight
  obtain ⟨r7, hrun7, hcl7, hpres7⟩ := crossRepoint_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q8 r6
  have hclose7 : r7 fClose = rightClose := by
    rw [hcl7, hri6, hpres5 fRight (by decide), hpres4 fRight (by decide),
      hpres3 fRight (by decide), hri2, hpres1 fRight (by decide)]
    exact hRight
  -- 8. RIGHT window address preamble
  obtain ⟨r8, hrun8, hbase8, hbb8, hpres8⟩ :=
    windowAddr_runsTo_route shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) q9 r7 rightClose hclose7
  -- 9. RIGHT seed leg.  Its two internal hosting facts must be restated at
  -- `P + 1` / `P + 61` for `P = A + 181 + n`; with a variable `n` those are
  -- not definitionally the layout's `A + 182 + n` / `A + 242 + n`.
  have q11' : HostedAt program (A + 181 + interior.length + 1)
      (rankCloseBlock (A + 181 + interior.length + 1)
        concreteBPNativeRankCloseTraceSegmentBase
        (bpFringeChunkBits shape.bpCode.length) shape.bpCode.length
        (builtRelativeSplitBPCloseRankData shape).wordSize
        (builtRelativeSplitBPCloseRankData shape).blocksPerSuper) := by
    have h : A + 181 + interior.length + 1 = A + 182 + interior.length := by
      omega
    rw [h]
    exact q11
  have q12' : HostedAt program (A + 181 + interior.length + 61)
      rankSeedFinish := by
    have h : A + 181 + interior.length + 61 = A + 242 + interior.length := by
      omega
    rw [h]
    exact q12
  obtain ⟨r9, hrun9, hacc9, hseed9, hb9, hbb9, hcl9, hri9, hpres9⟩ :=
    rankSeedLeg_runsTo_canonical shape (blockSize := (canonicalBPRelativeSummaryBlockSizeRaw shape))
      (leftClose := rightClose) q10 q11' q12' r8 hbb8
  -- 10. RIGHT range preamble
  obtain ⟨r10, hrun10, hstart10, hlo10, hhi10, hpres10⟩ :=
    crossRightRange_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q13 r9 rightClose (sbBB shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
      (by rw [hcl9, hpres8 fClose (by decide)]; exact hclose7)
      (by rw [hbb9]; exact hbb8)
  -- 11. RIGHT ARM
  obtain ⟨r11, hrun11, hval11, hpres11⟩ :=
    fringeArmProgramAt_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) hc q14
      (sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose) (sbBB shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
      (crossRightRelLo shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
      (crossRightRelHi shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
      (canonicalSeed shape (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)
      (blockStartOf (canonicalBPRelativeSummaryBlockSizeRaw shape) (blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose)) hR0 hR1 hR2 r10
      (by rw [hpres10 fBase (by decide), hb9]; exact hbase8)
      hlo10 hhi10
      (by rw [hpres10 fAcc (by decide)]; exact hacc9)
      (by rw [hpres10 fBB (by decide), hbb9]; exact hbb8)
      (by rw [hpres10 fSeed (by decide)]; exact hseed9)
      hstart10
  -- 12. RIGHT stash
  obtain ⟨r12, hrun12, hrv12, hrp12, hpres12⟩ :=
    crossStashRight_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q15 r11
  -- 13. unit pin
  obtain ⟨r13, hrun13, hone13, hpres13⟩ := crossPinOne_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q16 r12
  -- the LEFT stash's slots survived the interior and the whole right half
  have hLV : r13 mLV = r4 fRV + 1 := by
    rw [hpres13 mLV (by decide), hpres12 mLV (by decide),
      hpres11 mLV (by decide), hpres10 mLV (by decide),
      hpres9 mLV (by decide), hpres8 mLV (by decide),
      hpres7 mLV (by decide), hlv6]
    exact hlv5
  have hLP : r13 mLP = r4 fRP := by
    rw [hpres13 mLP (by decide), hpres12 mLP (by decide),
      hpres11 mLP (by decide), hpres10 mLP (by decide),
      hpres9 mLP (by decide), hpres8 mLP (by decide),
      hpres7 mLP (by decide), hlp6]
    exact hlp5
  -- the interior's answer survived the right half
  have hMV : r13 mMV = r6 mMV := by
    rw [hpres13 mMV (by decide), hpres12 mMV (by decide),
      hpres11 mMV (by decide), hpres10 mMV (by decide),
      hpres9 mMV (by decide), hpres8 mMV (by decide),
      hpres7 mMV (by decide)]
  have hMP : r13 mMP = r6 mMP := by
    rw [hpres13 mMP (by decide), hpres12 mMP (by decide),
      hpres11 mMP (by decide), hpres10 mMP (by decide),
      hpres9 mMP (by decide), hpres8 mMP (by decide),
      hpres7 mMP (by decide)]
  -- 14. THE MERGE
  obtain ⟨r14, hrun14, _hacc14, hres14, _hpres14⟩ :=
    candMerge3_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) q17 r13 (r4 fRV) (r4 fRP) (r6 mMV) (r6 mMP)
      (r11 fRV) (r11 fRP) hone13 hLV hLP hMV hMP
      (by rw [hpres13 mRV (by decide)]; exact hrv12)
      (by rw [hpres13 mRP (by decide)]; exact hrp12)
  -- route-side identification of the three candidates
  have hleft : (crossLeftArm shape fringeSegment (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose).value =
      some (r4 fRV, r4 fRP) := by
    rw [crossLeftArm, leftArm_value_eq]
    exact hval4.symm
  have hright : (crossRightArm shape fringeSegment (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose).value =
      some (r11 fRV, r11 fRP) := by
    rw [crossRightArm, rightArm_value_eq]
    exact hval11.symm
  -- every post-hole segment's exit is renormalised to the layout's own
  -- address before composition (see `runsTo_pc_congr`)
  have n7 := runsTo_pc_congr hrun7
    (by omega : A + 176 + interior.length + 1 = A + 177 + interior.length)
  have n8 := runsTo_pc_congr hrun8
    (by omega : A + 177 + interior.length + 4 = A + 181 + interior.length)
  have n9 := runsTo_pc_congr hrun9
    (by omega : A + 181 + interior.length + 64 = A + 245 + interior.length)
  have n10 := runsTo_pc_congr hrun10
    (by omega : A + 245 + interior.length + 10 = A + 255 + interior.length)
  have n11 := runsTo_pc_congr hrun11
    (by omega : A + 255 + interior.length + 95 = A + 350 + interior.length)
  have n12 := runsTo_pc_congr hrun12
    (by omega : A + 350 + interior.length + 3 = A + 353 + interior.length)
  have n13 := runsTo_pc_congr hrun13
    (by omega : A + 353 + interior.length + 1 = A + 354 + interior.length)
  have n14 := runsTo_pc_congr hrun14
    (by omega : A + 354 + interior.length + 16 = A + 370 + interior.length)
  refine ⟨r14, ?_, ?_⟩
  · have htrans :=
      ((((((((((((hrun1.trans hrun2).trans hrun3).trans hrun4).trans
        hrun5).trans hrun6).trans n7).trans n8).trans n9).trans
        n10).trans n11).trans n12).trans n13).trans n14
    have hmc : candMerge3Cats (r4 fRV, r4 fRP) (bestOfRegs (r6 mMV) (r6 mMP))
        (r11 fRV, r11 fRP) =
        candMerge3Cats
          ((crossLeftArm shape fringeSegment (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose).value.getD (0, 0))
          interiorValue
          ((crossRightArm shape fringeSegment (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose).value.getD
            (0, 0)) := by
      rw [hleft, hright, hmid6]
      rfl
    rw [hmc] at htrans
    simpa [crossBlockArmSpec, crossBlockArmCats, crossLeftArm, crossRightArm,
      crossLeftArmCats, crossRightArmCats, crossLeftRelLo, crossLeftRelHi,
      crossRightRelLo, crossRightRelHi, sbBase, sbBB, sbChunkBits,
      canonicalSeed, fringeLeg_trace_eq_leftArm, fringeLeg_trace_eq_rightArm,
      List.append_assoc] using htrans
  · rw [hres14, hleft.symm, hright.symm, hmid6]
    simp [crossBlockArmSpec, crossLeftArm, crossRightArm, canonicalSeed]

/-! ## Remaining (NOT implemented here)

Items 1-3 of the M3d-8 list are DONE (M3d-9): both range preambles, both
stashes, the repoint, the new unit pin, and the composed
`crossBlockArmProgramAt_runsTo` over an abstract interior.  Three
structural findings came out of doing them, all recorded at their
definitions above:

* `fringeArm_runsTo` had no preservation clause; it now has one
  (`FringeArmUntouched`).
* `rankSeedLeg_runsTo_canonical` had only the four specific clauses the
  same-block leg needed; it now has a general one
  (`RankSeedLegUntouched`).
* `fOne` (40) is INSIDE the fold bank, so the arms may clobber the merge's
  unit constant.  Hence `crossPinOne`, and the layout is 370 instructions,
  not 369.

What this module still does NOT have:

1. THE INTERIOR ITSELF.  `crossBlockArmProgramAt_runsTo` takes it as
   `hInterior` and is blocked on the `Nat.log2` decision (M3d-3 section 2)
   only for its INSTANTIATION, not for its statement.  Discharging
   `hInterior` is the whole remaining cross-block obligation.
2. ANTI-VACUITY BY EXECUTION for the composed arm.  The layout's hosting
   facts are derived from one assumption (`crossBlockArmProgramAt_hosts`),
   but no concrete program has yet been RUN through the whole cross arm the
   way `armWitness_path1..7` (`E1FringeArmProgram.lean:288`) runs the
   single arm.  That needs a concrete interior to fill the hole, so it is
   downstream of item 1.
3. If the interior leg needs pinned machine inputs beyond the two query
   operands, `hInterior`'s antecedent gains those conjuncts and the proof
   gains the matching obligation to establish them at `A + 176`.  The four
   preservation clauses are unaffected either way.
4. Nothing here closes or weakens any matrix row; all of REQ-E1-01..11 are
   whole-query scoped and remain OPEN.
-/

end E1CrossBlockArm
end WordRAM
end RMQ
