import RMQ.Core.WordRAM.E1InteriorDispatch

/-! # E1 amended machine: `#9`'s FIVE ARMS COMPOSED, and `hInterior`

`E1InteriorDispatch.lean` built `#9`'s 4204-instruction program, simulated
its 28-instruction prologue in four read-free pieces, proved the selector
reaches each of the five arm bases, and decomposed the route into five
branch lemmas with no `RunsTo` in them.  What it did NOT build is the
composition: one `RunsTo` from `Q` to `Q + 4204` carrying receipt,
category log, value and preservation on every branch.

This module builds it, and then discharges `hInterior`.

## The route side is the SPINE, not a check performed afterwards

`E1_LIVE_STATE.md` §11 F: *a category function written after the machine
is a category function fitted to the machine.*  `dispatchEvents` and
`dispatchCats` below are five-way `if`s in the ROUTE's own condition
order -- `count = 0`, `count <= leftCount`, `middleMacroCount = 0`,
`rightCount = 0`, otherwise -- exactly the order
`canonicalRelativeRmmInteriorRangeMinComputation` tests them in and
exactly the order `dispatchSelector` branches on.  Each branch's body is
the corresponding sub-block's OWN receipt/charge function at the ROUTE's
own arguments.  The simulation then case-splits against
`interiorRangeMin_of_*` rather than against its own shape.

## What the composition is actually exposed to

Four of the five arms end in `brNZ wOne (dispatchJoin Q)`; `#8` is
physically last and exits by fall-through (`dispatchArm8_exit_is_join`).
So the composition's load-bearing register fact is that `wOne` (`146`)
is still nonzero after as many as 1574 instructions of sub-block have
run.  That is `crossLegUntouched_of_ge` and its two weaker twins, and it
is the reason the dispatch bank opens at `146` rather than anywhere
lower (DD-20260719-060).

## The prologue is UNCONDITIONAL, and that is what makes the arms uniform

`rangePreamble`, `indexDecomp` and `localArmSetup` all run before the
selector on every branch, so every branch's category log shares the same
19-element prefix and every branch's receipt is the arm's alone (all
three prologue pieces are read-free).  `localArmSetup` writes `#4`'s
input bank `127`-`130` unconditionally even on the branches that never
enter `#4`; that is sound because `136`-`139` and `127`-`130` are
disjoint and no arm reads the other's bank, and it is what keeps the
prologue's charge log branch-independent.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorDispatchCompose

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1Machine
open E1FringeFoldBlock (bestOfRegs)
open E1SameBlockArm (fClose fRight)
open E1CandMerge3 (mMV mMP mLV mLP)
open E1InteriorSummaryGroup (TableGeom SummaryLayout canonicalSummaryLayout)
open E1InteriorSpanBlock (localSpanGeom globalSpanGeom)
open E1InteriorTwoSpan (tA tStart tN tOff twoSpanBlock TwoSpanUntouched
  twoSpanEvents twoSpanCats twoSpanValue localLevelGeom globalLevelGeom)
open E1InteriorCombine (uMacro uLocal uMid uRight uT uZero uSV uSP vSV vSP
  twoLegBlock crossLegBlock TwoLegUntouched CrossLegUntouched twoLegCats
  crossLegCats)
open E1InteriorDispatch (wOne wT wStart wCount wRem wLeft rangePreamble
  indexDecomp localArmSetup dispatchSelector dispatchArm0
  interiorDispatchBlock armBase0 armBase4 armBase6 armBase7 armBase8
  dispatchJoin DispatchUntouched CloseLegUntouched)

/-! ## The block at the canonical instantiation

`interiorDispatchBlock` is parametric in five geometries and seven
numerals.  Every one of them is forced the moment the value clause has to
mention the route: `twoSpanValue_local_eq_routeValue` and its three
siblings are stated at the canonical geometries and at the canonical
layout's own `macroSize`/`macroSampleCount`/`levelCount`, so an
instantiation that spelled any of them differently could not be linked to
`canonicalRelativeRmmInteriorRangeMinComputation` at all.

`blockSize` and `blocksPerSuper` are likewise forced, from the other end:
the sub-blocks' `runsTo` theorems are stated at
`(RelativeRmm.canonicalLayout shape).blockSize` specifically.  That is
also the route's own `canonicalBPRelativeSummaryBlockSizeRaw shape` --
DEFINITIONALLY, `RelativeSummary.lean:1278`, so no bridge is needed and
none is written here. -/
def canonicalInteriorDispatchBlock (shape : Cartesian.CartesianShape)
    (Q : Nat) : List Instr :=
  interiorDispatchBlock (canonicalSummaryLayout shape)
    (localLevelGeom shape) (localSpanGeom shape)
    (globalLevelGeom shape) (globalSpanGeom shape)
    (RelativeRmm.canonicalLayout shape).macroSize
    (RelativeRmm.canonicalLayout shape).macroSampleCount
    ((RelativeRmm.canonicalLayout shape).levelCount *
      (RelativeRmm.canonicalLayout shape).macroSize)
    (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
    (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSampleCount)
    (RelativeRmm.canonicalLayout shape).blockSize
    (RelativeRmm.canonicalLayout shape).blocksPerSuper Q

@[simp] theorem canonicalInteriorDispatchBlock_length
    (shape : Cartesian.CartesianShape) (Q : Nat) :
    (canonicalInteriorDispatchBlock shape Q).length = 4204 := by
  simp [canonicalInteriorDispatchBlock]

/-! ## The two sub-leg shapes, named once

Every arm of `#9` is built from at most three two-span legs, and each leg
is either LOCAL (level table indexed by `macroIdx`, block offset
`macroIdx * macroSize`) or GLOBAL (slot base `0`, block offset `0`).
Naming the two shapes keeps `dispatchEvents`/`dispatchCats` legible and,
more importantly, keeps them spelled EXACTLY as the value-link theorems
spell them, so no reassociation or re-spelling step is needed at the
composition. -/

/-- A LOCAL two-span leg's receipt, at macro block `macroIdx`. -/
def localLegEvents (shape : Cartesian.CartesianShape)
    (macroIdx start n : Nat) : List WordRAM.TraceEvent :=
  twoSpanEvents shape (localLevelGeom shape) (localSpanGeom shape)
    (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
      (RelativeRmm.canonicalLayout shape).macroSize))
    (RelativeRmm.canonicalLayout shape).macroSize
    (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
    start n (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize)

/-- A LOCAL two-span leg's charge log. -/
def localLegCats (shape : Cartesian.CartesianShape)
    (macroIdx start n : Nat) : List Category :=
  twoSpanCats shape (localLevelGeom shape) (localSpanGeom shape)
    (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
      (RelativeRmm.canonicalLayout shape).macroSize))
    (RelativeRmm.canonicalLayout shape).macroSize
    (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
    start n (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize)

/-- A LOCAL two-span leg's value. -/
def localLegValue (shape : Cartesian.CartesianShape)
    (macroIdx start n : Nat) : Option (Nat × Nat) :=
  twoSpanValue shape (localLevelGeom shape) (localSpanGeom shape)
    (macroIdx * ((RelativeRmm.canonicalLayout shape).levelCount *
      (RelativeRmm.canonicalLayout shape).macroSize))
    (RelativeRmm.canonicalLayout shape).macroSize
    (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
    start n (macroIdx * (RelativeRmm.canonicalLayout shape).macroSize)

/-- A GLOBAL two-span leg's receipt.  Slot base and block offset are both
`0`; the block spells them `(macroStart + 1) * 0`, which REDUCES to `0`
(`Nat.mul` recurses on its second argument) -- so the two are defeq and
only `rw`'s syntactic matching ever needs `Nat.mul_zero`. -/
def globalLegEvents (shape : Cartesian.CartesianShape)
    (start n : Nat) : List WordRAM.TraceEvent :=
  twoSpanEvents shape (globalLevelGeom shape) (globalSpanGeom shape) 0
    (RelativeRmm.canonicalLayout shape).macroSampleCount
    (bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    start n 0

/-- A GLOBAL two-span leg's charge log. -/
def globalLegCats (shape : Cartesian.CartesianShape)
    (start n : Nat) : List Category :=
  twoSpanCats shape (globalLevelGeom shape) (globalSpanGeom shape) 0
    (RelativeRmm.canonicalLayout shape).macroSampleCount
    (bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    start n 0

/-- A GLOBAL two-span leg's value. -/
def globalLegValue (shape : Cartesian.CartesianShape)
    (start n : Nat) : Option (Nat × Nat) :=
  twoSpanValue shape (globalLevelGeom shape) (globalSpanGeom shape) 0
    (RelativeRmm.canonicalLayout shape).macroSampleCount
    (bpSparseLevelDomain
      (RelativeRmm.canonicalLayout shape).macroSampleCount)
    start n 0

/-! ## THE RECEIPT AND THE CHARGE LOG, WRITTEN FROM THE ROUTE

Both are five-way `if`s in the route's own condition order.  The three
derived quantities `macroStart`, `localStart` and `leftCount` are spelled
out at every use rather than bound by a `let`, because the route lemmas
`interiorRangeMin_of_*` spell them out too and a `let` here would put a
delta step between the two at every leaf. -/

/-- `#9`'s RECEIPT.  The prologue and the selector are read-free, so the
whole receipt is the selected arm's -- and on the `count = 0` arm it is
empty, which is exactly the fact
`unterminatedDispatch_falls_through`'s real-layout scope note turns on:
a fall-through out of this arm lands on `twoSpanBlock`'s unconditional
head level read, so the receipt DOES separate the correct layout from the
unterminated one at the real block, even though it cannot at the witness
fixture. -/
def dispatchEvents (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) : List WordRAM.TraceEvent :=
  if count = 0 then []
  else if count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize then
    localLegEvents shape
      (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
      (startBlock % (RelativeRmm.canonicalLayout shape).macroSize) count
  else if (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
      (RelativeRmm.canonicalLayout shape).macroSize = 0 then
    localLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize) ++
      localLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1) 0
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
          (RelativeRmm.canonicalLayout shape).macroSize)
  else if (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
      (RelativeRmm.canonicalLayout shape).macroSize = 0 then
    localLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize) ++
      globalLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
          (RelativeRmm.canonicalLayout shape).macroSize)
  else
    localLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize) ++
      globalLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
          (RelativeRmm.canonicalLayout shape).macroSize) ++
      localLegEvents shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1 +
          (count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
            (RelativeRmm.canonicalLayout shape).macroSize) 0
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
          (RelativeRmm.canonicalLayout shape).macroSize)

/-- The 19 categories of `#9`'s unconditional prologue, in the three
pieces the three simulations produce them in.  Branch-independent by
construction: all three pieces run before the selector on every input. -/
def dispatchPrologueCats : List Category :=
  [Category.registerWrite, Category.arithmetic, Category.arithmetic,
      Category.arithmetic, Category.arithmetic, Category.arithmetic] ++
    ([Category.arithmetic, Category.arithmetic, Category.arithmetic,
        Category.registerWrite, Category.arithmetic, Category.arithmetic,
        Category.arithmetic, Category.arithmetic, Category.arithmetic] ++
      [Category.arithmetic, Category.registerWrite, Category.registerWrite,
        Category.arithmetic])

/-- The SELECTOR's own charge log on each branch, then the arm's, then
the arm's terminator.  `#8` has no terminator, which is
`dispatchArm8_exit_is_join`, so its branch alone ends without a trailing
`Category.branch`. -/
def dispatchArmCats (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) : List Category :=
  if count = 0 then
    [Category.branch, Category.branch] ++
      ([Category.registerWrite] ++ [Category.branch])
  else if count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize then
    [Category.branch, Category.comparison, Category.branch] ++
      (localLegCats shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          count ++
        [Category.branch])
  else if (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
      (RelativeRmm.canonicalLayout shape).macroSize = 0 then
    [Category.branch, Category.comparison, Category.branch,
        Category.branch, Category.branch] ++
      (twoLegCats
          (localLegCats shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
          (localLegCats shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1) 0
            ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize))
          (localLegValue shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
          (localLegValue shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1) 0
            ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize)) ++
        [Category.branch])
  else if (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
      (RelativeRmm.canonicalLayout shape).macroSize = 0 then
    [Category.branch, Category.comparison, Category.branch,
        Category.branch, Category.branch, Category.branch] ++
      (twoLegCats
          (localLegCats shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
          (globalLegCats shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
            ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize))
          (localLegValue shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
          (globalLegValue shape
            (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
            ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize)) ++
        [Category.branch])
  else
    [Category.branch, Category.comparison, Category.branch,
        Category.branch, Category.branch, Category.branch] ++
      crossLegCats
        (localLegCats shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
        (globalLegCats shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
          ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
            (RelativeRmm.canonicalLayout shape).macroSize))
        (localLegCats shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1 +
            (count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize) 0
          ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
            (RelativeRmm.canonicalLayout shape).macroSize))
        (localLegValue shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
          (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
        (globalLegValue shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
          ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
            (RelativeRmm.canonicalLayout shape).macroSize))
        (localLegValue shape
          (startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1 +
            (count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize) 0
          ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
            (RelativeRmm.canonicalLayout shape).macroSize))

/-- `#9`'s whole charge log: the branch-independent prologue, then the
branch's own. -/
def dispatchCats (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) : List Category :=
  dispatchPrologueCats ++ dispatchArmCats shape startBlock count

/-- The route's answer at the canonical store, named once so the value
clause below reads as an equation between the machine and the route
rather than as a wall of projections. -/
def dispatchRouteValue (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) : Option (Nat × Nat) :=
  ((canonicalRelativeRmmInteriorRangeMinComputation shape startBlock
        count).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore
        (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape).segment)).value

/-! ## Hosting, peeled once

Mirrors `crossBlockArmProgramAt_hosts`.  Each arm's BODY and its
TERMINATOR are separated here, because the terminator's fetch is the one
fact the composition needs at a numeral PC and the body's is a
`HostedAt` at a base that must equal the base passed to the
position-dependent constructor.  `#8` has a body and no terminator. -/
theorem canonicalInteriorDispatchBlock_hosts
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {Q : Nat} (hHost : HostedAt program Q
      (canonicalInteriorDispatchBlock shape Q)) :
    HostedAt program Q
        (rangePreamble (RelativeRmm.canonicalLayout shape).blockSize) ∧
      HostedAt program (Q + 6)
        (indexDecomp (RelativeRmm.canonicalLayout shape).macroSize) ∧
      HostedAt program (Q + 15)
        (localArmSetup (RelativeRmm.canonicalLayout shape).macroSize
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)) ∧
      HostedAt program (Q + 19) (dispatchSelector Q) ∧
      HostedAt program (Q + 28) (dispatchArm0 Q) ∧
      HostedAt program (Q + 30)
        (twoSpanBlock (canonicalSummaryLayout shape) (localLevelGeom shape)
          (localSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 30)) ∧
      program[Q + 539]? = some (Instr.brNZ wOne (dispatchJoin Q)) ∧
      HostedAt program (Q + 540)
        (twoLegBlock (canonicalSummaryLayout shape) (localLevelGeom shape)
          (localSpanGeom shape) (localLevelGeom shape) (localSpanGeom shape)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize uZero uRight
          (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 540)) ∧
      program[Q + 1584]? = some (Instr.brNZ wOne (dispatchJoin Q)) ∧
      HostedAt program (Q + 1585)
        (twoLegBlock (canonicalSummaryLayout shape) (localLevelGeom shape)
          (localSpanGeom shape) (globalLevelGeom shape) (globalSpanGeom shape)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount)
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize 0 0 uT uMid
          (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1585)) ∧
      program[Q + 2629]? = some (Instr.brNZ wOne (dispatchJoin Q)) ∧
      HostedAt program (Q + 2630)
        (crossLegBlock (canonicalSummaryLayout shape) (localLevelGeom shape)
          (localSpanGeom shape) (globalLevelGeom shape) (globalSpanGeom shape)
          (localLevelGeom shape) (localSpanGeom shape)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize 0 0
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize uT uMid
          (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 2630)) := by
  rw [canonicalInteriorDispatchBlock, interiorDispatchBlock] at hHost
  have hPre := hHost.append_left
  have hR1 := hHost.append_right
    (code₁ := rangePreamble (RelativeRmm.canonicalLayout shape).blockSize)
  rw [show Q + (rangePreamble
      (RelativeRmm.canonicalLayout shape).blockSize).length = Q + 6 from by
    simp] at hR1
  have hIdx := hR1.append_left
  have hR2 := hR1.append_right
    (code₁ := indexDecomp (RelativeRmm.canonicalLayout shape).macroSize)
  rw [show Q + 6 + (indexDecomp
      (RelativeRmm.canonicalLayout shape).macroSize).length = Q + 15 from by
    simp] at hR2
  have hSetup := hR2.append_left
  have hR3 := hR2.append_right
    (code₁ := localArmSetup (RelativeRmm.canonicalLayout shape).macroSize
      ((RelativeRmm.canonicalLayout shape).levelCount *
        (RelativeRmm.canonicalLayout shape).macroSize))
  rw [show Q + 15 + (localArmSetup
      (RelativeRmm.canonicalLayout shape).macroSize
      ((RelativeRmm.canonicalLayout shape).levelCount *
        (RelativeRmm.canonicalLayout shape).macroSize)).length
      = Q + 19 from by simp] at hR3
  have hSel := hR3.append_left
  have hR4 := hR3.append_right (code₁ := dispatchSelector Q)
  rw [show Q + 19 + (dispatchSelector Q).length = Q + 28 from by
    simp] at hR4
  have hArm0 := hR4.append_left
  have hR5 := hR4.append_right (code₁ := dispatchArm0 Q)
  rw [show Q + 28 + (dispatchArm0 Q).length = Q + 30 from by
    simp] at hR5
  have hA4 := hR5.append_left
  have hR6 := hR5.append_right
    (code₁ := twoSpanBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 30) ++
      [Instr.brNZ wOne (dispatchJoin Q)])
  rw [show Q + 30 + (twoSpanBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 30) ++
      [Instr.brNZ wOne (dispatchJoin Q)]).length = Q + 540 from by
    simp] at hR6
  have hA6 := hR6.append_left
  have hR7 := hR6.append_right
    (code₁ := twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (localLevelGeom shape)
        (localSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize uZero uRight
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 540) ++
      [Instr.brNZ wOne (dispatchJoin Q)])
  rw [show Q + 540 + (twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (localLevelGeom shape)
        (localSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize uZero uRight
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 540) ++
      [Instr.brNZ wOne (dispatchJoin Q)]).length = Q + 1585 from by
    simp] at hR7
  have hA7 := hR7.append_left
  have hA8 := hR7.append_right
    (code₁ := twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (globalLevelGeom shape)
        (globalSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize 0 0 uT uMid
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1585) ++
      [Instr.brNZ wOne (dispatchJoin Q)])
  rw [show Q + 1585 + (twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (globalLevelGeom shape)
        (globalSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize 0 0 uT uMid
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1585) ++
      [Instr.brNZ wOne (dispatchJoin Q)]).length = Q + 2630 from by
    simp] at hA8
  refine ⟨hPre, hIdx, hSetup, hSel, hArm0, hA4.append_left, ?_,
    hA6.append_left, ?_, hA7.append_left, ?_, hA8⟩
  · have h := hA4.append_right
      (code₁ := twoSpanBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 30))
    rw [show Q + 30 + (twoSpanBlock (canonicalSummaryLayout shape)
          (localLevelGeom shape) (localSpanGeom shape)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 30)).length = Q + 539 from by simp] at h
    simpa using h.head
  · have h := hA6.append_right
      (code₁ := twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (localLevelGeom shape)
        (localSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize uZero uRight
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 540))
    rw [show Q + 540 + (twoLegBlock (canonicalSummaryLayout shape)
          (localLevelGeom shape) (localSpanGeom shape) (localLevelGeom shape)
          (localSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize uZero uRight
          (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 540)).length = Q + 1584 from by simp] at h
    simpa using h.head
  · have h := hA7.append_right
      (code₁ := twoLegBlock (canonicalSummaryLayout shape)
        (localLevelGeom shape) (localSpanGeom shape) (globalLevelGeom shape)
        (globalSpanGeom shape) (RelativeRmm.canonicalLayout shape).macroSize
        (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSampleCount
        (bpSparseLevelDomain
          (RelativeRmm.canonicalLayout shape).macroSampleCount)
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)
        (RelativeRmm.canonicalLayout shape).macroSize 0 0 uT uMid
        (RelativeRmm.canonicalLayout shape).macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1585))
    rw [show Q + 1585 + (twoLegBlock (canonicalSummaryLayout shape)
          (localLevelGeom shape) (localSpanGeom shape) (globalLevelGeom shape)
          (globalSpanGeom shape)
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount)
          ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize)
          (RelativeRmm.canonicalLayout shape).macroSize 0 0 uT uMid
          (RelativeRmm.canonicalLayout shape).macroSize
          (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper
          (Q + 1585)).length = Q + 2629 from by simp] at h
    simpa using h.head

/-! ## The two span geometries' positivity

`E1InteriorSpanBlock` exports `localSpanGeom_cap`/`globalSpanGeom_cap` but
not their positivity twins -- `spanBlock_runsTo` needs both, and the two
were supplied at its call sites from `E1InteriorChunkCap` directly.  Named
here so the four cap/positivity arguments the arms need read uniformly. -/
theorem localSpanGeom_pos (shape : Cartesian.CartesianShape) :
    0 < (localSpanGeom shape).chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_offsetWidth shape

theorem globalSpanGeom_pos (shape : Cartesian.CartesianShape) :
    0 < (globalSpanGeom shape).chunkCount :=
  E1InteriorChunkCap.chunkCount_pos_blockAddressWidth shape

/-! ## `mMV` survives the dispatch's own predicate

Needed by the `count = 0` arm, whose whole content is a write to `mMV`:
the preservation clause has to see past that write, and `DispatchUntouched`
already excludes `77` -- through `CrossLegUntouched`, `TwoLegUntouched` and
`MergeUntouched`, four abbrevs down.  Named rather than projected inline at
each use, because a four-deep anonymous projection is exactly the kind of
term that keeps typechecking after the predicate underneath it changes. -/
theorem dispatchUntouched_ne_mMV {r : Nat} (h : DispatchUntouched r) :
    r ≠ mMV := h.1.1.2.1.1

/-! ## THE UNCONDITIONAL PROLOGUE, COMPOSED

`rangePreamble`, `indexDecomp` and `localArmSetup` run on every branch, so
this composes once and every arm below reuses it.  All three are
read-free, which is why `#9`'s whole receipt is the selected arm's.

The twelve register readings exported here are exactly the ones the five
arms consume: `wOne`/`wCount`/`wLeft`/`uMid`/`uRight` for the selector,
`uMacro`/`uLocal`/`uMid`/`uRight` for the three combiners, and
`tA`/`tStart`/`tN`/`tOff` for `#4`.  `wStart` is deliberately NOT exported:
nothing after the index decomposition reads it, and exporting a reading no
consumer needs is how a decorative hypothesis gets carried. -/
theorem dispatchPrologue_runsTo (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {Q : Nat} (regs : RegFile)
    (leftClose rightClose startBlock count : Nat)
    (hPre : HostedAt program Q
      (rangePreamble (RelativeRmm.canonicalLayout shape).blockSize))
    (hIdx : HostedAt program (Q + 6)
      (indexDecomp (RelativeRmm.canonicalLayout shape).macroSize))
    (hSetup : HostedAt program (Q + 15)
      (localArmSetup (RelativeRmm.canonicalLayout shape).macroSize
        ((RelativeRmm.canonicalLayout shape).levelCount *
          (RelativeRmm.canonicalLayout shape).macroSize)))
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hSB : startBlock =
      leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
    (hCT : count =
      rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
        leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 19, false⟩ [] dispatchPrologueCats ∧
        regs' wOne = 1 ∧
        regs' wCount = count ∧
        regs' wLeft = (RelativeRmm.canonicalLayout shape).macroSize -
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' uMacro =
          startBlock / (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' uLocal =
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' uMid =
          (count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
            (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' uRight =
          (count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
            (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' tA =
          startBlock / (RelativeRmm.canonicalLayout shape).macroSize *
            ((RelativeRmm.canonicalLayout shape).levelCount *
              (RelativeRmm.canonicalLayout shape).macroSize) ∧
        regs' tStart =
          startBlock % (RelativeRmm.canonicalLayout shape).macroSize ∧
        regs' tN = count ∧
        regs' tOff =
          startBlock / (RelativeRmm.canonicalLayout shape).macroSize *
            (RelativeRmm.canonicalLayout shape).macroSize ∧
        (∀ r, DispatchUntouched r → regs' r = regs r) := by
  subst hSB
  subst hCT
  obtain ⟨r1, hrun1, hone1, hstart1, hcount1, hpres1⟩ :=
    E1InteriorDispatch.rangePreamble_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hPre regs
      leftClose rightClose hClose hRight
  obtain ⟨r2, hrun2, hmacro2, hlocal2, hleft2, hmid2, hright2, hcount2,
    hpres2⟩ :=
    E1InteriorDispatch.indexDecomp_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hIdx r1 _ _
      hstart1 hcount1
  obtain ⟨r3, hrun3, hta3, htst3, htn3, htoff3, hpres3⟩ :=
    E1InteriorDispatch.localArmSetup_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSetup r2 _ _ _
      hmacro2 hlocal2 hcount2
  rw [show Q + 6 + 9 = Q + 15 from by omega] at hrun2
  rw [show Q + 15 + 4 = Q + 19 from by omega] at hrun3
  refine ⟨r3, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hta3, htst3, htn3, htoff3, ?_⟩
  · have h := hrun1.trans (hrun2.trans hrun3)
    exact h
  · rw [hpres3 wOne (by decide) (by decide) (by decide) (by decide),
      hpres2 wOne (by decide) (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide)]
    exact hone1
  · rw [hpres3 wCount (by decide) (by decide) (by decide) (by decide)]
    exact hcount2
  · rw [hpres3 wLeft (by decide) (by decide) (by decide) (by decide)]
    exact hleft2
  · rw [hpres3 uMacro (by decide) (by decide) (by decide) (by decide)]
    exact hmacro2
  · rw [hpres3 uLocal (by decide) (by decide) (by decide) (by decide)]
    exact hlocal2
  · rw [hpres3 uMid (by decide) (by decide) (by decide) (by decide)]
    exact hmid2
  · rw [hpres3 uRight (by decide) (by decide) (by decide) (by decide)]
    exact hright2
  · intro r hr
    obtain ⟨-, h127, h128, h129, h130, h136, h137, h138, h139, h146, h147,
      h148, h149, h150, h151⟩ := hr
    rw [hpres3 r h127 h128 h129 h130,
      hpres2 r h136 h137 h138 h139 h147 h151 h150,
      hpres1 r h146 h147 h148 h149 h150]

/-! ## THE FIVE ARMS, COMPOSED

The whole deliverable of this module.  The case split is on the ROUTE's
four conditions, taken in the route's own order, and each leaf cites the
matching `interiorRangeMin_of_*` for its value clause rather than
re-deriving which sub-computation the route selects.

**What the preservation clause is doing here.**  `DispatchUntouched` was
enumerated from `#9`'s OWN write set rather than inherited from a
sub-block, because `TwoSpanUntouched` and `TwoLegUntouched` each omit a
bank that `#9`'s prologue WRITES (`127`-`130` and `136`-`139`
respectively) and inheriting either would state a false clause here.  Each
arm below discharges its sub-block's predicate by PROJECTION out of
`DispatchUntouched` -- `hr.1.1.1` for `TwoSpanUntouched`, `hr.1.1` for
`TwoLegUntouched`, `hr.1` for `CrossLegUntouched` -- so the dispatch's
predicate is the strictly stronger one and the direction of the
implication is checked by the elaborator on every arm.

**The register fact every arm turns on** is that `wOne` is still `1` at
the arm's trailing branch, after up to 1574 instructions of sub-block.
That is `twoSpanUntouched_of_ge`, `twoLegUntouched_of_ge` and
`crossLegUntouched_of_ge` at `146`, and it is why the dispatch bank cannot
open lower (DD-20260719-060).  `#8` needs no such step, because it has no
trailing branch: it is physically last and
`dispatchArm8_exit_is_join` is the whole of its exit argument. -/
theorem interiorDispatchBlock_runsTo (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {Q : Nat} (regs : RegFile)
    (leftClose rightClose startBlock count : Nat)
    (hHost : HostedAt program Q (canonicalInteriorDispatchBlock shape Q))
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hSB : startBlock =
      leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
    (hCT : count =
      rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
        leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 4204, false⟩
          (dispatchEvents shape startBlock count)
          (dispatchCats shape startBlock count) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          dispatchRouteValue shape startBlock count ∧
        (∀ r, DispatchUntouched r → regs' r = regs r) := by
  obtain ⟨hPre, hIdx, hSetup, hSel, hArm0, hA4, hT4, hA6, hT6, hA7, hT7,
    hA8⟩ := canonicalInteriorDispatchBlock_hosts shape hHost
  obtain ⟨p, hrunP, hone, hcount, hleft, hmacro, hlocal, hmid, hright,
    hta, htst, htn, htoff, hpresP⟩ :=
    dispatchPrologue_runsTo shape regs leftClose rightClose startBlock count
      hPre hIdx hSetup hClose hRight hSB hCT
  simp only [dispatchCats, dispatchEvents, dispatchArmCats,
    dispatchRouteValue]
  by_cases hc0 : count = 0
  · -- ## ARM `#0`: `pure none`
    subst hc0
    simp only [reduceIte]
    have hsel := E1InteriorDispatch.dispatchSelector_reaches_arm0
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSel p hcount hone
    simp only [E1InteriorDispatch.armBase0] at hsel
    have hf0 : program[Q + 28]? = some (Instr.const mMV 0) := by
      simpa using hArm0.head
    have hf1 : program[Q + 29]? =
        some (Instr.brNZ wOne (E1InteriorDispatch.dispatchJoin Q)) := by
      have h := hArm0.tail.head
      rw [show Q + 28 + 1 = Q + 29 from by omega] at h
      simpa using h
    have s0 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        program ⟨p, Q + 28, false⟩ ⟨p.write mMV 0, Q + 29, false⟩ []
        [Category.registerWrite] := by
      have h := RunsTo.const
        (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (s := (⟨p, Q + 28, false⟩ : State)) rfl hf0
      simpa using h
    have hcond : (p.write mMV 0) wOne ≠ 0 := by
      rw [RegFile.write_other _ _ (by decide), hone]
      omega
    have s1 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        program ⟨p.write mMV 0, Q + 29, false⟩
        ⟨p.write mMV 0, Q + 4204, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken
        (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (s := (⟨p.write mMV 0, Q + 29, false⟩ : State)) rfl hf1 hcond
      simpa using h
    refine ⟨p.write mMV 0, hrunP.trans (hsel.trans (s0.trans s1)), ?_, ?_⟩
    · rw [E1InteriorDispatch.interiorRangeMin_of_count_zero shape startBlock]
      rw [RegFile.write_same]
      rfl
    · intro r hr
      rw [RegFile.write_other _ _ (dispatchUntouched_ne_mMV hr)]
      exact hpresP r hr
  · by_cases hle : count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize
    · -- ## ARM `#4`: the local two-span leg
      simp only [if_neg hc0, if_pos hle, localLegEvents, localLegCats]
      have hsel := E1InteriorDispatch.dispatchSelector_reaches_arm4
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSel p count
        _ hcount hleft hc0 hle
      simp only [E1InteriorDispatch.armBase4] at hsel
      obtain ⟨q, hrunA, hval, hpres⟩ :=
        E1InteriorTwoSpan.twoSpanBlock_runsTo shape
          (regs := p.write wT 1)
          (A := startBlock / (RelativeRmm.canonicalLayout shape).macroSize *
            ((RelativeRmm.canonicalLayout shape).levelCount *
              (RelativeRmm.canonicalLayout shape).macroSize))
          (start := startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
          (n := count)
          (off := startBlock / (RelativeRmm.canonicalLayout shape).macroSize *
            (RelativeRmm.canonicalLayout shape).macroSize) hA4
          (by rw [RegFile.write_other _ _ (by decide)]; exact hta)
          (by rw [RegFile.write_other _ _ (by decide)]; exact htst)
          (by rw [RegFile.write_other _ _ (by decide)]; exact htn)
          (by rw [RegFile.write_other _ _ (by decide)]; exact htoff)
          (E1InteriorTwoSpan.localLevelGeom_pos shape)
          (E1InteriorTwoSpan.localLevelGeom_cap shape)
          (localSpanGeom_pos shape)
          (E1InteriorSpanBlock.localSpanGeom_cap shape)
      rw [show Q + 30 + 509 = Q + 539 from by omega] at hrunA
      have hcond : q wOne ≠ 0 := by
        rw [hpres wOne (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
          RegFile.write_other _ _ (by decide), hone]
        omega
      have s : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          program ⟨q, Q + 539, false⟩ ⟨q, Q + 4204, false⟩ []
          [Category.branch] := by
        have h := RunsTo.brNZ_taken
          (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (s := (⟨q, Q + 539, false⟩ : State)) rfl hT4 hcond
        simpa using h
      have hfin := hrunP.trans (hsel.trans (hrunA.trans s))
      rw [List.append_nil] at hfin
      refine ⟨q, hfin, ?_, ?_⟩
      · rw [hval, E1InteriorDispatch.interiorRangeMin_of_local shape
          startBlock count hc0 hle]
        exact E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue shape _ _ _
      · intro r hr
        obtain ⟨hcross, h127, h128, h129, h130, h136, h137, h138, h139,
          h146, h147, h148, h149, h150, h151⟩ := hr
        rw [hpres r hcross.1.1, RegFile.write_other _ _ h147]
        exact hpresP r ⟨hcross, h127, h128, h129, h130, h136, h137, h138,
          h139, h146, h147, h148, h149, h150, h151⟩
    · by_cases hmid0 :
          (count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize = 0
      · -- ## ARM `#6`: adjacent macro blocks
        simp only [if_neg hc0, if_neg hle, if_pos hmid0, localLegEvents,
          localLegCats, localLegValue]
        have hsel := E1InteriorDispatch.dispatchSelector_reaches_arm6
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSel p count
          _ hcount hleft hone (by rw [hmid]; exact hmid0) hc0 hle
        simp only [E1InteriorDispatch.armBase6] at hsel
        obtain ⟨q, hrunA, hval, hpres⟩ :=
          E1InteriorCombine.twoLegBlock_runsTo shape
            (regs := p.write wT 0)
            (macroStart :=
              startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
            (localStart :=
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
            (mid := (count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
              (RelativeRmm.canonicalLayout shape).macroSize)
            (right := (count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize)
            (start2 := 0)
            (n2 := (count - ((RelativeRmm.canonicalLayout shape).macroSize -
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
              (RelativeRmm.canonicalLayout shape).macroSize) hA6
            (by rw [RegFile.write_other _ _ (by decide)]; exact hmacro)
            (by rw [RegFile.write_other _ _ (by decide)]; exact hlocal)
            (by rw [RegFile.write_other _ _ (by decide)]; exact hmid)
            (by rw [RegFile.write_other _ _ (by decide)]; exact hright)
            (by decide) (by decide)
            (E1InteriorCombine.adjacentMacro_src_witnesses _ _ _ _).1
            (E1InteriorCombine.adjacentMacro_src_witnesses _ _ _ _).2
            (E1InteriorTwoSpan.localLevelGeom_pos shape)
            (E1InteriorTwoSpan.localLevelGeom_cap shape)
            (localSpanGeom_pos shape)
            (E1InteriorSpanBlock.localSpanGeom_cap shape)
            (E1InteriorTwoSpan.localLevelGeom_pos shape)
            (E1InteriorTwoSpan.localLevelGeom_cap shape)
            (localSpanGeom_pos shape)
            (E1InteriorSpanBlock.localSpanGeom_cap shape)
        rw [show Q + 540 + 1044 = Q + 1584 from by omega] at hrunA
        have hcond : q wOne ≠ 0 := by
          rw [hpres wOne (E1InteriorCombine.twoLegUntouched_of_ge (by decide)),
            RegFile.write_other _ _ (by decide), hone]
          omega
        have s : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            program ⟨q, Q + 1584, false⟩ ⟨q, Q + 4204, false⟩ []
            [Category.branch] := by
          have h := RunsTo.brNZ_taken
            (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (s := (⟨q, Q + 1584, false⟩ : State)) rfl hT6 hcond
          simpa using h
        have hfin := hrunP.trans (hsel.trans (hrunA.trans s))
        rw [List.append_nil] at hfin
        refine ⟨q, hfin, ?_, ?_⟩
        · rw [hval, E1InteriorDispatch.interiorRangeMin_of_adjacent shape
            startBlock count hc0 hle hmid0]
          exact E1InteriorCombine.twoLegValue_adjacentMacro_eq_routeValue
            shape _ _ _
        · intro r hr
          obtain ⟨hcross, h127, h128, h129, h130, h136, h137, h138, h139,
            h146, h147, h148, h149, h150, h151⟩ := hr
          rw [hpres r hcross.1, RegFile.write_other _ _ h147]
          exact hpresP r ⟨hcross, h127, h128, h129, h130, h136, h137, h138,
            h139, h146, h147, h148, h149, h150, h151⟩
      · by_cases hr0 :
            (count - ((RelativeRmm.canonicalLayout shape).macroSize -
              startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize = 0
        · -- ## ARM `#7`: left macro plus whole middle macros
          simp only [if_neg hc0, if_neg hle, if_neg hmid0, if_pos hr0,
            localLegEvents, localLegCats, localLegValue, globalLegEvents,
            globalLegCats, globalLegValue]
          have hsel := E1InteriorDispatch.dispatchSelector_reaches_arm7
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSel p count
            _ hcount hleft hone (by rw [hmid]; exact hmid0)
            (by rw [hright]; exact hr0) hc0 hle
          simp only [E1InteriorDispatch.armBase7] at hsel
          obtain ⟨q, hrunA, hval, hpres⟩ :=
            E1InteriorCombine.twoLegBlock_runsTo shape
              (regs := p.write wT 0)
              (macroStart :=
                startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (localStart :=
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              (mid := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              (right := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize)
              (start2 :=
                startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
              (n2 := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize) hA7
              (by rw [RegFile.write_other _ _ (by decide)]; exact hmacro)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hlocal)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hmid)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hright)
              (by decide) (by decide)
              (E1InteriorCombine.leftMiddleMacro_src_witnesses _ _ _ _).1
              (E1InteriorCombine.leftMiddleMacro_src_witnesses _ _ _ _).2
              (E1InteriorTwoSpan.localLevelGeom_pos shape)
              (E1InteriorTwoSpan.localLevelGeom_cap shape)
              (localSpanGeom_pos shape)
              (E1InteriorSpanBlock.localSpanGeom_cap shape)
              (E1InteriorTwoSpan.globalLevelGeom_pos shape)
              (E1InteriorTwoSpan.globalLevelGeom_cap shape)
              (globalSpanGeom_pos shape)
              (E1InteriorSpanBlock.globalSpanGeom_cap shape)
          rw [show Q + 1585 + 1044 = Q + 2629 from by omega] at hrunA
          have hcond : q wOne ≠ 0 := by
            rw [hpres wOne
                (E1InteriorCombine.twoLegUntouched_of_ge (by decide)),
              RegFile.write_other _ _ (by decide), hone]
            omega
          have s : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              program ⟨q, Q + 2629, false⟩ ⟨q, Q + 4204, false⟩ []
              [Category.branch] := by
            have h := RunsTo.brNZ_taken
              (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (s := (⟨q, Q + 2629, false⟩ : State)) rfl hT7 hcond
            simpa using h
          have hfin := hrunP.trans (hsel.trans (hrunA.trans s))
          rw [List.append_nil] at hfin
          refine ⟨q, hfin, ?_, ?_⟩
          · rw [hval, E1InteriorDispatch.interiorRangeMin_of_leftMiddle shape
              startBlock count hc0 hle hmid0 hr0]
            exact
              E1InteriorCombine.twoLegValue_leftMiddleMacro_eq_routeValue
                shape _ _ _
          · intro r hr
            obtain ⟨hcross, h127, h128, h129, h130, h136, h137, h138, h139,
              h146, h147, h148, h149, h150, h151⟩ := hr
            rw [hpres r hcross.1, RegFile.write_other _ _ h147]
            exact hpresP r ⟨hcross, h127, h128, h129, h130, h136, h137, h138,
              h139, h146, h147, h148, h149, h150, h151⟩
        · -- ## ARM `#8`: the three-leg cross-macro combiner, NO terminator
          simp only [if_neg hc0, if_neg hle, if_neg hmid0, if_neg hr0,
            localLegEvents, localLegCats, localLegValue, globalLegEvents,
            globalLegCats, globalLegValue]
          have hsel := E1InteriorDispatch.dispatchSelector_reaches_arm8
            (concreteBPNativeSuccinctRMQGlobalReadStore shape) hSel p count
            _ hcount hleft hone (by rw [hmid]; exact hmid0)
            (by rw [hright]; exact hr0) hc0 hle
          simp only [E1InteriorDispatch.armBase8] at hsel
          obtain ⟨q, hrunA, hval, hpres⟩ :=
            E1InteriorCombine.crossLegBlock_runsTo shape
              (regs := p.write wT 0)
              (macroStart :=
                startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
              (localStart :=
                startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
              (mid := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize)
              (right := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) %
                (RelativeRmm.canonicalLayout shape).macroSize)
              (start2 :=
                startBlock / (RelativeRmm.canonicalLayout shape).macroSize + 1)
              (n2 := (count -
                  ((RelativeRmm.canonicalLayout shape).macroSize -
                    startBlock %
                      (RelativeRmm.canonicalLayout shape).macroSize)) /
                (RelativeRmm.canonicalLayout shape).macroSize) hA8
              (by rw [RegFile.write_other _ _ (by decide)]; exact hmacro)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hlocal)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hmid)
              (by rw [RegFile.write_other _ _ (by decide)]; exact hright)
              (by decide) (by decide)
              (E1InteriorCombine.crossMacro_src_witnesses _ _ _ _).1
              (E1InteriorCombine.crossMacro_src_witnesses _ _ _ _).2
              (E1InteriorTwoSpan.localLevelGeom_pos shape)
              (E1InteriorTwoSpan.localLevelGeom_cap shape)
              (localSpanGeom_pos shape)
              (E1InteriorSpanBlock.localSpanGeom_cap shape)
              (E1InteriorTwoSpan.globalLevelGeom_pos shape)
              (E1InteriorTwoSpan.globalLevelGeom_cap shape)
              (globalSpanGeom_pos shape)
              (E1InteriorSpanBlock.globalSpanGeom_cap shape)
              (E1InteriorTwoSpan.localLevelGeom_pos shape)
              (E1InteriorTwoSpan.localLevelGeom_cap shape)
              (localSpanGeom_pos shape)
              (E1InteriorSpanBlock.localSpanGeom_cap shape)
          rw [show Q + 2630 + 1574 = Q + 4204 from by omega] at hrunA
          refine ⟨q, hrunP.trans (hsel.trans hrunA), ?_, ?_⟩
          · rw [hval, E1InteriorDispatch.interiorRangeMin_of_cross shape
              startBlock count hc0 hle hmid0 hr0]
            exact E1InteriorCombine.crossLegValue_crossMacro_eq_routeValue
              shape _ _ _ _
          · intro r hr
            obtain ⟨hcross, h127, h128, h129, h130, h136, h137, h138, h139,
              h146, h147, h148, h149, h150, h151⟩ := hr
            rw [hpres r hcross, RegFile.write_other _ _ h147]
            exact hpresP r ⟨hcross, h127, h128, h129, h130, h136, h137, h138,
              h139, h146, h147, h148, h149, h150, h151⟩

/-! ## THE ROUTE'S BLOCK SIZE AND THE SUB-BLOCKS' AGREE, CHECKED

The route fixes the interior's range with
`canonicalBPRelativeSummaryBlockSizeRaw shape`; every sub-block's
`runsTo` is stated at `(RelativeRmm.canonicalLayout shape).blockSize`.
A worker two lanes ago flagged this as an open question and a later one
recorded that they agree definitionally.  Recorded here as a KERNEL
CHECK rather than as a remark: if the two ever diverge, this line stops
compiling and every `hInterior` instantiation below it stops with it. -/
theorem canonicalBlockSize_eq_layoutBlockSize
    (shape : Cartesian.CartesianShape) :
    canonicalBPRelativeSummaryBlockSizeRaw shape =
      (RelativeRmm.canonicalLayout shape).blockSize := rfl

/-! ## `hInterior`, DISCHARGED

`crossBlockArmProgramAt_runsTo`'s `hInterior` (`E1CrossBlockArm.lean:1143`)
promises, for EVERY entry register file agreeing on `fClose` and `fRight`:
a `RunsTo` at base `A + 176` to `A + 176 + interior.length`, the value in
`mMV`/`mMP`, and FOUR register equalities -- `fClose`, `fRight`, `mLV`,
`mLP`.  Four, not five.

**The quantifier order is what makes this nontrivial.**  `interiorTrace`,
`interiorCats` and `interiorValue` are bound OUTSIDE the `∀ regsS`, so the
interior's answer must be a function of `fClose` and `fRight` ALONE.  A
correct interior that read any other entry register could not discharge
this premise.  `rangePreamble` is what makes it a function of those two:
it recomputes the whole range from them by six instructions, and
`interiorRange_from_operands` is the route-side half of the same fact. -/
theorem interiorDispatch_hInterior (shape : Cartesian.CartesianShape)
    {program : E1Machine.Program} {A leftClose rightClose : Nat}
    (hHost : HostedAt program (A + 176)
      (canonicalInteriorDispatchBlock shape (A + 176))) :
    ∀ regsS : RegFile, regsS fClose = leftClose →
      regsS fRight = rightClose →
      ∃ regsI : RegFile,
        RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
            ⟨regsS, A + 176, false⟩
            ⟨regsI, A + 176 +
              (canonicalInteriorDispatchBlock shape (A + 176)).length,
              false⟩
          (dispatchEvents shape
            (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
            (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
              leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
          (dispatchCats shape
            (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
            (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
              leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                1)) ∧
        bestOfRegs (regsI mMV) (regsI mMP) =
          dispatchRouteValue shape
            (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
            (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
              leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                1) ∧
        regsI fClose = regsS fClose ∧ regsI fRight = regsS fRight ∧
        regsI mLV = regsS mLV ∧ regsI mLP = regsS mLP := by
  intro regsS hCl hRi
  obtain ⟨regsI, hrun, hval, hpres⟩ :=
    interiorDispatchBlock_runsTo shape regsS leftClose rightClose _ _ hHost
      hCl hRi rfl rfl
  refine ⟨regsI, ?_, hval, ?_, ?_, ?_, ?_⟩
  · rw [canonicalInteriorDispatchBlock_length]
    exact hrun
  · exact hpres fClose
      E1InteriorDispatch.dispatchUntouched_at_crossBlockArm_operands.1
  · exact hpres fRight
      E1InteriorDispatch.dispatchUntouched_at_crossBlockArm_operands.2.1
  · exact hpres mLV
      E1InteriorDispatch.dispatchUntouched_at_crossBlockArm_operands.2.2.1
  · exact hpres mLP
      E1InteriorDispatch.dispatchUntouched_at_crossBlockArm_operands.2.2.2

/-- **THE ADDITIONAL EXPORT, NOT A FIFTH CONJUNCT.**

`hInterior` has exactly four register equalities and a fifth conjunct does
not typecheck against it.  The close leg's `CloseLegUntouched` clause is
therefore proved SEPARATELY, so that it is already in hand when the
close-leg branch merges and widens the premise -- and so that nobody has
to widen `hInterior` to get it. -/
theorem interiorDispatch_preserves_closeLeg
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {A leftClose rightClose : Nat}
    (hHost : HostedAt program (A + 176)
      (canonicalInteriorDispatchBlock shape (A + 176)))
    (regsS : RegFile) (hCl : regsS fClose = leftClose)
    (hRi : regsS fRight = rightClose) :
    ∃ regsI : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regsS, A + 176, false⟩
          ⟨regsI, A + 176 +
            (canonicalInteriorDispatchBlock shape (A + 176)).length, false⟩
        (dispatchEvents shape
          (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
          (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
            leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
        (dispatchCats shape
          (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
          (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
            leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1)) ∧
      (∀ r, CloseLegUntouched r → regsI r = regsS r) := by
  obtain ⟨regsI, hrun, hval, hpres⟩ :=
    interiorDispatchBlock_runsTo shape regsS leftClose rightClose _ _ hHost
      hCl hRi rfl rfl
  refine ⟨regsI, ?_, ?_⟩
  · rw [canonicalInteriorDispatchBlock_length]
    exact hrun
  · intro r hr
    exact hpres r
      (E1InteriorDispatch.dispatchUntouched_of_closeLegUntouched hr)

/-- **THE PREMISE ACTUALLY FITS.**

`interiorDispatch_hInterior` states something with `hInterior`'s SHAPE;
this consumes `crossBlockArmProgramAt_runsTo` with it, which is the only
check that the shape actually UNIFIES with the premise -- including that
the route's `canonicalBPRelativeSummaryBlockSizeRaw` and the sub-blocks'
`(RelativeRmm.canonicalLayout shape).blockSize` are the same term to the
elaborator, and that `interior.length` in the target PC is `4204`.

The remaining premises are the close leg's, not the interior's: `hc` and
the six `readBits` length facts belong to the fringe arms and are carried
through untouched.  `E1CrossBlockArm.lean` is NOT edited -- this is
instantiation of its implicit parameters from the interior's side. -/
theorem crossBlockArm_withCanonicalInterior_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {A fringeSegment leftClose rightClose : Nat}
    (hc : E1SameBlockArm.sbChunkBits shape ≤
      SuccinctRank.machineWordBits shape.bpCode.length)
    (hHost : HostedAt program A
      (E1CrossBlockArm.crossBlockArmProgramAt shape fringeSegment
        (canonicalBPRelativeSummaryBlockSizeRaw shape) A
        (canonicalInteriorDispatchBlock shape (A + 176))))
    (hL0 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hL1 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hL2 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        leftClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR0 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR1 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose + 1)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (hR2 : (E1FringeArmBlock.readBits (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (E1SameBlockArm.sbBase shape (canonicalBPRelativeSummaryBlockSizeRaw shape)
        rightClose + 2)).length =
        SuccinctRank.machineWordBits shape.bpCode.length)
    (regs : RegFile)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, A, false⟩
          ⟨regsF, A + 370 +
            (canonicalInteriorDispatchBlock shape (A + 176)).length, false⟩
        (E1CrossBlockArm.crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨dispatchRouteValue shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1),
            dispatchEvents shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1)⟩
          leftClose rightClose).trace
        (E1CrossBlockArm.crossBlockArmCats shape fringeSegment
          (canonicalBPRelativeSummaryBlockSizeRaw shape)
          (dispatchCats shape
            (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
            (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
              leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
          (dispatchRouteValue shape
            (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
            (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
              leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
          leftClose rightClose) ∧
      some (regsF E1SameBlockArm.fRes) =
        (E1CrossBlockArm.crossBlockArmSpec shape
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          fringeSegment (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          ⟨dispatchRouteValue shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1),
            dispatchEvents shape
              (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
              (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
                leftClose / (RelativeRmm.canonicalLayout shape).blockSize -
                  1)⟩
          leftClose rightClose).value :=
  E1CrossBlockArm.crossBlockArmProgramAt_runsTo shape hc hHost hL0 hL1 hL2
    hR0 hR1 hR2
    (interiorDispatch_hInterior shape
      ((E1CrossBlockArm.crossBlockArmProgramAt_hosts shape fringeSegment
        (canonicalBPRelativeSummaryBlockSizeRaw shape) A
        (canonicalInteriorDispatchBlock shape (A + 176))
        hHost).2.2.2.2.2.2.2.1))
    regs hClose hRight

/-! ## THE COMPOSITION'S OWN DISCRIMINATOR: RIGHT JOIN, WRONG ARM

`E1_LIVE_STATE.md` §6 now records seven models.  The seventh
(`unterminatedDispatch_falls_through`) is a MISSING TERMINATOR; this is
its sibling and the defect this module could actually have shipped: a
selector whose target is a DIFFERENT ARM'S BASE.  Every arm reaches the
join, every arm ends un-halted, every arm's write set sits inside
`DispatchUntouched` -- so the wrong arm running is invisible to exit PC,
to the halted flag, and to preservation.

**And it is invisible to the CATEGORY LOG here by construction.**  §6's
fifth model established that a category log constrains WHICH INSTRUCTIONS
RAN and nothing about their operands; a mis-dispatch between two arms of
the same instruction shape is exactly a control path the log cannot
separate.  The two witness arms below are given IDENTICAL instruction
shapes deliberately, so that the log agrees and the receipt is left as the
only non-value discriminator.

**What the receipt does here, and where that stops.**  Both witness arms
READ, at different addresses, so the receipt separates them -- for ANY
store, because a `readWord` event records its ADDRESS and the two
addresses are different numerals whatever the store returns.  By §6's
sixth-model rule -- *a receipt's power over a skipped-code defect is
exactly whether the skipped code reads* -- this is the good case, and it
is the real block's case too: `#4`, `#6`, `#7` and `#8` all begin with an
unconditional level read, so a real mis-dispatch changes the first
event of the receipt.

**Two scope notes, because the fixture and the block differ.**
1. The category-log AGREEMENT is the FIXTURE's, not the block's.  `#9`'s
   real arms are 510, 1045, 1045 and 1574 instructions long with
   different logs, so the real category log would ALSO catch a
   mis-dispatch.  The fixture suppresses that on purpose, to isolate what
   the receipt alone can do.
2. Both witness arms end UN-HALTED, as every real sub-block does.  A
   halting witness arm cannot exhibit a control-flow defect at all --
   which is how the close-leg lane's cross-arm defect stayed invisible to
   the whole battery. -/

/-- The two witness arms, at `2..5` and `6..9`, joining at `10`.
Identical instruction shapes; they differ only in the address read and in
the marker left in `mMV`. -/
def missArms : List Instr :=
  [ Instr.const wT 5, Instr.readMem wStart 0 wT, Instr.const mMV 1
  , Instr.brNZ wOne 10
  , Instr.const wT 9, Instr.readMem wStart 0 wT, Instr.const mMV 2
  , Instr.brNZ wOne 10 ]

/-- The CORRECT selector: `count = 0` reaches the first arm. -/
def missSelector : List Instr :=
  [ Instr.brNZ wCount 6, Instr.brNZ wOne 2 ]

/-- **THE IMPOSTOR**: one branch target moved from the first arm's base to
the SECOND arm's base.  Not a missing terminator and not a wrong operand
-- a correct, present, terminating branch that goes to the wrong arm. -/
def missSelectorImpostor : List Instr :=
  [ Instr.brNZ wCount 6, Instr.brNZ wOne 6 ]

def missDispatch : List Instr := missSelector ++ missArms

def missDispatchImpostor : List Instr := missSelectorImpostor ++ missArms

/-- The two layouts differ in exactly one instruction, at index `1`: same
length, same instruction at `0`, same tail from `2` on, different at `1`.
Stated with `drop` rather than a quantifier over indices so that the whole
claim DECIDES. -/
theorem missDispatch_differ_at_one_index :
    missDispatch.length = missDispatchImpostor.length ∧
      missDispatch[0]? = missDispatchImpostor[0]? ∧
      missDispatch[1]? ≠ missDispatchImpostor[1]? ∧
      missDispatch.drop 2 = missDispatchImpostor.drop 2 :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- The CORRECT layout on a `count = 0` query: the first arm runs, reading
address `5` and leaving marker `1`. -/
theorem missDispatch_runs_armA (store : ReadStore) (regs : RegFile)
    (hCount : regs wCount = 0) (hOne : regs wOne = 1) :
    ∃ regs' : RegFile,
      RunsTo store missDispatch ⟨regs, 0, false⟩ ⟨regs', 10, false⟩
        [.readWord 0 5 (store.readWord? 0 5)]
        [Category.branch, Category.branch, Category.registerWrite,
          Category.memoryRead, Category.registerWrite, Category.branch] ∧
      regs' mMV = 1 := by
  refine ⟨((regs.write wT 5).write wStart
    (decodeRead (store.readWord? 0 5))).write mMV 1, ?_, by simp⟩
  have f0 : missDispatch[0]? = some (Instr.brNZ wCount 6) := rfl
  have f1 : missDispatch[1]? = some (Instr.brNZ wOne 2) := rfl
  have f2 : missDispatch[2]? = some (Instr.const wT 5) := rfl
  have f3 : missDispatch[3]? = some (Instr.readMem wStart 0 wT) := rfl
  have f4 : missDispatch[4]? = some (Instr.const mMV 1) := rfl
  have f5 : missDispatch[5]? = some (Instr.brNZ wOne 10) := rfl
  have h0 : RunsTo store missDispatch ⟨regs, 0, false⟩ ⟨regs, 1, false⟩ []
      [Category.branch] := by
    have h := RunsTo.brNZ_not_taken (store := store)
      (s := (⟨regs, 0, false⟩ : State)) rfl f0
      (by simpa using hCount)
    simpa using h
  have h1 : RunsTo store missDispatch ⟨regs, 1, false⟩ ⟨regs, 2, false⟩ []
      [Category.branch] :=
    RunsTo.brNZ_taken (store := store) (s := (⟨regs, 1, false⟩ : State)) rfl
      f1 (by simp [hOne])
  have h2 : RunsTo store missDispatch ⟨regs, 2, false⟩
      ⟨regs.write wT 5, 3, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, 2, false⟩ : State)) rfl f2
    simpa using h
  have h3 : RunsTo store missDispatch ⟨regs.write wT 5, 3, false⟩
      ⟨(regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5)), 4, false⟩
      [.readWord 0 5 (store.readWord? 0 5)] [Category.memoryRead] := by
    have h := RunsTo.readMem (store := store)
      (s := (⟨regs.write wT 5, 3, false⟩ : State)) rfl f3
    simpa using h
  have h4 : RunsTo store missDispatch
      ⟨(regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5)), 4, false⟩
      ⟨((regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5))).write mMV 1, 5, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨(regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5)), 4, false⟩ : State)) rfl
      f4
    simpa using h
  have h5 : RunsTo store missDispatch
      ⟨((regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5))).write mMV 1, 5, false⟩
      ⟨((regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5))).write mMV 1, 10, false⟩ []
      [Category.branch] :=
    RunsTo.brNZ_taken (store := store)
      (s := (⟨((regs.write wT 5).write wStart
        (decodeRead (store.readWord? 0 5))).write mMV 1, 5, false⟩ : State))
      rfl f5
      (by
        show (((regs.write wT 5).write wStart
          (decodeRead (store.readWord? 0 5))).write mMV 1) wOne ≠ 0
        rw [RegFile.write_other _ _ (by decide),
          RegFile.write_other _ _ (by decide),
          RegFile.write_other _ _ (by decide), hOne]
        omega)
  have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  simpa using h

/-- **THE IMPOSTOR RUNS THE OTHER ARM** on the same query: it reaches the
same join, un-halted, having read address `9` and left marker `2`. -/
theorem missDispatchImpostor_runs_armB (store : ReadStore) (regs : RegFile)
    (hCount : regs wCount = 0) (hOne : regs wOne = 1) :
    ∃ regs' : RegFile,
      RunsTo store missDispatchImpostor ⟨regs, 0, false⟩ ⟨regs', 10, false⟩
        [.readWord 0 9 (store.readWord? 0 9)]
        [Category.branch, Category.branch, Category.registerWrite,
          Category.memoryRead, Category.registerWrite, Category.branch] ∧
      regs' mMV = 2 := by
  refine ⟨((regs.write wT 9).write wStart
    (decodeRead (store.readWord? 0 9))).write mMV 2, ?_, by simp⟩
  have f0 : missDispatchImpostor[0]? = some (Instr.brNZ wCount 6) := rfl
  have f1 : missDispatchImpostor[1]? = some (Instr.brNZ wOne 6) := rfl
  have f6 : missDispatchImpostor[6]? = some (Instr.const wT 9) := rfl
  have f7 : missDispatchImpostor[7]? = some (Instr.readMem wStart 0 wT) := rfl
  have f8 : missDispatchImpostor[8]? = some (Instr.const mMV 2) := rfl
  have f9 : missDispatchImpostor[9]? = some (Instr.brNZ wOne 10) := rfl
  have h0 : RunsTo store missDispatchImpostor ⟨regs, 0, false⟩
      ⟨regs, 1, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ_not_taken (store := store)
      (s := (⟨regs, 0, false⟩ : State)) rfl f0
      (by simpa using hCount)
    simpa using h
  have h1 : RunsTo store missDispatchImpostor ⟨regs, 1, false⟩
      ⟨regs, 6, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (store := store) (s := (⟨regs, 1, false⟩ : State)) rfl
      f1 (by simp [hOne])
  have h2 : RunsTo store missDispatchImpostor ⟨regs, 6, false⟩
      ⟨regs.write wT 9, 7, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, 6, false⟩ : State)) rfl f6
    simpa using h
  have h3 : RunsTo store missDispatchImpostor ⟨regs.write wT 9, 7, false⟩
      ⟨(regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9)), 8, false⟩
      [.readWord 0 9 (store.readWord? 0 9)] [Category.memoryRead] := by
    have h := RunsTo.readMem (store := store)
      (s := (⟨regs.write wT 9, 7, false⟩ : State)) rfl f7
    simpa using h
  have h4 : RunsTo store missDispatchImpostor
      ⟨(regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9)), 8, false⟩
      ⟨((regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9))).write mMV 2, 9, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨(regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9)), 8, false⟩ : State)) rfl
      f8
    simpa using h
  have h5 : RunsTo store missDispatchImpostor
      ⟨((regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9))).write mMV 2, 9, false⟩
      ⟨((regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9))).write mMV 2, 10, false⟩ []
      [Category.branch] :=
    RunsTo.brNZ_taken (store := store)
      (s := (⟨((regs.write wT 9).write wStart
        (decodeRead (store.readWord? 0 9))).write mMV 2, 9, false⟩ : State))
      rfl f9
      (by
        show (((regs.write wT 9).write wStart
          (decodeRead (store.readWord? 0 9))).write mMV 2) wOne ≠ 0
        rw [RegFile.write_other _ _ (by decide),
          RegFile.write_other _ _ (by decide),
          RegFile.write_other _ _ (by decide), hOne]
        omega)
  have h := h0.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
  simpa using h

/-- **THE EXIT PC AND THE HALTED FLAG DO NOT SEPARATE THEM.**  Both layouts
reach `10` un-halted -- which is the property a layout check would most
naturally verify, and the property this defect preserves exactly. -/
theorem missDispatch_exit_and_halt_agree :
    ((10 : Nat), false) = ((10 : Nat), false) := rfl

/-- **THE CATEGORY LOG DOES NOT SEPARATE THEM.**  Six categories,
positionally identical.  This is the fixture's own construction -- the two
witness arms were given identical instruction shapes -- and NOT a property
of `#9`, whose four real arms have logs of four different lengths. -/
theorem missDispatch_catLogs_agree :
    [Category.branch, Category.branch, Category.registerWrite,
        Category.memoryRead, Category.registerWrite, Category.branch] =
      [Category.branch, Category.branch, Category.registerWrite,
        Category.memoryRead, Category.registerWrite, Category.branch] := rfl

/-- **THE RECEIPT DOES SEPARATE THEM, AT EVERY STORE.**

The addresses are different numerals, and a `readWord` event carries its
address, so the two receipts differ whatever the store returns -- the
inequality does not depend on the store's contents at `5` or at `9`, and
in particular survives a store that answers both with `none`.  This is
the sixth model's rule in its favourable direction, and it is why `#9`'s
receipt is a real instrument against a mis-dispatch rather than a
formality: every arm `#9` can reach begins with a level read. -/
theorem missDispatch_receipts_differ (store : ReadStore) :
    [WordRAM.TraceEvent.readWord 0 5 (store.readWord? 0 5)] ≠
      [WordRAM.TraceEvent.readWord 0 9 (store.readWord? 0 9)] := by
  simp

/-- **AND THE VALUES DIFFER**, which is the other discriminator.  Recorded
so the boundary is exact: of exit PC, halted flag, category log, receipt
and value, the last two catch this defect and the first three do not. -/
theorem missDispatch_values_differ (bp : Nat) :
    bestOfRegs 1 bp ≠ bestOfRegs 2 bp := by simp

end E1InteriorDispatchCompose
end WordRAM
end RMQ
