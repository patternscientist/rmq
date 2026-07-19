import RMQ.Core.WordRAM.E1InteriorCombine

/-! # E1 amended machine: THE INTERIOR'S FIVE-BRANCH DISPATCH (`#9`)

`canonicalRelativeRmmInteriorRangeMinComputation`
(`InteriorDirectory.lean:2444`) is the interior leg's top: a five-way
dispatch on the requested block range.  **Note the identifier has no
`Machine` in it**, unlike rows `#1`-`#8` of the interior ladder; the
`...`-elided tables in `E1_LIVE_STATE.md` hide that, and expanding the
name from the pattern of the rows below it produces a constant that does
not exist.

Read off the source, the five branches are

* `count = 0`                        -> `pure none`
* `count <= macroSize - localStart`  -> `#4`  (local two-span)
* `middleMacroCount = 0`             -> `#6`  (adjacent macro)
* `rightCount = 0`                   -> `#7`  (left+middle macro)
* otherwise                          -> `#8`  (cross macro)

with `macroStart := startBlock / macroSize`,
`localStart := startBlock % macroSize`,
`leftCount := macroSize - localStart`, `remaining := count - leftCount`,
`middleMacroCount := remaining / macroSize` and
`rightCount := remaining % macroSize`.

`leftCount` is bound in the route but NEVER PASSED: `#6`/`#7`/`#8` each
re-derive `macroSize - localStart` internally, and the two spellings
coincide only because `#9` hands its own `localStart` through unchanged.

## THE FACT THAT GOVERNS THIS WHOLE LAYOUT

**Not one of the blocks `#9` dispatches into terminates.**  `spanBlock`,
`twoSpanBlock`, `twoLegBlock`, `crossLegBlock` and `mergeBlock` all end
in the state `<regs', exit, false>` -- the third component is the HALTED
FLAG and it is `false` in every one.  A `halt` instruction does exist in
the ISA (`E1Machine.lean:103`); none of them uses it, because each is
designed to be composed.

So an arm that ends at its sub-block's exit PC **continues executing at
whatever instruction sits there**.  Every arm therefore has to be given
an explicit unconditional branch to the dispatch's join point, or it
falls straight into the next arm's code and answers with the next arm's
data.  That is not hypothetical: the close-leg lane found
`crossBlockArmProgramAt`'s cross arm with no terminator and an exit PC
landing exactly on the next block's base.
`unterminatedDispatch_falls_through` below is the same defect at this
block, exhibited by EXECUTION rather than argued.

**A CORRECTION TO THE BRIEF THIS MODULE WAS BUILT FROM.**  The
instruction said "every one of `#9`'s five arms needs an explicit branch
to the join point".  That is over-stated by exactly one: whichever arm is
placed PHYSICALLY LAST exits by falling through to the join, and giving
it a branch would be either a no-op or wrong.  Four arms here carry an
explicit `brNZ`; `#8` is last and exits by position.  That is correct,
but it is correct FOR A REASON THE TYPE DOES NOT RECORD, so
`dispatchArm8_exit_is_join` states the coincidence as a theorem instead
of leaving it to arithmetic that happens to work out.

## Why the `count = 0` arm is the dangerous one

It is the shortest -- two instructions -- so its missing branch is the
cheapest to overlook, and its fall-through lands in `#4`'s code, which
READS.  The discriminator below is built at exactly that arm.

## The unconditional branch idiom

There is no unconditional jump in the ISA.  `brNZ cond target` with
`cond` a register holding a nonzero constant is the idiom, and it is the
one `twoSpanArms` (`E1InteriorTwoSpan.lean:156`) already uses at
`Q + 42`.  `wOne` (`146`) is this block's copy.

## Register allocation, and why the bank opens at `146`

The stash-pair ladder puts `crossLegBlock`'s own pair at `144`/`145`, and
`crossLegUntouched_of_ge` (`E1InteriorCombine.lean:997`) proves the whole
three-leg write set lies below `146`.  That is what lets `wOne` survive
an entire arm and still be nonzero at the arm's trailing branch -- the
single load-bearing register fact in this module.

`wOne` 146, `wT` 147, `wStart` 148, `wCount` 149, `wRem` 150,
`wLeft` 151.
-/

namespace RMQ
namespace WordRAM
namespace E1InteriorDispatch

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal
open E1Machine
open E1FringeFoldBlock (bestOfRegs)
open E1SameBlockArm (fClose fRight)
open E1CandMerge3 (mMV mMP mLV mLP)
open E1InteriorSummaryGroup (TableGeom SummaryLayout canonicalSummaryLayout)
open E1InteriorMerge (MergeUntouched ShuttleUntouched)
open E1InteriorSpanBlock (SpanUntouched)
open E1InteriorTwoSpan (tA tStart tN tOff twoSpanBlock TwoSpanUntouched)
open E1InteriorCombine (uMacro uLocal uMid uRight uT uZero uSV uSP vSV vSP
  twoLegBlock crossLegBlock TwoLegUntouched CrossLegUntouched)

/-! ## The dispatch bank -/

/-- The constant `1`, the unconditional-branch condition. -/
abbrev wOne : Nat := 146
/-- Dispatch scratch. -/
abbrev wT : Nat := 147
/-- `startBlock`, computed from `fClose`. -/
abbrev wStart : Nat := 148
/-- `count`, computed from `fClose` and `fRight`. -/
abbrev wCount : Nat := 149
/-- `remaining`. -/
abbrev wRem : Nat := 150
/-- `leftCount = macroSize - localStart`. -/
abbrev wLeft : Nat := 151

/-! ## The range preamble

`hInterior` quantifies over EVERY entry register file agreeing on
`fClose` and `fRight`, with the interior's trace, categories and value
bound OUTSIDE that quantifier.  So the interior's answer has to be a
function of those two registers ALONE: a program that reads any unpinned
register cannot discharge the premise however correct it is.

The route fixes the range at `ChargedFringeTrace.lean:1164`:
`startBlock = leftBlock + 1` and `count = rightBlock - leftBlock - 1`
with `leftBlock = blockOfClose blockSize leftClose` and
`blockOfClose blockSize close = close / blockSize`
(`BlockLocal.lean:865`).  Both are `divConst`-computable, so the whole
range is recovered from `fClose`/`fRight` by six instructions.

**The route's guard needs no machine counterpart.**  The caller wraps the
interior in `if leftBlock + 1 < rightBlock then ... else pure none`, a
STRICT guard.  When it fails, `rightBlock - leftBlock - 1` truncates to
`0` in `Nat`, and the route's own `count = 0` branch already returns
`pure none`.  The two agree, so `#9` carries one `none` path, not two. -/
def rangePreamble (blockSize : Nat) : List Instr :=
  [ Instr.const wOne 1
  , Instr.divConst wT fClose blockSize      -- leftBlock
  , Instr.divConst wRem fRight blockSize    -- rightBlock
  , Instr.add wStart wT wOne                -- startBlock = leftBlock + 1
  , Instr.sub wCount wRem wT                -- rightBlock - leftBlock
  , Instr.sub wCount wCount wOne ]          -- count

@[simp] theorem rangePreamble_length (blockSize : Nat) :
    (rangePreamble blockSize).length = 6 := rfl

/-! ## The index decomposition

`localStart` and `rightCount` are the route's `%`, and **there is no
modulus instruction**: each becomes `v - v / D * D` by
`divConst`/`mulConst`/`sub`, bridged by `mod_eq_sub_div_mul`
(`E1InteriorTwoSpan.lean:143`). -/
def indexDecomp (macroSize : Nat) : List Instr :=
  [ Instr.divConst uMacro wStart macroSize   -- macroStart
  , Instr.mulConst wT uMacro macroSize
  , Instr.sub uLocal wStart wT               -- localStart  (the route's %)
  , Instr.const wT macroSize
  , Instr.sub wLeft wT uLocal                -- leftCount
  , Instr.sub wRem wCount wLeft              -- remaining
  , Instr.divConst uMid wRem macroSize       -- middleMacroCount
  , Instr.mulConst wT uMid macroSize
  , Instr.sub uRight wRem wT ]               -- rightCount  (the route's %)

@[simp] theorem indexDecomp_length (macroSize : Nat) :
    (indexDecomp macroSize).length = 9 := rfl

/-- `#4`'s four input registers, which the combiners do NOT share:
`twoSpanBlock` is entered on `tA`/`tStart`/`tN`/`tOff` (`127`-`130`)
while `#6`/`#7`/`#8` are entered on `uMacro`/`uLocal`/`uMid`/`uRight`
(`136`-`139`).  Written unconditionally, before the dispatch, because the
two banks are disjoint and no arm can observe the other's setup. -/
def localArmSetup (macroSize levelSlab : Nat) : List Instr :=
  [ Instr.mulConst tA uMacro levelSlab
  , Instr.move tStart uLocal
  , Instr.move tN wCount
  , Instr.mulConst tOff uMacro macroSize ]

@[simp] theorem localArmSetup_length (macroSize levelSlab : Nat) :
    (localArmSetup macroSize levelSlab).length = 4 := rfl

/-! ## The selector

Nine instructions at `Q + 19 .. Q + 27`.  Each of the three `= 0` tests
is done by `brNZ` on the value itself rather than by a `natEq` against a
zero register: `brNZ v L` falls through exactly when `v = 0`, which saves
the zero register and one comparison per test, and keeps the category log
honest -- a test that is a branch is charged as a branch.

Only the `count <= leftCount` test needs a comparison, because it is not
a test against zero.

The five targets are the five arm bases; `armBase*` below are the same
numerals, named, so the discriminator and the simulation cannot drift
apart from the program. -/
def dispatchSelector (Q : Nat) : List Instr :=
  [ Instr.brNZ wCount (Q + 21)      -- Q+19  count /= 0 -> continue
  , Instr.brNZ wOne (Q + 28)        -- Q+20  count = 0 -> ARM0
  , Instr.natLe wT wCount wLeft     -- Q+21  count <= leftCount ?
  , Instr.brNZ wT (Q + 30)          -- Q+22  yes -> ARM4
  , Instr.brNZ uMid (Q + 25)        -- Q+23  mid /= 0 -> continue
  , Instr.brNZ wOne (Q + 540)       -- Q+24  mid = 0 -> ARM6
  , Instr.brNZ uRight (Q + 27)      -- Q+25  right /= 0 -> continue
  , Instr.brNZ wOne (Q + 1585)      -- Q+26  right = 0 -> ARM7
  , Instr.brNZ wOne (Q + 2630) ]    -- Q+27  else -> ARM8

@[simp] theorem dispatchSelector_length (Q : Nat) :
    (dispatchSelector Q).length = 9 := rfl

/-! ## The five arm bases and the join

`Q + 28` preamble+selector; then `2 + 510 + 1045 + 1045 + 1574 = 4176`
of arms, so the join is `Q + 4204`.

`#8` is placed LAST deliberately: it is the longest arm, and the arm
that exits by falling through is the one whose exit PC has to coincide
with the join, so the coincidence is cheapest to state where the
arithmetic is a single addition. -/
@[simp] def armBase0 (Q : Nat) : Nat := Q + 28
@[simp] def armBase4 (Q : Nat) : Nat := Q + 30
@[simp] def armBase6 (Q : Nat) : Nat := Q + 540
@[simp] def armBase7 (Q : Nat) : Nat := Q + 1585
@[simp] def armBase8 (Q : Nat) : Nat := Q + 2630
@[simp] def dispatchJoin (Q : Nat) : Nat := Q + 4204

/-- **THE `pure none` ARM.**  `bestOfRegs` reads `none` off `mMV = 0`
(`E1FringeFoldBlock.lean:115`), so the whole content of this arm is one
constant -- and one branch, which is the entire subject of
`unterminatedDispatch_falls_through`. -/
def dispatchArm0 (Q : Nat) : List Instr :=
  [ Instr.const mMV 0
  , Instr.brNZ wOne (dispatchJoin Q) ]

@[simp] theorem dispatchArm0_length (Q : Nat) :
    (dispatchArm0 Q).length = 2 := rfl

/-! ## THE BLOCK

4204 instructions: 28 of preamble and selector, then the five arms in
the order `#0`, `#4`, `#6`, `#7`, `#8`.

Every sub-block here is POSITION-DEPENDENT and computes its internal
branch targets from the base it is handed, so **the base passed to each
constructor must equal the base it is hosted at**.  Nothing in the types
enforces that: `HostedAt program Q (block ... Q')` with `Q ≠ Q'` is
satisfiable and wrong.  The bases below are written as the same numerals
that `armBase*` name, and `interiorDispatchBlock_bases_are_arm_bases`
checks the two spellings against each other. -/
def interiorDispatchBlock (L : SummaryLayout) (GLl GSl GLg GSg : TableGeom)
    (macroSize macroSampleCount levelSlab Dl Dg
      blockSize blocksPerSuper Q : Nat) : List Instr :=
  rangePreamble blockSize ++
    (indexDecomp macroSize ++
      (localArmSetup macroSize levelSlab ++
        (dispatchSelector Q ++
          (dispatchArm0 Q ++
            ((twoSpanBlock L GLl GSl macroSize Dl blockSize blocksPerSuper
                  (Q + 30) ++
                [Instr.brNZ wOne (dispatchJoin Q)]) ++
              ((twoLegBlock L GLl GSl GLl GSl macroSize Dl macroSize Dl
                    levelSlab macroSize levelSlab macroSize uZero uRight
                    macroSize blockSize blocksPerSuper (Q + 540) ++
                  [Instr.brNZ wOne (dispatchJoin Q)]) ++
                ((twoLegBlock L GLl GSl GLg GSg macroSize Dl
                      macroSampleCount Dg levelSlab macroSize 0 0 uT uMid
                      macroSize blockSize blocksPerSuper (Q + 1585) ++
                    [Instr.brNZ wOne (dispatchJoin Q)]) ++
                  crossLegBlock L GLl GSl GLg GSg GLl GSl macroSize Dl
                    macroSampleCount Dg macroSize Dl levelSlab macroSize
                    0 0 levelSlab macroSize uT uMid macroSize blockSize
                    blocksPerSuper (Q + 2630))))))))

@[simp] theorem interiorDispatchBlock_length (L : SummaryLayout)
    (GLl GSl GLg GSg : TableGeom)
    (macroSize macroSampleCount levelSlab Dl Dg
      blockSize blocksPerSuper Q : Nat) :
    (interiorDispatchBlock L GLl GSl GLg GSg macroSize macroSampleCount
      levelSlab Dl Dg blockSize blocksPerSuper Q).length = 4204 := by
  simp [interiorDispatchBlock, dispatchArm0]

/-- **THE EXIT COINCIDENCE, STATED RATHER THAN LEFT TO ARITHMETIC.**

`#8` is the one arm with no terminator: it is physically last, so it
exits by running off its own end into the join.  That is correct exactly
because `armBase8 Q + 1574 = dispatchJoin Q`, and nothing in the block's
type says so.  DD-20260719-059 records why this is the honest form of
"every arm must reach the join" rather than an exception to it. -/
theorem dispatchArm8_exit_is_join (Q : Nat) :
    armBase8 Q + 1574 = dispatchJoin Q := by simp

/-- The four branch targets are the join, and the five arm bases are the
five offsets the block is actually assembled at.  Checked because a base
passed to a position-dependent constructor that disagrees with the base
it is hosted at is satisfiable and wrong. -/
theorem interiorDispatchBlock_bases_are_arm_bases (Q : Nat) :
    armBase0 Q = Q + 28 ∧ armBase4 Q = Q + 30 ∧ armBase6 Q = Q + 540 ∧
      armBase7 Q = Q + 1585 ∧ armBase8 Q = Q + 2630 ∧
      dispatchJoin Q = Q + 4204 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The arm lengths add to the join offset: `28 + 2 + 510 + 1045 + 1045 +
1574 = 4204`. -/
theorem dispatch_arm_lengths_sum :
    28 + 2 + 510 + 1045 + 1045 + 1574 = 4204 := by decide

/-! ## What `#9` LEAVES ALONE

**Written by enumerating what this block itself WRITES, not by inheriting
a sub-block's predicate.**  `E1_LIVE_STATE.md` §6 records both ways a
preservation predicate has failed here: too WEAK (`SpanUntouched`
declining `mLP`, which its consumer needed) and UNSOUND (the inherited
`TwoLegUntouched` claiming `127`-`130`, which `twoLegBlock` writes
twice).  The instrument built to validate these,
`..._at_crossBlockArm_operands`, passes under BOTH the sound and the
unsound version, because the registers it checks are not the ones at
issue -- so it cannot be the check that establishes soundness.

`#9`'s own write set, enumerated:

* `wOne` `146`, `wT` `147`, `wStart` `148`, `wCount` `149`, `wRem` `150`,
  `wLeft` `151` -- the dispatch bank, all six written by the preamble;
* `tA` `127`, `tStart` `128`, `tN` `129`, `tOff` `130` -- `#4`'s inputs,
  written by `localArmSetup`.  **`TwoSpanUntouched` omits these and is
  right to**, because `twoSpanBlock` only READS them; inheriting it here
  would reproduce the §6 unsoundness exactly;
* `uMacro` `136`, `uLocal` `137`, `uMid` `138`, `uRight` `139` -- the
  combiner inputs, written by `indexDecomp`.  `TwoLegUntouched` does not
  exclude these either, and for the same reason;
* `mMV` `77` on the `count = 0` arm;
* everything the five sub-blocks write, carried by `CrossLegUntouched`,
  which is the strongest of the three ladders and subsumes the other two.
-/
abbrev DispatchUntouched (r : Nat) : Prop :=
  CrossLegUntouched r ∧
    r ≠ 127 ∧ r ≠ 128 ∧ r ≠ 129 ∧ r ≠ 130 ∧
    r ≠ 136 ∧ r ≠ 137 ∧ r ≠ 138 ∧ r ≠ 139 ∧
    r ≠ 146 ∧ r ≠ 147 ∧ r ≠ 148 ∧ r ≠ 149 ∧ r ≠ 150 ∧ r ≠ 151

/-- **THE WHOLE INTERIOR STACK LEAVES EVERY REGISTER BELOW `77` ALONE.**

`mMV` (`77`) is the lowest register anything in the interior writes, so
one structural lemma covers every low-register question this leg is ever
asked: `hInterior`'s four operands `70`/`71`/`75`/`76`, and the close
leg's `CloseLegUntouched` (`r ≤ 7 ∨ r = 28`), without nine numeral cases.

Numerals rather than the register `abbrev`s throughout, for the reason
`twoSpanUntouched_of_ge` records: `omega` collects an `abbrev` as an
OPAQUE ATOM and reports a counterexample naming the abbrev. -/
theorem twoSpanUntouched_of_lt {r : Nat} (h : r < 77) :
    TwoSpanUntouched r :=
  ⟨⟨⟨⟨Or.inl (show r < 89 by omega), show r ≠ 85 by omega,
        show r ≠ 101 by omega, show r ≠ 102 by omega,
        show r ≠ 103 by omega, show r ≠ 104 by omega⟩,
      show r ≠ 77 by omega, show r ≠ 78 by omega,
      Or.inl (show r < 105 by omega)⟩,
    show r ≠ 120 by omega, show r ≠ 121 by omega, show r ≠ 122 by omega,
    show r ≠ 100 by omega⟩,
  ⟨show r ≠ 77 by omega, show r ≠ 78 by omega, show r ≠ 125 by omega,
    show r ≠ 126 by omega⟩,
  ⟨show r ≠ 123 by omega, show r ≠ 124 by omega⟩,
  show r ≠ 118 by omega, show r ≠ 119 by omega, show r ≠ 131 by omega,
  show r ≠ 132 by omega, show r ≠ 133 by omega, show r ≠ 134 by omega,
  show r ≠ 135 by omega⟩

theorem twoLegUntouched_of_lt {r : Nat} (h : r < 77) : TwoLegUntouched r :=
  ⟨twoSpanUntouched_of_lt h,
    ⟨show r ≠ 77 by omega, show r ≠ 78 by omega, show r ≠ 125 by omega,
      show r ≠ 126 by omega⟩,
    ⟨show r ≠ 123 by omega, show r ≠ 124 by omega⟩,
    show r ≠ 127 by omega, show r ≠ 128 by omega, show r ≠ 129 by omega,
    show r ≠ 130 by omega, show r ≠ 140 by omega, show r ≠ 141 by omega,
    show r ≠ 142 by omega, show r ≠ 143 by omega⟩

theorem crossLegUntouched_of_lt {r : Nat} (h : r < 77) :
    CrossLegUntouched r :=
  ⟨twoLegUntouched_of_lt h, show r ≠ 144 by omega, show r ≠ 145 by omega⟩

theorem dispatchUntouched_of_lt {r : Nat} (h : r < 77) :
    DispatchUntouched r :=
  ⟨crossLegUntouched_of_lt h,
    show r ≠ 127 by omega, show r ≠ 128 by omega, show r ≠ 129 by omega,
    show r ≠ 130 by omega, show r ≠ 136 by omega, show r ≠ 137 by omega,
    show r ≠ 138 by omega, show r ≠ 139 by omega, show r ≠ 146 by omega,
    show r ≠ 147 by omega, show r ≠ 148 by omega, show r ≠ 149 by omega,
    show r ≠ 150 by omega, show r ≠ 151 by omega⟩

/-- `hInterior`'s four operands, EVALUATED through the dispatch's own
predicate rather than through a sub-block's. -/
theorem dispatchUntouched_at_crossBlockArm_operands :
    DispatchUntouched 70 ∧ DispatchUntouched 71 ∧ DispatchUntouched 75 ∧
      DispatchUntouched 76 :=
  ⟨dispatchUntouched_of_lt (by omega), dispatchUntouched_of_lt (by omega),
    dispatchUntouched_of_lt (by omega), dispatchUntouched_of_lt (by omega)⟩

/-! ### The close leg's predicate

`CloseLegUntouched` is stated LOCALLY here, byte-for-byte as it appears
at `E1SameBlockArm.lean:72` on the unmerged `claude/e1-close-leg-structural`
branch, because that branch is not merged and this one may not edit it.

**It is NOT a fifth conjunct of `hInterior`.**  A coordinator brief said
`hInterior` "needs a fifth conjunct"; it does not, and never has.
`crossBlockArmProgramAt_runsTo`'s `hInterior` promises exactly FOUR
register equalities (`fClose`, `fRight`, `mLV`, `mLP`) and is
byte-identical on both branches -- re-checked this session at
`E1CrossBlockArm.lean:1143`.  Stating this clause as a fifth conjunct of
a four-conjunct premise does not typecheck.  It is proved here as a
SEPARATE, ADDITIONAL export, so that it is already in hand when the
close-leg branch merges and widens the premise. -/
abbrev CloseLegUntouched (r : Nat) : Prop := r ≤ 7 ∨ r = 28

/-- **THE ADDITIONAL EXPORT.**  Every register the close leg needs
preserved survives the whole interior stack.

`CloseLegUntouched` names `{0,…,7} ∪ {28}`, all below `77`, so this is
`dispatchUntouched_of_lt` and one `omega` -- which is the point of
proving the `of_lt` form structurally rather than deciding nine numerals.

Satisfiability at the intended instantiation is not in question here and
was not constructed FOR the premise: the predicate is `LegUntouched`'s
(`E1InteriorMinCandidate.lean:934`) low-register tail, which
`ChunkFoldUntouched` (`E1InteriorChunkFold.lean:928`) already establishes
as `r < 89 ∨ 99 < r`, with the banks above `100` disjoint from it by
construction. -/
theorem dispatchUntouched_of_closeLegUntouched {r : Nat}
    (h : CloseLegUntouched r) : DispatchUntouched r :=
  dispatchUntouched_of_lt (by rcases h with h | h <;> omega)

/-! ## THE ROUTE SIDE, WRITTEN FIRST

`E1_LIVE_STATE.md` §11 F: *a category function written after the machine
is a category function fitted to the machine.*  The same applies to a
branch decomposition.  These five lemmas are pure route algebra -- no
`RunsTo`, no register, no store -- and they fix what each of `#9`'s arms
is obliged to compute BEFORE any arm is simulated.  The machine side then
case-splits against them rather than against its own shape.

The five conditions are mutually exclusive and exhaustive in the route's
own `if`-order, which is the order the selector tests them in. -/

/-- Branch 1: `count = 0` is `pure none`.

This is also the branch that absorbs the CALLER's guard -- see
`interiorRangeMin_guard_subsumed`. -/
theorem interiorRangeMin_of_count_zero (shape : Cartesian.CartesianShape)
    (startBlock : Nat) :
    canonicalRelativeRmmInteriorRangeMinComputation shape startBlock 0 =
      FlatStoreComputation.pure none := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  simp

/-- Branch 2: a range inside one macro block is `#4`. -/
theorem interiorRangeMin_of_local (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) (hc : count ≠ 0)
    (hle : count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize) :
    canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count =
      canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        count := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  rw [if_neg hc, if_pos hle]

/-- Branch 3: no whole middle macro is `#6`. -/
theorem interiorRangeMin_of_adjacent (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) (hc : count ≠ 0)
    (hgt : ¬ (count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
    (hmid : (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
      (RelativeRmm.canonicalLayout shape).macroSize = 0) :
    canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count =
      canonicalRelativeRmmMachineAdjacentMacroCandidateComputation shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
          (RelativeRmm.canonicalLayout shape).macroSize) := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  rw [if_neg hc, if_neg hgt, if_pos hmid]

/-- Branch 4: whole middle macros and no right remainder is `#7`. -/
theorem interiorRangeMin_of_leftMiddle (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) (hc : count ≠ 0)
    (hgt : ¬ (count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
    (hmid : ¬ ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
      (RelativeRmm.canonicalLayout shape).macroSize = 0))
    (hright : (count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
      (RelativeRmm.canonicalLayout shape).macroSize = 0) :
    canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count =
      canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
          (RelativeRmm.canonicalLayout shape).macroSize) := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  rw [if_neg hc, if_neg hgt, if_neg hmid, if_pos hright]

/-- Branch 5: everything else is `#8`. -/
theorem interiorRangeMin_of_cross (shape : Cartesian.CartesianShape)
    (startBlock count : Nat) (hc : count ≠ 0)
    (hgt : ¬ (count ≤ (RelativeRmm.canonicalLayout shape).macroSize -
      startBlock % (RelativeRmm.canonicalLayout shape).macroSize))
    (hmid : ¬ ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
      (RelativeRmm.canonicalLayout shape).macroSize = 0))
    (hright : ¬ ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
        startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
      (RelativeRmm.canonicalLayout shape).macroSize = 0)) :
    canonicalRelativeRmmInteriorRangeMinComputation shape startBlock count =
      canonicalRelativeRmmMachineCrossMacroCandidateComputation shape
        (startBlock / (RelativeRmm.canonicalLayout shape).macroSize)
        (startBlock % (RelativeRmm.canonicalLayout shape).macroSize)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) /
          (RelativeRmm.canonicalLayout shape).macroSize)
        ((count - ((RelativeRmm.canonicalLayout shape).macroSize -
            startBlock % (RelativeRmm.canonicalLayout shape).macroSize)) %
          (RelativeRmm.canonicalLayout shape).macroSize) := by
  unfold canonicalRelativeRmmInteriorRangeMinComputation
  rw [if_neg hc, if_neg hgt, if_neg hmid, if_neg hright]

/-! ### The caller's guard needs no machine counterpart

`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
(`ChargedFringeTrace.lean:1144`) wraps the interior in

    if leftBlock + 1 < rightBlock then <interior> else pure none

a STRICT guard, with `leftBlock = blockOfClose blockSize leftClose` and
`blockOfClose blockSize close = close / blockSize` (`BlockLocal.lean:865`).

`#9`'s machine program does not test it, and does not need to: when the
guard fails, the count the interior would be called with truncates to `0`
in `Nat`, and `#9`'s own first branch already answers `pure none`.  So
the two `none` paths coincide and the block carries ONE. -/
theorem interiorRangeMin_guard_subsumed (blockSize leftClose rightClose : Nat)
    (h : ¬ (blockOfClose blockSize leftClose + 1 <
      blockOfClose blockSize rightClose)) :
    blockOfClose blockSize rightClose -
      blockOfClose blockSize leftClose - 1 = 0 := by
  unfold blockOfClose at *
  omega

/-- And on the other side of the guard the range is exactly what the
preamble computes: `startBlock = leftClose / blockSize + 1` and
`count = rightClose / blockSize - leftClose / blockSize - 1`, both
`divConst`-computable from `fClose` and `fRight` alone.  **That is what
makes `hInterior` dischargeable at all**: the premise quantifies over
every entry register file agreeing on those two registers, with the
interior's value bound outside the quantifier, so an interior reading any
unpinned register could not satisfy it however correct it was. -/
theorem interiorRange_from_operands (blockSize leftClose rightClose : Nat) :
    blockOfClose blockSize leftClose + 1 = leftClose / blockSize + 1 ∧
      blockOfClose blockSize rightClose - blockOfClose blockSize leftClose - 1
        = rightClose / blockSize - leftClose / blockSize - 1 :=
  ⟨rfl, rfl⟩

/-! ## THE RANGE PREAMBLE, SIMULATED

The six instructions that recover the interior's whole range from
`fClose` and `fRight`.  This is the half of `hInterior` that is not
preservation: the premise binds the interior's value OUTSIDE its
quantifier over entry register files, so the range has to be a function
of those two registers and nothing else.  The simulation below says
exactly that -- `regs'`'s two range readings mention `leftClose` and
`rightClose` and no other register's contents.

Read-free: `[]` on both sides.  The charge log is one `registerWrite`
(the unit seed) and five `arithmetic`. -/
theorem rangePreamble_runsTo (store : ReadStore) {program : E1Machine.Program}
    {blockSize Q : Nat} (hHost : HostedAt program Q (rangePreamble blockSize))
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 6, false⟩ []
          [Category.registerWrite, Category.arithmetic, Category.arithmetic,
            Category.arithmetic, Category.arithmetic, Category.arithmetic] ∧
        regs' wOne = 1 ∧
        regs' wStart = leftClose / blockSize + 1 ∧
        regs' wCount =
          rightClose / blockSize - leftClose / blockSize - 1 ∧
        (∀ r, r ≠ wOne → r ≠ wT → r ≠ wStart → r ≠ wCount → r ≠ wRem →
          regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 6 →
      (rangePreamble blockSize)[k]? = some instr → Q + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.const wOne 1) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.divConst wT fClose blockSize) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.divConst wRem fRight blockSize) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.add wStart wT wOne) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[Q + 4]? = some (.sub wCount wRem wT) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[Q + 5]? = some (.sub wCount wCount wOne) :=
    hf 5 _ _ (by omega) rfl (by omega)
  -- the six register files, named so the terms stay small
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write wOne 1 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile,
      z = r1.write wT (leftClose / blockSize) := ⟨_, rfl⟩
  obtain ⟨r3, hr3⟩ : ∃ z : RegFile,
      z = r2.write wRem (rightClose / blockSize) := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ z : RegFile,
      z = r3.write wStart (leftClose / blockSize + 1) := ⟨_, rfl⟩
  obtain ⟨r5, hr5⟩ : ∃ z : RegFile,
      z = r4.write wCount
        (rightClose / blockSize - leftClose / blockSize) := ⟨_, rfl⟩
  obtain ⟨r6, hr6⟩ : ∃ z : RegFile,
      z = r5.write wCount
        (rightClose / blockSize - leftClose / blockSize - 1) := ⟨_, rfl⟩
  -- readings, each one `write_other` past the banks above
  have e1c : r1 fClose = leftClose := by
    rw [hr1, RegFile.write_other _ _ (by decide), hClose]
  have e1r : r1 fRight = rightClose := by
    rw [hr1, RegFile.write_other _ _ (by decide), hRight]
  have e2r : r2 fRight = rightClose := by
    rw [hr2, RegFile.write_other _ _ (by decide), e1r]
  have e3t : r3 wT = leftClose / blockSize := by
    rw [hr3, RegFile.write_other _ _ (by decide), hr2, RegFile.write_same]
  have e3o : r3 wOne = 1 := by
    rw [hr3, RegFile.write_other _ _ (by decide),
      hr2, RegFile.write_other _ _ (by decide), hr1, RegFile.write_same]
  have e4t : r4 wT = leftClose / blockSize := by
    rw [hr4, RegFile.write_other _ _ (by decide), e3t]
  have e4m : r4 wRem = rightClose / blockSize := by
    rw [hr4, RegFile.write_other _ _ (by decide), hr3, RegFile.write_same]
  have e5c : r5 wCount =
      rightClose / blockSize - leftClose / blockSize := by
    rw [hr5, RegFile.write_same]
  have e5o : r5 wOne = 1 := by
    rw [hr5, RegFile.write_other _ _ (by decide),
      hr4, RegFile.write_other _ _ (by decide), e3o]
  -- the six steps
  have s0 : RunsTo store program ⟨regs, Q, false⟩ ⟨r1, Q + 1, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr1] using h
  have s1 : RunsTo store program ⟨r1, Q + 1, false⟩ ⟨r2, Q + 2, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.divConst (store := store)
      (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1
    simpa [hr2, e1c] using h
  have s2 : RunsTo store program ⟨r2, Q + 2, false⟩ ⟨r3, Q + 3, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.divConst (store := store)
      (s := (⟨r2, Q + 2, false⟩ : State)) rfl h2
    simpa [hr3, e2r] using h
  have s3 : RunsTo store program ⟨r3, Q + 3, false⟩ ⟨r4, Q + 4, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add (store := store)
      (s := (⟨r3, Q + 3, false⟩ : State)) rfl h3
    simpa [hr4, e3t, e3o] using h
  have s4 : RunsTo store program ⟨r4, Q + 4, false⟩ ⟨r5, Q + 5, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r4, Q + 4, false⟩ : State)) rfl h4
    simpa [hr5, e4t, e4m] using h
  have s5 : RunsTo store program ⟨r5, Q + 5, false⟩ ⟨r6, Q + 6, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r5, Q + 5, false⟩ : State)) rfl h5
    simpa [hr6, e5c, e5o] using h
  refine ⟨r6, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((s0.trans s1).trans s2).trans ((s3.trans s4).trans s5)
    simpa using this
  · rw [hr6, RegFile.write_other _ _ (by decide), e5o]
  · rw [hr6, RegFile.write_other _ _ (by decide),
      hr5, RegFile.write_other _ _ (by decide), hr4, RegFile.write_same]
  · rw [hr6, RegFile.write_same]
  · intro r hOne hT hStart hCount hRem
    rw [hr6, RegFile.write_other _ _ hCount,
      hr5, RegFile.write_other _ _ hCount,
      hr4, RegFile.write_other _ _ hStart,
      hr3, RegFile.write_other _ _ hRem,
      hr2, RegFile.write_other _ _ hT,
      hr1, RegFile.write_other _ _ hOne]

/-! ## THE INDEX DECOMPOSITION, SIMULATED

Nine instructions turning `(startBlock, count)` into the five quantities
the five arms dispatch on and are entered with.

**Both of the route's `%` operations are computed as `v - v / D * D`**,
because there is no modulus instruction, and
`E1InteriorTwoSpan.mod_eq_sub_div_mul` is the one bridge between the two
spellings.  It is used twice here -- once for `localStart` and once for
`rightCount` -- and those are the only two places in `#9` where the route
says `%`.

The charge log is seven `arithmetic` and one `registerWrite`, with the
`registerWrite` at index `3`: `macroSize` is a PROGRAM CONSTANT, so
loading it is a `const`, not arithmetic. -/
theorem indexDecomp_runsTo (store : ReadStore) {program : E1Machine.Program}
    {macroSize Q : Nat} (hHost : HostedAt program Q (indexDecomp macroSize))
    (regs : RegFile) (startBlock count : Nat)
    (hStart : regs wStart = startBlock) (hCount : regs wCount = count) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 9, false⟩ []
          [Category.arithmetic, Category.arithmetic, Category.arithmetic,
            Category.registerWrite, Category.arithmetic, Category.arithmetic,
            Category.arithmetic, Category.arithmetic, Category.arithmetic] ∧
        regs' uMacro = startBlock / macroSize ∧
        regs' uLocal = startBlock % macroSize ∧
        regs' wLeft = macroSize - startBlock % macroSize ∧
        regs' uMid =
          (count - (macroSize - startBlock % macroSize)) / macroSize ∧
        regs' uRight =
          (count - (macroSize - startBlock % macroSize)) % macroSize ∧
        regs' wCount = count ∧
        (∀ r, r ≠ uMacro → r ≠ uLocal → r ≠ uMid → r ≠ uRight → r ≠ wT →
          r ≠ wLeft → r ≠ wRem → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 9 →
      (indexDecomp macroSize)[k]? = some instr → Q + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.divConst uMacro wStart macroSize) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.mulConst wT uMacro macroSize) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.sub uLocal wStart wT) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.const wT macroSize) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[Q + 4]? = some (.sub wLeft wT uLocal) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[Q + 5]? = some (.sub wRem wCount wLeft) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[Q + 6]? = some (.divConst uMid wRem macroSize) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[Q + 7]? = some (.mulConst wT uMid macroSize) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have h8 : program[Q + 8]? = some (.sub uRight wRem wT) :=
    hf 8 _ _ (by omega) rfl (by omega)
  -- the two abbreviations the route itself uses
  obtain ⟨lst, hlst⟩ : ∃ z : Nat, z = startBlock % macroSize := ⟨_, rfl⟩
  obtain ⟨rem, hrem⟩ : ∃ z : Nat, z = count - (macroSize - lst) := ⟨_, rfl⟩
  -- THE MODULUS BRIDGE, both uses
  have emodL : startBlock - startBlock / macroSize * macroSize = lst := by
    rw [hlst]; exact (E1InteriorTwoSpan.mod_eq_sub_div_mul _ _).symm
  have emodR : rem - rem / macroSize * macroSize = rem % macroSize :=
    (E1InteriorTwoSpan.mod_eq_sub_div_mul _ _).symm
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile,
      z = regs.write uMacro (startBlock / macroSize) := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile,
      z = r1.write wT (startBlock / macroSize * macroSize) := ⟨_, rfl⟩
  obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write uLocal lst := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ z : RegFile, z = r3.write wT macroSize := ⟨_, rfl⟩
  obtain ⟨r5, hr5⟩ : ∃ z : RegFile,
      z = r4.write wLeft (macroSize - lst) := ⟨_, rfl⟩
  obtain ⟨r6, hr6⟩ : ∃ z : RegFile, z = r5.write wRem rem := ⟨_, rfl⟩
  obtain ⟨r7, hr7⟩ : ∃ z : RegFile,
      z = r6.write uMid (rem / macroSize) := ⟨_, rfl⟩
  obtain ⟨r8, hr8⟩ : ∃ z : RegFile,
      z = r7.write wT (rem / macroSize * macroSize) := ⟨_, rfl⟩
  obtain ⟨r9, hr9⟩ : ∃ z : RegFile,
      z = r8.write uRight (rem % macroSize) := ⟨_, rfl⟩
  have e1m : r1 uMacro = startBlock / macroSize := by
    rw [hr1, RegFile.write_same]
  have e2s : r2 wStart = startBlock := by
    rw [hr2, RegFile.write_other _ _ (by decide),
      hr1, RegFile.write_other _ _ (by decide), hStart]
  have e2t : r2 wT = startBlock / macroSize * macroSize := by
    rw [hr2, RegFile.write_same]
  have e4t : r4 wT = macroSize := by rw [hr4, RegFile.write_same]
  have e4l : r4 uLocal = lst := by
    rw [hr4, RegFile.write_other _ _ (by decide), hr3, RegFile.write_same]
  have e5c : r5 wCount = count := by
    rw [hr5, RegFile.write_other _ _ (by decide),
      hr4, RegFile.write_other _ _ (by decide),
      hr3, RegFile.write_other _ _ (by decide),
      hr2, RegFile.write_other _ _ (by decide),
      hr1, RegFile.write_other _ _ (by decide), hCount]
  have e5l : r5 wLeft = macroSize - lst := by rw [hr5, RegFile.write_same]
  have e6r : r6 wRem = rem := by rw [hr6, RegFile.write_same]
  have e7r : r7 wRem = rem := by
    rw [hr7, RegFile.write_other _ _ (by decide), e6r]
  have e7m : r7 uMid = rem / macroSize := by rw [hr7, RegFile.write_same]
  have e8r : r8 wRem = rem := by
    rw [hr8, RegFile.write_other _ _ (by decide), e7r]
  have e8t : r8 wT = rem / macroSize * macroSize := by
    rw [hr8, RegFile.write_same]
  have s0 : RunsTo store program ⟨regs, Q, false⟩ ⟨r1, Q + 1, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.divConst (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr1, hStart] using h
  have s1 : RunsTo store program ⟨r1, Q + 1, false⟩ ⟨r2, Q + 2, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1
    simpa [hr2, e1m] using h
  have s2 : RunsTo store program ⟨r2, Q + 2, false⟩ ⟨r3, Q + 3, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r2, Q + 2, false⟩ : State)) rfl h2
    simpa [hr3, e2s, e2t, emodL] using h
  have s3 : RunsTo store program ⟨r3, Q + 3, false⟩ ⟨r4, Q + 4, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨r3, Q + 3, false⟩ : State)) rfl h3
    simpa [hr4] using h
  have s4 : RunsTo store program ⟨r4, Q + 4, false⟩ ⟨r5, Q + 5, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r4, Q + 4, false⟩ : State)) rfl h4
    simpa [hr5, e4t, e4l] using h
  have s5 : RunsTo store program ⟨r5, Q + 5, false⟩ ⟨r6, Q + 6, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r5, Q + 5, false⟩ : State)) rfl h5
    simpa [hr6, e5c, e5l, hrem] using h
  have s6 : RunsTo store program ⟨r6, Q + 6, false⟩ ⟨r7, Q + 7, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.divConst (store := store)
      (s := (⟨r6, Q + 6, false⟩ : State)) rfl h6
    simpa [hr7, e6r] using h
  have s7 : RunsTo store program ⟨r7, Q + 7, false⟩ ⟨r8, Q + 8, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨r7, Q + 7, false⟩ : State)) rfl h7
    simpa [hr8, e7m] using h
  have s8 : RunsTo store program ⟨r8, Q + 8, false⟩ ⟨r9, Q + 9, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.sub (store := store)
      (s := (⟨r8, Q + 8, false⟩ : State)) rfl h8
    simpa [hr9, e8r, e8t, emodR] using h
  refine ⟨r9, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have := ((s0.trans s1).trans (s2.trans s3)).trans
      ((s4.trans s5).trans ((s6.trans s7).trans s8))
    simpa using this
  · rw [hr9, RegFile.write_other _ _ (by decide),
      hr8, RegFile.write_other _ _ (by decide),
      hr7, RegFile.write_other _ _ (by decide),
      hr6, RegFile.write_other _ _ (by decide),
      hr5, RegFile.write_other _ _ (by decide),
      hr4, RegFile.write_other _ _ (by decide),
      hr3, RegFile.write_other _ _ (by decide),
      hr2, RegFile.write_other _ _ (by decide), e1m]
  · rw [hr9, RegFile.write_other _ _ (by decide),
      hr8, RegFile.write_other _ _ (by decide),
      hr7, RegFile.write_other _ _ (by decide),
      hr6, RegFile.write_other _ _ (by decide),
      hr5, RegFile.write_other _ _ (by decide), e4l, hlst]
  · rw [hr9, RegFile.write_other _ _ (by decide),
      hr8, RegFile.write_other _ _ (by decide),
      hr7, RegFile.write_other _ _ (by decide),
      hr6, RegFile.write_other _ _ (by decide), e5l, hlst]
  · rw [hr9, RegFile.write_other _ _ (by decide),
      hr8, RegFile.write_other _ _ (by decide), e7m, hrem, hlst]
  · rw [hr9, RegFile.write_same, hrem, hlst]
  · rw [hr9, RegFile.write_other _ _ (by decide),
      hr8, RegFile.write_other _ _ (by decide),
      hr7, RegFile.write_other _ _ (by decide),
      hr6, RegFile.write_other _ _ (by decide), e5c]
  · intro r hMacro hLocal hMid hRight hT hLeft hRem
    rw [hr9, RegFile.write_other _ _ hRight,
      hr8, RegFile.write_other _ _ hT,
      hr7, RegFile.write_other _ _ hMid,
      hr6, RegFile.write_other _ _ hRem,
      hr5, RegFile.write_other _ _ hLeft,
      hr4, RegFile.write_other _ _ hT,
      hr3, RegFile.write_other _ _ hLocal,
      hr2, RegFile.write_other _ _ hT,
      hr1, RegFile.write_other _ _ hMacro]

/-! ## THE WITNESS LAYOUT AND ITS IMPOSTOR

The real block is 4204 instructions over five heavyweight sub-blocks and
cannot be kernel-executed: `canonicalSummaryLayout`'s `wordScale` routes
through `machineWordBits`, hence `Nat.log2`, hence well-founded
recursion, which the compiler evaluates and the kernel does not.

So the fall-through question is asked at a layout that has the real
one's CONTROL SHAPE and none of its reads: the same nine-instruction
selector, the same five arms in the same order, each arm a marker write
plus a terminator, and the last arm falling through to a `halt`.  What
makes the fixture load-bearing is that **every witness arm ends
un-halted**, exactly as every real sub-block does; a witness arm that
halted at its own end would be the one shape that cannot exhibit the
defect, which is precisely how the close-leg lane's cross-arm defect
stayed invisible.

The markers are written to `mMV`, the real output register, so the
fixture's verdict is stated in the same vocabulary as the block's: the
correct layout leaves `bestOfRegs` reading `none`, the impostor leaves it
reading `some`. -/
def witnessArms (J : Nat) : List Instr :=
  [ Instr.const mMV 0, Instr.brNZ wOne J        -- 9,10   ARM0 -> none
  , Instr.const mMV 5, Instr.brNZ wOne J        -- 11,12  ARM4
  , Instr.const mMV 7, Instr.brNZ wOne J        -- 13,14  ARM6
  , Instr.const mMV 8, Instr.brNZ wOne J        -- 15,16  ARM7
  , Instr.const mMV 9                           -- 17     ARM8, falls through
  , Instr.halt ]                                -- 18     JOIN

/-- The witness selector: the real nine, retargeted at the witness arm
bases.  Same instructions, same order, same categories. -/
def witnessSelector : List Instr :=
  [ Instr.brNZ wCount 2
  , Instr.brNZ wOne 9         -- ARM0
  , Instr.natLe wT wCount wLeft
  , Instr.brNZ wT 11          -- ARM4
  , Instr.brNZ uMid 6
  , Instr.brNZ wOne 13        -- ARM6
  , Instr.brNZ uRight 8
  , Instr.brNZ wOne 15        -- ARM7
  , Instr.brNZ wOne 17 ]      -- ARM8

/-- The correct witness layout. -/
def witnessDispatch : List Instr := witnessSelector ++ witnessArms 18

/-- **THE IMPOSTOR.**  Identical to `witnessDispatch` except that
`ARM0`'s terminator -- instruction `10`, `brNZ wOne 18` -- is an ordinary
register write instead of a branch.

The substitute rewrites `wOne` with the value it already holds, so it is
innocuous in every respect except control: same length, so every branch
target in the layout still points where it pointed; same category
(`registerWrite` for `const` against `branch` for `brNZ` -- see
`unterminatedDispatch_catLogs_differ`); and no register ends with a
different value by its own action.  **The only difference between the two
programs is one instruction's control effect.** -/
def unterminatedArms (J : Nat) : List Instr :=
  [ Instr.const mMV 0, Instr.const wOne 1       -- 9,10   ARM0, NO TERMINATOR
  , Instr.const mMV 5, Instr.brNZ wOne J
  , Instr.const mMV 7, Instr.brNZ wOne J
  , Instr.const mMV 8, Instr.brNZ wOne J
  , Instr.const mMV 9
  , Instr.halt ]

def unterminatedDispatch : List Instr := witnessSelector ++ unterminatedArms 18

@[simp] theorem witnessDispatch_length : witnessDispatch.length = 19 := rfl

@[simp] theorem unterminatedDispatch_length :
    unterminatedDispatch.length = 19 := rfl

/-- The two layouts differ in exactly one instruction, at index `10`. -/
theorem dispatch_layouts_differ_at_one_index :
    (∀ i, i ≠ 10 → witnessDispatch[i]? = unterminatedDispatch[i]?) ∧
      witnessDispatch[10]? = some (Instr.brNZ wOne 18) ∧
      unterminatedDispatch[10]? = some (Instr.const wOne 1) := by
  refine ⟨?_, rfl, rfl⟩
  intro i hi
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 => rfl
  | 10 => exact absurd rfl hi
  | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 => rfl
  | (n + 19) => rfl

/-! ### The two executions

Both are run on the SAME query -- `count = 0`, the branch whose route
answer is `pure none` -- and from the same entry register file.  The
dispatch is correct in both, the selector is correct in both, and the
arm it selects is correct in both.  Only the arm's exit differs. -/

/-- **THE CORRECT LAYOUT.**  `count = 0` selects `ARM0`, which writes the
`none` marker and BRANCHES to the join.  Halts at `18` with `mMV = 0`, so
`bestOfRegs` reads `none` -- the route's answer. -/
theorem witnessDispatch_runs_none (store : ReadStore) (regs : RegFile)
    (hCount : regs wCount = 0) (hOne : regs wOne = 1) :
    ∃ regsF : RegFile,
      RunsTo store witnessDispatch ⟨regs, 0, false⟩ ⟨regsF, 18, true⟩ []
          [Category.branch, Category.branch, Category.registerWrite,
            Category.branch, Category.control] ∧
        bestOfRegs (regsF mMV) (regsF mMP) = none := by
  have s0 : RunsTo store witnessDispatch ⟨regs, 0, false⟩
      ⟨regs, 1, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := witnessDispatch)
      (s := ⟨regs, 0, false⟩) (cond := wCount) (target := 2) rfl rfl
    simpa [hCount] using h
  have s1 : RunsTo store witnessDispatch ⟨regs, 1, false⟩
      ⟨regs, 9, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := witnessDispatch)
      (s := ⟨regs, 1, false⟩) (cond := wOne) (target := 9) rfl rfl
    simpa [hOne] using h
  have s9 : RunsTo store witnessDispatch ⟨regs, 9, false⟩
      ⟨regs.write mMV 0, 10, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs, 9, false⟩) rfl rfl
  have hOne' : (regs.write mMV 0) wOne = 1 := by
    rw [RegFile.write_other _ _ (by decide), hOne]
  have s10 : RunsTo store witnessDispatch ⟨regs.write mMV 0, 10, false⟩
      ⟨regs.write mMV 0, 18, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := witnessDispatch)
      (s := ⟨regs.write mMV 0, 10, false⟩) (cond := wOne) (target := 18)
      rfl rfl
    simpa [hOne'] using h
  have s18 : RunsTo store witnessDispatch ⟨regs.write mMV 0, 18, false⟩
      ⟨regs.write mMV 0, 18, true⟩ [] [Category.control] :=
    RunsTo.halt (s := ⟨regs.write mMV 0, 18, false⟩) rfl rfl
  refine ⟨regs.write mMV 0, ?_, ?_⟩
  · have := ((s0.trans s1).trans s9).trans (s10.trans s18)
    simpa using this
  · simp [bestOfRegs, RegFile.write, mMV]

/--
**THE DISCRIMINATOR.  The unterminated layout reaches the wrong code, by
execution.**

Same store, same entry registers, same query, same correct selector, and
the same correct `ARM0` -- which writes the `none` marker.  Because
`ARM0` does not branch, control runs off its end into `ARM4`'s code,
which overwrites the marker.  The machine halts carrying `5`, so
`bestOfRegs` reads `some (4, _)` where the route reads `none`.

This is the right-shape/wrong-content class at PROGRAM LAYOUT level, and
the third variety of it in `E1_LIVE_STATE.md` §6 -- `some` where the
route is `none` -- arising here from nothing but a missing terminator.
It is the defect the close-leg lane found in `crossBlockArmProgramAt`,
transplanted to the shape `#9` would have had if any of its five arms had
been allowed to end at its sub-block's exit PC. -/
theorem unterminatedDispatch_falls_through (store : ReadStore)
    (regs : RegFile) (hCount : regs wCount = 0) (hOne : regs wOne = 1) :
    ∃ regsF : RegFile,
      RunsTo store unterminatedDispatch ⟨regs, 0, false⟩
          ⟨regsF, 18, true⟩ []
          [Category.branch, Category.branch, Category.registerWrite,
            Category.registerWrite, Category.registerWrite,
            Category.branch, Category.control] ∧
        bestOfRegs (regsF mMV) (regsF mMP) = some (4, regsF mMP) := by
  have s0 : RunsTo store unterminatedDispatch ⟨regs, 0, false⟩
      ⟨regs, 1, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := unterminatedDispatch)
      (s := ⟨regs, 0, false⟩) (cond := wCount) (target := 2) rfl rfl
    simpa [hCount] using h
  have s1 : RunsTo store unterminatedDispatch ⟨regs, 1, false⟩
      ⟨regs, 9, false⟩ [] [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := unterminatedDispatch)
      (s := ⟨regs, 1, false⟩) (cond := wOne) (target := 9) rfl rfl
    simpa [hOne] using h
  have s9 : RunsTo store unterminatedDispatch ⟨regs, 9, false⟩
      ⟨regs.write mMV 0, 10, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs, 9, false⟩) rfl rfl
  -- THE MISSING TERMINATOR: an ordinary register write, so control
  -- simply advances into `ARM4`.
  have s10 : RunsTo store unterminatedDispatch
      ⟨regs.write mMV 0, 10, false⟩
      ⟨(regs.write mMV 0).write wOne 1, 11, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs.write mMV 0, 10, false⟩) rfl rfl
  have s11 : RunsTo store unterminatedDispatch
      ⟨(regs.write mMV 0).write wOne 1, 11, false⟩
      ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 12, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (s := ⟨(regs.write mMV 0).write wOne 1, 11, false⟩) rfl rfl
  have hOne' : (((regs.write mMV 0).write wOne 1).write mMV 5) wOne = 1 := by
    rw [RegFile.write_other _ _ (by decide), RegFile.write_same]
  have s12 : RunsTo store unterminatedDispatch
      ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 12, false⟩
      ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 18, false⟩ []
      [Category.branch] := by
    have h := RunsTo.brNZ (store := store) (program := unterminatedDispatch)
      (s := ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 12, false⟩)
      (cond := wOne) (target := 18) rfl rfl
    simpa [hOne'] using h
  have s18 : RunsTo store unterminatedDispatch
      ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 18, false⟩
      ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 18, true⟩ []
      [Category.control] :=
    RunsTo.halt
      (s := ⟨((regs.write mMV 0).write wOne 1).write mMV 5, 18, false⟩)
      rfl rfl
  refine ⟨((regs.write mMV 0).write wOne 1).write mMV 5, ?_, ?_⟩
  · have := ((s0.trans s1).trans s9).trans
      ((s10.trans s11).trans (s12.trans s18))
    simpa using this
  · simp [bestOfRegs, RegFile.write, mMV]

/-! ### The non-entailments: which checks CANNOT tell the two apart

Stated so the boundary is exact rather than implied, in the style of
`spanNoneArm_discriminates` (`E1InteriorSpanBlock.lean:540`) and
`twoSpanNoneArm_discriminates` (`E1InteriorTwoSpan.lean:1251`). -/

/-- **The exit PC does not separate them, and neither does the halted
flag.**  Both layouts halt, and both halt at `18`.  A check of the form
"the block ends where it should, halted" passes on the impostor.

This is the sharpest of the four non-entailments, because "exits at the
join" is the property a layout check would most naturally be written to
verify, and the fall-through defect PRESERVES it: the impostor reaches
the join too, just with another arm's data. -/
theorem unterminatedDispatch_exit_and_halt_agree :
    ((18 : Nat) = 18) ∧ (true = true) := ⟨rfl, rfl⟩

/-- **The receipt does not separate them AT THIS LAYOUT, and the reason
is a property of the WITNESS, not of the block.**

Both runs emit `[]`, so receipt equality and read count are identical.
But that is because no witness arm reads -- the fixture trades the real
arms for markers precisely so it can be kernel-executed.

`E1_LIVE_STATE.md` §6's sixth model fixes the rule: **a receipt
constrains WHICH READS HAPPENED, so its power over a skipped-code defect
is exactly whether the skipped code READS.**  In the REAL block the
`count = 0` arm falls into `#4`, whose first act is the unconditional
level read at the head of `twoSpanBlock`, so the real receipt WOULD
carry an event the route never emitted and WOULD catch this.  **The
blindness recorded here is the witness's, and it must not be quoted as
the block's.** -/
theorem unterminatedDispatch_receipts_agree :
    ([] : List TraceEvent) = ([] : List TraceEvent) := rfl

/-- **What DOES separate them, besides the value: the positional category
log.**  The fall-through changes the CONTROL PATH -- it substitutes a
`registerWrite` for a `branch` and then executes a whole extra arm -- so
the logs differ in length as well as content.

By §6's fifth model this is the expected side of the line: a category log
constrains which instructions ran, and this defect changes which
instructions ran.  It is `mergePos`-style defects, which preserve the
path, that a category log cannot see. -/
theorem unterminatedDispatch_catLogs_differ :
    ([Category.branch, Category.branch, Category.registerWrite,
        Category.branch, Category.control] : List Category) ≠
      [Category.branch, Category.branch, Category.registerWrite,
        Category.registerWrite, Category.registerWrite,
        Category.branch, Category.control] := by decide

/-- **And the values differ**: `none` against `some`.  With
`witnessDispatch_runs_none` and `unterminatedDispatch_falls_through` this
is the pair that makes the value clause of `#9`'s simulation
load-bearing rather than decorative. -/
theorem unterminatedDispatch_values_differ (bp : Nat) :
    bestOfRegs 0 bp ≠ bestOfRegs 5 bp := by
  simp [bestOfRegs]

end E1InteriorDispatch
end WordRAM
end RMQ
