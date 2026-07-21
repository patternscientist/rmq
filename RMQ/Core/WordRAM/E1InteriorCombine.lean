import RMQ.Core.WordRAM.E1InteriorTwoSpan

/-! # E1 amended machine: the interior's READ-FREE COMBINERS (#6, #7, #8)

`canonicalRelativeRmmMachineAdjacentMacroCandidateComputation`
(`InteriorDirectory.lean:2400`),
`...LeftMiddleMacroCandidateComputation` (`:2413`) and
`...CrossMacroCandidateComputation` (`:2426`) are the interior's three
macro combiners.  None of them reads: each is a `bind`/`map` over
sub-legs that read, and the combination itself is `bpCandidateMerge?`.

`#6` and `#7` have ONE shape between them -- two sub-legs merged --
differing only in whether the SECOND leg is local or global:

* `#6` -- local `(macroStart, localStart, macroSize - localStart)` then
  local `(macroStart + 1, 0, rightCount)`;
* `#7` -- the same left leg, then global `(macroStart + 1,
  middleMacroCount)`.

`#8` is `#7`'s two legs followed by a third, local
`(macroStart + 1 + middleMacroCount, 0, rightCount)`, merged in --
`bpCandidateMerge3?` being DEFINITIONALLY two two-way merges
(`merge3_eq_two_merges`, `E1InteriorMerge.lean:593`).

## The uniformity that makes one block cover both

A local leg needs `tA = macroIdx * (levelCount * macroSize)` and
`tOff = macroIdx * macroSize`; a global leg needs `tA = 0` and
`tOff = 0`.  Written as `mulConst` by a PROGRAM CONSTANT those are the
same two instructions -- `mulConst dst src 0` is `src * 0` -- so
`legSetup` is one four-instruction shape with one category log
(`[arithmetic, registerWrite, registerWrite, arithmetic]`) at both, and
no branch distinguishes a local leg from a global one.

Without that, the two setups would differ in CATEGORY as well as in
content, and `#6` and `#7` would need separate charge logs for a
difference that is not observable in the route.

## STATE OF THIS MODULE -- READ BEFORE BUILDING ON IT

**PROVED:** `legSetup_runsTo`, and now `twoLegBlock_runsTo` -- the exact
simulation of the whole 1044-instruction combiner, with receipt, charge
log, route value and preservation.

~~**DEFINED BUT NOT YET SIMULATED:** `twoLegBlock` ... **`twoLegBlock_runsTo`
DOES NOT EXIST**, so nothing here yet entitles anyone to say `#6` or `#7`
is closed.~~ **SUPERSEDED (E1-LaneB4).** The simulation exists; `#6` and
`#7` are instantiated below.  Left struck through rather than deleted, per
the standing rule.

**A DEFECT THE SIMULATION EXPOSED, recorded because it is the module's
main lesson.**  `TwoLegUntouched` as first written was UNSOUND for its own
block -- it omitted the four two-span inputs `tA`/`tStart`/`tN`/`tOff`,
which this combiner WRITES in its two `legSetup`s, so it was provable at
four registers the block clobbers.  Nothing catches that while a block is
merely DEFINED.  See the predicate's own doc comment; DD-20260719-056.

## THE CORRECTION, AND WHY THE BLOCK LOOKS THE WAY IT DOES

The natural combiner -- stash the first sub-leg's candidate in
`qLV`/`qLP` with `mergeShuttle`, run the second sub-leg, merge -- IS
WRONG.  `twoSpanBlock` CONTAINS a `mergeShuttle` and a `mergeBlock`, so
it writes `qLV`/`qLP` itself; the second sub-leg destroys the stash.
`E1InteriorTwoSpan.twoSpanUntouched_excludes_mergeStash` proves this
rather than leaving it to inspection, and `E1_LIVE_STATE.md` §2's
"chaining does need a two-instruction shuttle, which exists" is true one
level DOWN and not sufficient one level UP.

So this block carries its OWN stash pair, `uSV`/`uSP` at `142`/`143`,
stashes after the first sub-leg and restores into `qLV`/`qLP` only after
the second one has finished -- two moves each, replacing the shuttle.
**Every nesting level needs its own stash pair**, so `#8`'s third leg will
need a third, and so will `#9` if it ever stashes across a dispatch arm.

This was caught by the type checker (`TwoSpanUntouched qLV` is
unprovable, because it is FALSE), not by a fixture.  Worth recording as a
case where the preservation predicate did its job at the composition site
rather than at the block that stated it.

DD-20260719-055.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorCombine

open E1Machine
open RMQ.SuccinctClose
open E1FringeFoldBlock (bestOfRegs)
open E1CandMerge3 (mMV mMP)
open E1InteriorSummaryGroup (TableGeom SummaryLayout canonicalSummaryLayout)
open E1InteriorSpanBlock (SpanUntouched)
open E1InteriorMerge (qLV qLP mergeBlock mergeCats MergeUntouched mergeShuttle
  ShuttleUntouched)
open E1InteriorTwoSpan (tA tStart tN tOff twoSpanBlock twoSpanEvents
  twoSpanCats twoSpanValue TwoSpanUntouched)

/-! ## Registers

The interior's fourth new bank, opening at `136`.  `uMacro`, `uLocal`,
`uMid` and `uRight` are INPUTS the caller writes; `uT` and `uZero` are
scratch.  Every one of them is above `135`, so `TwoSpanUntouched` covers
the whole bank and a sub-leg cannot disturb a later leg's inputs. -/

/-- Input: `macroStart`. -/
abbrev uMacro : Nat := 136
/-- Input: `localStart`. -/
abbrev uLocal : Nat := 137
/-- Input: `middleMacroCount`. -/
abbrev uMid : Nat := 138
/-- Input: `rightCount`. -/
abbrev uRight : Nat := 139
/-- Scratch: `leftCount`, then `macroStart + 1`. -/
abbrev uT : Nat := 140
/-- Scratch: the constant `0`, a source for legs whose start is `0`. -/
abbrev uZero : Nat := 141

/-- Scratch: the OUTER stash of the first sub-leg's candidate value.

NOT `qLV`: `twoSpanBlock` contains a shuttle and a merge and therefore
WRITES `qLV`/`qLP` (`twoSpanUntouched_excludes_mergeStash`), so a
candidate stashed there would be destroyed by the second sub-leg.  Each
nesting level needs its own stash pair; this is the combiner's. -/
abbrev uSV : Nat := 142

/-- Scratch: the outer stash of the first sub-leg's candidate position. -/
abbrev uSP : Nat := 143

/-! ## One leg's input setup -/

/-- FOUR INSTRUCTIONS setting a two-span leg's four inputs.

`kA` and `kO` are program constants: `(levelCount * macroSize, macroSize)`
for a local leg, `(0, 0)` for a global one.  `mulConst _ _ 0` is what lets
the global leg reuse the local leg's instruction shape rather than needing
its own. -/
def legSetup (kA kO srcMacro srcStart srcN : Nat) : List Instr :=
  [ Instr.mulConst tA srcMacro kA
  , Instr.move tStart srcStart
  , Instr.move tN srcN
  , Instr.mulConst tOff srcMacro kO ]

@[simp] theorem legSetup_length (kA kO srcMacro srcStart srcN : Nat) :
    (legSetup kA kO srcMacro srcStart srcN).length = 4 := rfl

/-- A setup's charge log: the same at a local leg and a global one. -/
def legSetupCats : List Category :=
  [Category.arithmetic, Category.registerWrite, Category.registerWrite,
    Category.arithmetic]

/-- EXACT SIMULATION OF ONE SETUP.  Read-free, four writes, and it leaves
the whole combiner bank alone -- which is what lets the SECOND setup run
after the first leg without restating the caller's inputs.

THE THREE SOURCE PREMISES ARE NOT DECORATIVE.  The four destinations are
`127`-`130` and every source this block is instantiated at lives in the
combiner bank at `136`+, so `136 <= src` is exactly what makes each
source still readable when its instruction runs -- a setup whose source
coincided with an earlier destination would silently read the value just
written.  They are stated as numeric bounds rather than as four
disequalities because the bound is the fact the register allocation
guarantees. -/
theorem legSetup_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {kA kO srcMacro srcStart srcN Q : Nat} {regs : RegFile}
    (hHost : HostedAt program Q (legSetup kA kO srcMacro srcStart srcN))
    (hbM : 136 ≤ srcMacro) (hbS : 136 ≤ srcStart) (hbN : 136 ≤ srcN) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 4, false⟩ []
        legSetupCats ∧
      regs' tA = regs srcMacro * kA ∧ regs' tStart = regs srcStart ∧
      regs' tN = regs srcN ∧ regs' tOff = regs srcMacro * kO ∧
      (∀ r, r ≠ tA → r ≠ tStart → r ≠ tN → r ≠ tOff → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 4 →
      (legSetup kA kO srcMacro srcStart srcN)[k]? = some instr → Q + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.mulConst tA srcMacro kA) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.move tStart srcStart) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.move tN srcN) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.mulConst tOff srcMacro kO) :=
    hf 3 _ _ (by omega) rfl (by omega)
  -- the sources outrank every destination, so each still reads the
  -- caller's value when its own instruction runs
  have hSA : srcStart ≠ tA := by simp only [tA]; omega
  have hNA : srcN ≠ tA := by simp only [tA]; omega
  have hNS : srcN ≠ tStart := by simp only [tStart]; omega
  have hMA : srcMacro ≠ tA := by simp only [tA]; omega
  have hMS : srcMacro ≠ tStart := by simp only [tStart]; omega
  have hMN : srcMacro ≠ tN := by simp only [tN]; omega
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write tA (regs srcMacro * kA) :=
    ⟨_, rfl⟩
  have s0 : RunsTo store program ⟨regs, Q, false⟩ ⟨r1, Q + 1, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr1] using h
  have hv1S : r1 srcStart = regs srcStart := by
    rw [hr1, RegFile.write_other _ _ hSA]
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write tStart (regs srcStart) :=
    ⟨_, rfl⟩
  have s1 : RunsTo store program ⟨r1, Q + 1, false⟩ ⟨r2, Q + 2, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1
    rw [hr2, ← hv1S]
    simpa using h
  have hv2N : r2 srcN = regs srcN := by
    rw [hr2, RegFile.write_other _ _ hNS, hr1, RegFile.write_other _ _ hNA]
  obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write tN (regs srcN) := ⟨_, rfl⟩
  have s2 : RunsTo store program ⟨r2, Q + 2, false⟩ ⟨r3, Q + 3, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨r2, Q + 2, false⟩ : State)) rfl h2
    rw [hr3, ← hv2N]
    simpa using h
  have hv3M : r3 srcMacro = regs srcMacro := by
    rw [hr3, RegFile.write_other _ _ hMN, hr2, RegFile.write_other _ _ hMS,
      hr1, RegFile.write_other _ _ hMA]
  obtain ⟨r4, hr4⟩ : ∃ z : RegFile, z = r3.write tOff (regs srcMacro * kO) :=
    ⟨_, rfl⟩
  have s3 : RunsTo store program ⟨r3, Q + 3, false⟩ ⟨r4, Q + 4, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.mulConst (store := store)
      (s := (⟨r3, Q + 3, false⟩ : State)) rfl h3
    rw [hr4, ← hv3M]
    simpa using h
  refine ⟨r4, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have hrun := ((s0.trans s1).trans s2).trans s3
    simpa [legSetupCats] using hrun
  · rw [hr4, RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1, RegFile.write_same]
  · rw [hr4, RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2, RegFile.write_same]
  · rw [hr4, RegFile.write_other _ _ (by decide), hr3, RegFile.write_same]
  · rw [hr4, RegFile.write_same]
  · intro r hA hS hN hO
    rw [hr4, RegFile.write_other _ _ hO, hr3, RegFile.write_other _ _ hN,
      hr2, RegFile.write_other _ _ hS, hr1, RegFile.write_other _ _ hA]

/-! ## THE TWO-LEG COMBINER: `#6` AND `#7` -/

/-- THE TWO-LEG COMBINER (1044 instructions, exit `Q + 1044`).

DEFINED ONLY -- its exact simulation is OWED; see the module header.

Prologue (`leftCount := macroSize - localStart`, and the zero source),
the left leg's setup, a two-span block, the OUTER STASH, `macroStart + 1`,
the second leg's setup, a second two-span block, the RESTORE, and the
merge.

READ-FREE IN ITSELF: every read is inside one of the two sub-legs, which
is what `#6` and `#7` being `bind`/`map` combinations of sub-legs means
(`InteriorDirectory.lean:2406`, `:2419`). -/
def twoLegBlock (L : SummaryLayout) (GL1 GS1 GL2 GS2 : TableGeom)
    (M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat) : List Instr :=
  [ Instr.const uZero 0        -- Q+0
  , Instr.const uT macroSize   -- Q+1
  , Instr.sub uT uT uLocal ] ++ -- Q+2  leftCount := macroSize - localStart
    (legSetup kA1 kO1 uMacro uLocal uT ++          -- Q+3 .. Q+6
      (twoSpanBlock L GL1 GS1 M1 D1 blockSize blocksPerSuper (Q + 7) ++
        ([ Instr.move uSV mMV                       -- Q+516  OUTER stash
          , Instr.move uSP mMP ] ++                 -- Q+517  (NOT qLV/qLP)
          ([ Instr.const uT 1                       -- Q+518
            , Instr.add uT uMacro uT ] ++           -- Q+519  macroStart + 1
            (legSetup kA2 kO2 uT srcStart2 srcN2 ++ -- Q+520 .. Q+523
              (twoSpanBlock L GL2 GS2 M2 D2 blockSize blocksPerSuper
                  (Q + 524) ++
                ([ Instr.move qLV uSV               -- Q+1033 restore, AFTER
                  , Instr.move qLP uSP ] ++         -- Q+1034 the sub-leg
                  mergeBlock (Q + 1035))))))))

@[simp] theorem twoLegBlock_length (L : SummaryLayout)
    (GL1 GS1 GL2 GS2 : TableGeom)
    (M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat) :
    (twoLegBlock L GL1 GS1 GL2 GS2 M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2
      srcN2 macroSize blockSize blocksPerSuper Q).length = 1044 := by
  simp [twoLegBlock]

/-- The combiner's charge log: the prologue, the two setups, the two
sub-legs' own logs, the shuttle, the two `uT` instructions and the merge. -/
def twoLegCats (catsA catsB : List Category)
    (valA valB : Option (Nat × Nat)) : List Category :=
  [Category.registerWrite, Category.registerWrite, Category.arithmetic] ++
    (legSetupCats ++
      (catsA ++
        ([Category.registerWrite, Category.registerWrite,
            Category.registerWrite, Category.arithmetic] ++
          (legSetupCats ++
            (catsB ++
              ([Category.registerWrite, Category.registerWrite] ++
                mergeCats valA valB))))))

/-- What the combiner LEAVES ALONE.

**THIS SUPERSEDES THE FIRST VERSION OF THIS PREDICATE, WHICH WAS UNSOUND
FOR ITS OWN BLOCK.**  The original read

    TwoSpanUntouched r ∧ MergeUntouched r ∧ ShuttleUntouched r ∧
      r ≠ uT ∧ r ≠ uZero ∧ r ≠ uSV ∧ r ≠ uSP

and omitted the four two-span INPUTS `tA`, `tStart`, `tN`, `tOff`
(`127`-`130`).  `TwoSpanUntouched` omits them DELIBERATELY and correctly --
`twoSpanBlock` only READS them, never writes them, and saying so is what
lets `#6`-`#9` chain two sub-legs with only some inputs rewritten between.
But `twoLegBlock` WRITES all four, TWICE, in its two `legSetup`s.  So the
old predicate was provable at four registers the combiner clobbers
(`TwoLegUntouched 127` closed by `decide`), and the preservation clause of
`twoLegBlock_runsTo` stated with it would have been FALSE.

Nothing catches this while a block is only DEFINED: a preservation
predicate is not executed until a simulation quantifies over it, and the
`at_crossBlockArm_operands` evaluation below passes under BOTH versions,
because `70`/`71`/`75`/`76` are not among the registers at issue.  A
predicate can be too WEAK (the `SpanUntouched`/`mLP` case recorded in
`E1_LIVE_STATE.md` §9) or, as here, too STRONG, and only the consumer's
proof obligation distinguishes them.

Recorded rather than silently repaired, per the standing rule.
DD-20260719-056. -/
abbrev TwoLegUntouched (r : Nat) : Prop :=
  TwoSpanUntouched r ∧ MergeUntouched r ∧ ShuttleUntouched r ∧
    r ≠ tA ∧ r ≠ tStart ∧ r ≠ tN ∧ r ≠ tOff ∧
    r ≠ uT ∧ r ≠ uZero ∧ r ≠ uSV ∧ r ≠ uSP

/-- THE FOUR CROSS-BLOCK-ARM OPERANDS SURVIVE THE WHOLE COMBINER.

The ten numeral conjuncts are EVALUATED; only the leading
`TwoSpanUntouched` comes from the sub-block's own twin.  A whole-statement
`by decide` does NOT work here and the failure is worth recording: with
eleven conjuncts, four of them instantiated, `Decidable` instance
synthesis gives up ("failed to synthesize Decidable (TwoLegUntouched 70 ∧
...)") even though every leaf is a decidable numeral comparison and the
SAME predicate decides fine at a single register.  Depth, not
decidability. -/
theorem twoLegUntouched_at_crossBlockArm_operands :
    TwoLegUntouched 70 ∧ TwoLegUntouched 71 ∧ TwoLegUntouched 75 ∧
      TwoLegUntouched 76 :=
  ⟨⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.2.2,
      by decide, by decide, by decide, by decide, by decide, by decide,
      by decide, by decide, by decide, by decide⟩⟩

/-- **THE WHOLE WRITE SET LIES BELOW `144`.**

The combiner's twin of `twoSpanUntouched_of_ge`, and the reason `#8` can
carry a THIRD stash pair at `144`/`145` across a two-leg sub-block without
re-deciding eleven conjuncts.  `144` is one past `uSP`, the highest
register this block writes.

Numerals, not the register abbrevs, for the reason
`twoSpanUntouched_of_ge` records: `omega` collects an `abbrev` as an
unreduced atom. -/
theorem twoLegUntouched_of_ge {r : Nat} (h : 144 ≤ r) : TwoLegUntouched r :=
  ⟨E1InteriorTwoSpan.twoSpanUntouched_of_ge (by omega),
    ⟨show r ≠ 77 by omega, show r ≠ 78 by omega, show r ≠ 125 by omega,
      show r ≠ 126 by omega⟩,
    ⟨show r ≠ 123 by omega, show r ≠ 124 by omega⟩,
    show r ≠ 127 by omega, show r ≠ 128 by omega, show r ≠ 129 by omega,
    show r ≠ 130 by omega, show r ≠ 140 by omega, show r ≠ 141 by omega,
    show r ≠ 142 by omega, show r ≠ 143 by omega⟩

/-- The combiner-bank version, and the one the INPUT registers need.

`uMacro`, `uLocal`, `uMid` and `uRight` sit at `136`-`139`, BELOW the
block's own scratch, so `twoLegUntouched_of_ge` does not reach them --
yet a caller chaining a second combiner after this one has to carry them
across.  Any register at `136`+ that is not one of the four slots this
block writes for itself is left alone. -/
theorem twoLegUntouched_of_bank {r : Nat} (h : 136 ≤ r) (hT : r ≠ uT)
    (hZ : r ≠ uZero) (hV : r ≠ uSV) (hP : r ≠ uSP) : TwoLegUntouched r :=
  ⟨E1InteriorTwoSpan.twoSpanUntouched_of_ge h,
    ⟨show r ≠ 77 by omega, show r ≠ 78 by omega, show r ≠ 125 by omega,
      show r ≠ 126 by omega⟩,
    ⟨show r ≠ 123 by omega, show r ≠ 124 by omega⟩,
    show r ≠ 127 by omega, show r ≠ 128 by omega, show r ≠ 129 by omega,
    show r ≠ 130 by omega, hT, hZ, hV, hP⟩

/-! ## Exact simulation of the two-leg combiner -/

/--
EXACT SIMULATION OF THE TWO-LEG COMBINER, PARAMETRIC IN BOTH SUB-LEGS.

Exit `Q + 1044`.  The receipt is the two sub-legs' receipts CONCATENATED
and nothing else: everything outside them -- prologue, both setups, stash,
bump, restore, merge -- is read-free, which is exactly what `#6` and `#7`
being `bind`/`map` combinations of sub-legs means
(`InteriorDirectory.lean:2406`, `:2419`).  The value is the ROUTE's own
`bpCandidateMerge?` of the two sub-legs' route values, not the block's
arithmetic.

NO STORE HYPOTHESIS AND NO VALIDITY HYPOTHESIS, both inherited from
`twoSpanBlock_runsTo`.

**`hS2`/`hN2` ARE WHAT MAKE `#6` AND `#7` ONE BLOCK, AND THEY ARE NOT
DECORATIVE.**  The second leg's start and count come from DIFFERENT
registers at the two instantiations -- `(uZero, uRight)` at `#6`,
`(uT, uMid)` at `#7` -- so the block cannot name them.  It instead takes a
function from the six combiner-bank readings that hold when the second
setup runs to the value that source carries.  At each instantiation the
witness is a PROJECTION of those six readings, so the premise is
discharged by picking one hypothesis and not by an argument:
`#6`'s start witness is the `uZero` reading, `#7`'s is the `uT` reading
(see `adjacentMacro_runsTo` and `leftMiddleMacro_runsTo`).

The premise is NOT vacuous: the six readings constrain six DISTINCT
registers (`136`, `137`, `138`, `139`, `141`, `140`) at independent
values, so a `RegFile` satisfying all six exists, and the two
instantiations below exhibit one each.  A block that instead took
`start2`/`n2` as bare naturals with no tie to a register would be
satisfied by a setup reading the WRONG register that happened to hold the
right value.
-/
theorem twoLegBlock_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {GL1 GS1 GL2 GS2 : TableGeom}
    {M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2 macroSize Q : Nat}
    {macroStart localStart mid right start2 n2 : Nat} {regs : RegFile}
    (hHost : HostedAt program Q
      (twoLegBlock (canonicalSummaryLayout shape) GL1 GS1 GL2 GS2
        M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2 macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper Q))
    (hMacro : regs uMacro = macroStart) (hLocal : regs uLocal = localStart)
    (hMid : regs uMid = mid) (hRight : regs uRight = right)
    (hbS2 : 136 ≤ srcStart2) (hbN2 : 136 ≤ srcN2)
    (hS2 : ∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r srcStart2 = start2)
    (hN2 : ∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r srcN2 = n2)
    (hL1Pos : 0 < GL1.chunkCount) (hL1Cap : GL1.chunkCount ≤ 8)
    (hS1Pos : 0 < GS1.chunkCount) (hS1Cap : GS1.chunkCount ≤ 8)
    (hL2Pos : 0 < GL2.chunkCount) (hL2Cap : GL2.chunkCount ≤ 8)
    (hS2Pos : 0 < GS2.chunkCount) (hS2Cap : GS2.chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 1044, false⟩
          (twoSpanEvents shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1) ++
            twoSpanEvents shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2))
          (twoLegCats
            (twoSpanCats shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1))
            (twoSpanCats shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2))
            (twoSpanValue shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1))
            (twoSpanValue shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2))) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          bpCandidateMerge?
            (twoSpanValue shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1))
            (twoSpanValue shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2)) ∧
        (∀ r, TwoLegUntouched r → regs' r = regs r) := by
  -- ## hosting, peeled in the block's own append order.  Each suffix's BASE
  -- is normalised IN PLACE rather than re-ascribed: ascribing would mean
  -- spelling out the remaining sub-blocks at every one of the eight steps,
  -- and a `_` for the suffix does not elaborate.
  have hPro : HostedAt program Q
      [Instr.const uZero 0, Instr.const uT macroSize,
        Instr.sub uT uT uLocal] := hHost.append_left
  have hR1 := hHost.append_right (code₁ := [Instr.const uZero 0,
    Instr.const uT macroSize, Instr.sub uT uT uLocal])
  rw [show Q + [Instr.const uZero 0, Instr.const uT macroSize,
    Instr.sub uT uT uLocal].length = Q + 3 from rfl] at hR1
  have hSet1 : HostedAt program (Q + 3)
      (legSetup kA1 kO1 uMacro uLocal uT) := hR1.append_left
  have hR2 := hR1.append_right (code₁ := legSetup kA1 kO1 uMacro uLocal uT)
  rw [show Q + 3 + (legSetup kA1 kO1 uMacro uLocal uT).length = Q + 7 from by
    simp only [legSetup_length]] at hR2
  have hSpan1 : HostedAt program (Q + 7)
      (twoSpanBlock (canonicalSummaryLayout shape) GL1 GS1 M1 D1
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 7)) :=
    hR2.append_left
  have hR3 := hR2.append_right
    (code₁ := twoSpanBlock (canonicalSummaryLayout shape) GL1 GS1 M1 D1
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 7))
  rw [show Q + 7 + (twoSpanBlock (canonicalSummaryLayout shape) GL1 GS1 M1 D1
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 7)).length
      = Q + 516 from by
    simp only [E1InteriorTwoSpan.twoSpanBlock_length]] at hR3
  have hStash : HostedAt program (Q + 516)
      [Instr.move uSV mMV, Instr.move uSP mMP] := hR3.append_left
  have hR4 := hR3.append_right
    (code₁ := [Instr.move uSV mMV, Instr.move uSP mMP])
  rw [show Q + 516 + [Instr.move uSV mMV, Instr.move uSP mMP].length
    = Q + 518 from rfl] at hR4
  have hBump : HostedAt program (Q + 518)
      [Instr.const uT 1, Instr.add uT uMacro uT] := hR4.append_left
  have hR5 := hR4.append_right
    (code₁ := [Instr.const uT 1, Instr.add uT uMacro uT])
  rw [show Q + 518 + [Instr.const uT 1, Instr.add uT uMacro uT].length
    = Q + 520 from rfl] at hR5
  have hSet2 : HostedAt program (Q + 520)
      (legSetup kA2 kO2 uT srcStart2 srcN2) := hR5.append_left
  have hR6 := hR5.append_right (code₁ := legSetup kA2 kO2 uT srcStart2 srcN2)
  rw [show Q + 520 + (legSetup kA2 kO2 uT srcStart2 srcN2).length = Q + 524
    from by simp only [legSetup_length]] at hR6
  have hSpan2 : HostedAt program (Q + 524)
      (twoSpanBlock (canonicalSummaryLayout shape) GL2 GS2 M2 D2
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 524)) :=
    hR6.append_left
  have hR7 := hR6.append_right
    (code₁ := twoSpanBlock (canonicalSummaryLayout shape) GL2 GS2 M2 D2
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 524))
  rw [show Q + 524 + (twoSpanBlock (canonicalSummaryLayout shape) GL2 GS2 M2 D2
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 524)).length
      = Q + 1033 from by
    simp only [E1InteriorTwoSpan.twoSpanBlock_length]] at hR7
  have hRest : HostedAt program (Q + 1033)
      [Instr.move qLV uSV, Instr.move qLP uSP] := hR7.append_left
  have hMergeH : HostedAt program (Q + 1035) (mergeBlock (Q + 1035)) := by
    have h := hR7.append_right
      (code₁ := [Instr.move qLV uSV, Instr.move qLP uSP])
    rw [show Q + 1033 + [Instr.move qLV uSV, Instr.move qLP uSP].length
      = Q + 1035 from rfl] at h
    exact h
  -- ## Q+0 .. Q+2: the prologue
  have f0 : program[Q]? = some (Instr.const uZero 0) := hPro.head
  have f1 : program[Q + 1]? = some (Instr.const uT macroSize) := by
    have h := hPro.tail.head
    simpa using h
  have f2 : program[Q + 2]? = some (Instr.sub uT uT uLocal) := by
    have h := hPro.tail.tail.head
    have harith : Q + 1 + 1 = Q + 2 := by omega
    rwa [harith] at h
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write uZero 0 := ⟨_, rfl⟩
  have s0 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨regs, Q, false⟩ ⟨r1, Q + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨regs, Q, false⟩ : State)) rfl f0
    simpa [hr1] using h
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write uT macroSize := ⟨_, rfl⟩
  have s1 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r1, Q + 1, false⟩ ⟨r2, Q + 2, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r1, Q + 1, false⟩ : State)) rfl f1
    simpa [hr2] using h
  have hr2T : r2 uT = macroSize := by rw [hr2, RegFile.write_same]
  have hr2L : r2 uLocal = localStart := by
    rw [hr2, RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide)]
    exact hLocal
  obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write uT (macroSize - localStart) :=
    ⟨_, rfl⟩
  have s2 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r2, Q + 2, false⟩ ⟨r3, Q + 3, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.sub
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r2, Q + 2, false⟩ : State)) rfl f2
    simpa [hr3, hr2T, hr2L] using h
  -- what the prologue leaves for the first setup
  have h3M : r3 uMacro = macroStart := by
    rw [hr3, RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide)]
    exact hMacro
  have h3L : r3 uLocal = localStart := by
    rw [hr3, RegFile.write_other _ _ (by decide)]; exact hr2L
  have h3T : r3 uT = macroSize - localStart := by
    rw [hr3, RegFile.write_same]
  -- ## Q+3 .. Q+6: the left leg's setup
  obtain ⟨r4, sSet1, h4A, h4S, h4N, h4O, h4P⟩ :=
    legSetup_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (regs := r3) hSet1 (by decide) (by decide) (by decide)
  rw [h3M] at h4A
  rw [h3L] at h4S
  rw [h3T] at h4N
  rw [h3M] at h4O
  -- ## Q+7 .. Q+515: the left sub-leg
  obtain ⟨r5, sSpan1, hVal1, hPres1⟩ :=
    E1InteriorTwoSpan.twoSpanBlock_runsTo shape hSpan1 h4A h4S h4N h4O hL1Pos hL1Cap hS1Pos
      hS1Cap
  -- ## Q+516, Q+517: the OUTER stash
  have f516 : program[Q + 516]? = some (Instr.move uSV mMV) := hStash.head
  have f517 : program[Q + 517]? = some (Instr.move uSP mMP) := by
    have h := hStash.tail.head
    have harith : Q + 516 + 1 = Q + 517 := by omega
    rwa [harith] at h
  obtain ⟨r6, hr6⟩ : ∃ z : RegFile, z = r5.write uSV (r5 mMV) := ⟨_, rfl⟩
  have s516 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r5, Q + 516, false⟩ ⟨r6, Q + 517, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r5, Q + 516, false⟩ : State)) rfl f516
    simpa [hr6] using h
  have hr6P : r6 mMP = r5 mMP := by
    rw [hr6, RegFile.write_other _ _ (by decide)]
  obtain ⟨r7, hr7⟩ : ∃ z : RegFile, z = r6.write uSP (r5 mMP) := ⟨_, rfl⟩
  have s517 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r6, Q + 517, false⟩ ⟨r7, Q + 518, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r6, Q + 517, false⟩ : State)) rfl f517
    simpa [hr7, hr6P] using h
  -- ## Q+518, Q+519: `macroStart + 1`
  have f518 : program[Q + 518]? = some (Instr.const uT 1) := hBump.head
  have f519 : program[Q + 519]? = some (Instr.add uT uMacro uT) := by
    have h := hBump.tail.head
    have harith : Q + 518 + 1 = Q + 519 := by omega
    rwa [harith] at h
  obtain ⟨r8, hr8⟩ : ∃ z : RegFile, z = r7.write uT 1 := ⟨_, rfl⟩
  have s518 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r7, Q + 518, false⟩ ⟨r8, Q + 519, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r7, Q + 518, false⟩ : State)) rfl f518
    simpa [hr8] using h
  -- a combiner-bank register survives the stash, the bump seed and the sub-leg
  -- A combiner-bank register survives the left setup, the left sub-leg, the
  -- stash and the bump seed.  `r ≠ uZero` is REQUIRED and was missing from
  -- the first version of this helper: the prologue's `const uZero 0` is the
  -- very first instruction, so the claim is FALSE at `141`.  The four
  -- disequalities against the setup's destinations are spelled as NUMERALS
  -- because `omega` collects a register `abbrev` as an unreduced atom -- the
  -- same trap `twoSpanUntouched_of_ge` records.
  have hBank : ∀ r : Nat, 136 ≤ r → r ≠ uT → r ≠ uZero → r ≠ uSV → r ≠ uSP →
      r8 r = regs r := by
    intro r hge hT hZ hV hP
    rw [hr8, RegFile.write_other _ _ hT, hr7, RegFile.write_other _ _ hP,
      hr6, RegFile.write_other _ _ hV,
      hPres1 r (E1InteriorTwoSpan.twoSpanUntouched_of_ge hge),
      h4P r (show r ≠ 127 by omega) (show r ≠ 128 by omega)
        (show r ≠ 129 by omega) (show r ≠ 130 by omega), hr3,
      RegFile.write_other _ _ hT, hr2, RegFile.write_other _ _ hT, hr1,
      RegFile.write_other _ _ hZ]
  have h8M : r8 uMacro = macroStart := by
    rw [hBank uMacro (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hMacro
  have h8T : r8 uT = 1 := by rw [hr8, RegFile.write_same]
  obtain ⟨r9, hr9⟩ : ∃ z : RegFile, z = r8.write uT (macroStart + 1) :=
    ⟨_, rfl⟩
  have s519 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
      ⟨r8, Q + 519, false⟩ ⟨r9, Q + 520, false⟩ [] [Category.arithmetic] := by
    have h := RunsTo.add
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r8, Q + 519, false⟩ : State)) rfl f519
    simpa [hr9, h8M, h8T] using h
  -- the six readings that pin the second leg's sources
  have h9M : r9 uMacro = macroStart := by
    rw [hr9, RegFile.write_other _ _ (by decide)]; exact h8M
  have h9L : r9 uLocal = localStart := by
    rw [hr9, RegFile.write_other _ _ (by decide),
      hBank uLocal (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hLocal
  have h9Mid : r9 uMid = mid := by
    rw [hr9, RegFile.write_other _ _ (by decide),
      hBank uMid (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hMid
  have h9R : r9 uRight = right := by
    rw [hr9, RegFile.write_other _ _ (by decide),
      hBank uRight (by decide) (by decide) (by decide) (by decide) (by decide)]
    exact hRight
  have h9Z : r9 uZero = 0 := by
    rw [hr9, RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide),
      hPres1 uZero (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
      h4P uZero (by decide) (by decide) (by decide) (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1, RegFile.write_same]
  have h9T : r9 uT = macroStart + 1 := by rw [hr9, RegFile.write_same]
  -- ## Q+520 .. Q+523: the second leg's setup
  obtain ⟨r10, sSet2, h10A, h10S, h10N, h10O, h10P⟩ :=
    legSetup_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (regs := r9) hSet2 (by decide) hbS2 hbN2
  rw [h9T] at h10A h10O
  rw [hS2 r9 h9M h9L h9Mid h9R h9Z h9T] at h10S
  rw [hN2 r9 h9M h9L h9Mid h9R h9Z h9T] at h10N
  -- ## Q+524 .. Q+1032: the second sub-leg
  obtain ⟨r11, sSpan2, hVal2, hPres2⟩ :=
    E1InteriorTwoSpan.twoSpanBlock_runsTo shape hSpan2 h10A h10S h10N h10O hL2Pos hL2Cap hS2Pos
      hS2Cap
  -- ## Q+1033, Q+1034: the RESTORE, after the second sub-leg
  have f1033 : program[Q + 1033]? = some (Instr.move qLV uSV) := hRest.head
  have f1034 : program[Q + 1034]? = some (Instr.move qLP uSP) := by
    have h := hRest.tail.head
    have harith : Q + 1033 + 1 = Q + 1034 := by omega
    rwa [harith] at h
  have h11V : r11 uSV = r5 mMV := by
    rw [hPres2 uSV (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
      h10P uSV (by decide) (by decide) (by decide) (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6, RegFile.write_same]
  have h11P : r11 uSP = r5 mMP := by
    rw [hPres2 uSP (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
      h10P uSP (by decide) (by decide) (by decide) (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7, RegFile.write_same]
  obtain ⟨r12, hr12⟩ : ∃ z : RegFile, z = r11.write qLV (r5 mMV) := ⟨_, rfl⟩
  have s1033 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨r11, Q + 1033, false⟩ ⟨r12, Q + 1034, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r11, Q + 1033, false⟩ : State)) rfl f1033
    simpa [hr12, h11V] using h
  have hr12P : r12 uSP = r5 mMP := by
    rw [hr12, RegFile.write_other _ _ (by decide)]; exact h11P
  obtain ⟨r13, hr13⟩ : ∃ z : RegFile, z = r12.write qLP (r5 mMP) := ⟨_, rfl⟩
  have s1034 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨r12, Q + 1034, false⟩ ⟨r13, Q + 1035, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨r12, Q + 1034, false⟩ : State)) rfl f1034
    simpa [hr13, hr12P] using h
  -- ## Q+1035 .. Q+1043: the merge
  have h13LV : r13 qLV = r5 mMV := by
    rw [hr13, RegFile.write_other _ _ (by decide), hr12, RegFile.write_same]
  have h13LP : r13 qLP = r5 mMP := by rw [hr13, RegFile.write_same]
  have h13MV : r13 mMV = r11 mMV := by
    rw [hr13, RegFile.write_other _ _ (by decide), hr12,
      RegFile.write_other _ _ (by decide)]
  have h13MP : r13 mMP = r11 mMP := by
    rw [hr13, RegFile.write_other _ _ (by decide), hr12,
      RegFile.write_other _ _ (by decide)]
  obtain ⟨r14, sMerge, hValM, hPresM⟩ :=
    E1InteriorMerge.mergeBlock_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hMergeH r13
      (r5 mMV) (r5 mMP) (r11 mMV) (r11 mMP) h13LV h13LP h13MV h13MP
  rw [hVal1, hVal2] at sMerge hValM
  have harithEnd : Q + 1035 + 9 = Q + 1044 := by omega
  rw [harithEnd] at sMerge
  refine ⟨r14, ?_, ?_, ?_⟩
  · have h := ((((((((((((s0.trans s1).trans s2).trans sSet1).trans
      sSpan1).trans s516).trans s517).trans s518).trans s519).trans
      sSet2).trans sSpan2).trans s1033).trans s1034).trans sMerge
    simpa [twoLegCats, legSetupCats, List.append_assoc] using h
  · exact hValM
  · intro r hr
    obtain ⟨hTS, hM, hSh, hTA, hTSt, hTN, hTO, hUT, hUZ, hUSV, hUSP⟩ := hr
    rw [hPresM r hM, hr13, RegFile.write_other _ _ hSh.2, hr12,
      RegFile.write_other _ _ hSh.1, hPres2 r hTS,
      h10P r hTA hTSt hTN hTO, hr9, RegFile.write_other _ _ hUT, hr8,
      RegFile.write_other _ _ hUT, hr7, RegFile.write_other _ _ hUSP, hr6,
      RegFile.write_other _ _ hUSV, hPres1 r hTS,
      h4P r hTA hTSt hTN hTO, hr3, RegFile.write_other _ _ hUT, hr2,
      RegFile.write_other _ _ hUT, hr1, RegFile.write_other _ _ hUZ]

/-! ## `#6` AND `#7` INSTANTIATED

Both are `twoLegBlock` at a geometry pair and a source pair, exactly as
`#4`/`#5` are `twoSpanBlock` at a geometry pair.  The value links below
are stated at the parameters `twoLegBlock_runsTo` actually PRODUCES --
`macroStart * kA1`, `(macroStart + 1) * kA2` and so on -- rather than at
their reduced forms, so a caller composes them by `rw` and not by an
arithmetic detour.

`#7`'s global leg takes `kA2 = kO2 = 0`, so its slot base and block
offset arrive as `(macroStart + 1) * 0`.  That REDUCES to `0`, because
`Nat.mul` recurses on its second argument -- the mirror image of the
`0 + value` trap `E1_LIVE_STATE.md` §4 records, and for once it falls the
convenient way. -/

/-- **`#6` INSTANTIATED.** The two-leg combiner's value, at the LOCAL
geometries on both legs and at the route's own parameters, IS the value of
`canonicalRelativeRmmMachineAdjacentMacroCandidateComputation`.

NO VALIDITY, CAP OR STORE HYPOTHESIS, inherited from `#4`'s link.

The left leg's count is `macroSize - localStart`, which is the route's own
`leftCount`: `#6` recomputes it internally rather than taking it as an
argument (`InteriorDirectory.lean:2404`), so the machine must recompute it
too -- which is what the combiner's three-instruction prologue does. -/
theorem twoLegValue_adjacentMacro_eq_routeValue
    (shape : Cartesian.CartesianShape)
    (macroStart localStart rightCount : Nat) :
    bpCandidateMerge?
        (twoSpanValue shape (E1InteriorTwoSpan.localLevelGeom shape)
          (E1InteriorSpanBlock.localSpanGeom shape)
          (macroStart * ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize))
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          localStart
          ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
          (macroStart * (RelativeRmm.canonicalLayout shape).macroSize))
        (twoSpanValue shape (E1InteriorTwoSpan.localLevelGeom shape)
          (E1InteriorSpanBlock.localSpanGeom shape)
          ((macroStart + 1) * ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize))
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          0 rightCount
          ((macroStart + 1) * (RelativeRmm.canonicalLayout shape).macroSize)) =
      ((canonicalRelativeRmmMachineAdjacentMacroCandidateComputation shape
            macroStart localStart rightCount).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  rw [E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue,
    E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue]
  unfold canonicalRelativeRmmMachineAdjacentMacroCandidateComputation
  simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]
  rfl

/-- **`#7` INSTANTIATED.** The left leg is `#4`'s local geometry pair; the
second leg is `#5`'s global pair at slot base and block offset
`(macroStart + 1) * 0`. -/
theorem twoLegValue_leftMiddleMacro_eq_routeValue
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount : Nat) :
    bpCandidateMerge?
        (twoSpanValue shape (E1InteriorTwoSpan.localLevelGeom shape)
          (E1InteriorSpanBlock.localSpanGeom shape)
          (macroStart * ((RelativeRmm.canonicalLayout shape).levelCount *
            (RelativeRmm.canonicalLayout shape).macroSize))
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          localStart
          ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
          (macroStart * (RelativeRmm.canonicalLayout shape).macroSize))
        (twoSpanValue shape (E1InteriorTwoSpan.globalLevelGeom shape)
          (E1InteriorSpanBlock.globalSpanGeom shape)
          ((macroStart + 1) * 0)
          (RelativeRmm.canonicalLayout shape).macroSampleCount
          (bpSparseLevelDomain
            (RelativeRmm.canonicalLayout shape).macroSampleCount)
          (macroStart + 1) middleMacroCount ((macroStart + 1) * 0)) =
      ((canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation shape
            macroStart localStart middleMacroCount).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  -- `(macroStart + 1) * 0` REDUCES to `0`, but `rw` matches syntactically,
  -- so the reduction has to be performed rather than relied on.
  simp only [Nat.mul_zero]
  rw [E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue,
    E1InteriorTwoSpan.twoSpanValue_global_eq_routeValue]
  unfold canonicalRelativeRmmMachineLeftMiddleMacroCandidateComputation
  simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]
  rfl

/-! ## The second leg's source premises, WITNESSED at both instantiations

`twoLegBlock_runsTo`'s `hS2`/`hN2` are OWED premises: each says the
second setup's source register carries a named value whenever the six
combiner-bank readings hold.  Rule 1 asks for a witness AT THE INTENDED
INSTANTIATION, and both witnesses are projections -- `#6` reads its start
from `uZero` and its count from `uRight`, `#7` reads its start from `uT`
(which holds `macroStart + 1` by then) and its count from `uMid`.

These are stated as theorems rather than left to the call site so that the
premises are demonstrably NOT vacuous: a `RegFile` satisfying all six
readings exists, since the six constrain six DISTINCT registers. -/

/-- `#6`'s second-leg sources: `(uZero, uRight)`. -/
theorem adjacentMacro_src_witnesses
    (macroStart localStart mid rightCount : Nat) :
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = rightCount → r uZero = 0 →
      r uT = macroStart + 1 → r uZero = 0) ∧
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = rightCount → r uZero = 0 →
      r uT = macroStart + 1 → r uRight = rightCount) :=
  ⟨fun _ _ _ _ _ hz _ => hz, fun _ _ _ _ hr _ _ => hr⟩

/-- `#7`'s second-leg sources: `(uT, uMid)`.  `uT` holds `macroStart + 1`
by the time the second setup runs, which is what the block's two-instruction
bump establishes and what makes the global leg's `macroStart` argument
correct. -/
theorem leftMiddleMacro_src_witnesses
    (macroStart localStart middleMacroCount right : Nat) :
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = middleMacroCount → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r uT = macroStart + 1) ∧
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = middleMacroCount → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r uMid = middleMacroCount) :=
  ⟨fun _ _ _ _ _ _ ht => ht, fun _ _ _ hm _ _ _ => hm⟩

/-! ## THE THREE-LEG COMBINER: `#8`

`#8` is NOT a third primitive.  `bpCandidateMerge3? left middle right` is
DEFINITIONALLY `bpCandidateMerge? (bpCandidateMerge? left middle) right`
(`merge3_eq_two_merges`, `E1InteriorMerge.lean:593`), and `#8`'s first two
legs are exactly `#7`'s.  So the block is `twoLegBlock` at `#7`'s
parameters, followed by a third local leg and one more two-way merge --
1574 instructions, of which 1044 are the two-leg combiner unchanged.

**THE THIRD NESTING LEVEL NEEDS A THIRD STASH PAIR**, `vSV`/`vSP` at
`144`/`145`.  `uSV`/`uSP` will NOT do: `twoLegBlock` writes them itself,
exactly as `twoSpanBlock` writes `qLV`/`qLP`.  `twoLegUntouched_of_ge`
(write set below `144`) is what makes the new pair survive the whole
two-leg sub-block without re-deciding eleven conjuncts, and it is why that
lemma exists.

`rightMacroStart` is recomputed from `uMacro` and `uMid` in four
instructions rather than read out of `uT` -- `twoLegBlock` does leave
`macroStart + 1` there, but its `runsTo` states what the block LEAVES
ALONE and says nothing about the final value of a register it writes.
Depending on that value would mean strengthening the two-leg contract for
a saving of three instructions.  `uZero` is re-seeded for the same reason. -/

/-- Scratch: the OUTERMOST stash of the first TWO legs' merged candidate.

NOT `uSV`: `twoLegBlock` writes that pair, so a candidate stashed there
would be destroyed by the two-leg sub-block, exactly as `twoSpanBlock`
destroys `qLV`/`qLP`.  Third nesting level, third pair. -/
abbrev vSV : Nat := 144

/-- Scratch: the outermost stash of the merged candidate's position. -/
abbrev vSP : Nat := 145

/-- THE THREE-LEG COMBINER (1574 instructions, exit `Q + 1574`). -/
def crossLegBlock (L : SummaryLayout) (GL1 GS1 GL2 GS2 GL3 GS3 : TableGeom)
    (M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat) : List Instr :=
  twoLegBlock L GL1 GS1 GL2 GS2 M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q ++
    ([ Instr.move vSV mMV            -- Q+1044  OUTERMOST stash
      , Instr.move vSP mMP ] ++      -- Q+1045
      ([ Instr.const uZero 0         -- Q+1046  re-seed the zero source
        , Instr.const uT 1           -- Q+1047
        , Instr.add uT uMacro uT     -- Q+1048  macroStart + 1
        , Instr.add uT uT uMid ] ++  -- Q+1049  + middleMacroCount
        (legSetup kA3 kO3 uT uZero uRight ++  -- Q+1050 .. Q+1053
          (twoSpanBlock L GL3 GS3 M3 D3 blockSize blocksPerSuper (Q + 1054) ++
            ([ Instr.move qLV vSV    -- Q+1563  restore, AFTER the third leg
              , Instr.move qLP vSP ] ++ -- Q+1564
              mergeBlock (Q + 1565))))))

@[simp] theorem crossLegBlock_length (L : SummaryLayout)
    (GL1 GS1 GL2 GS2 GL3 GS3 : TableGeom)
    (M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2
      macroSize blockSize blocksPerSuper Q : Nat) :
    (crossLegBlock L GL1 GS1 GL2 GS2 GL3 GS3 M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2
      kA3 kO3 srcStart2 srcN2 macroSize blockSize blocksPerSuper Q).length
      = 1574 := by
  simp [crossLegBlock]

/-- The three-leg combiner's charge log. -/
def crossLegCats (catsA catsB catsC : List Category)
    (valA valB valC : Option (Nat × Nat)) : List Category :=
  twoLegCats catsA catsB valA valB ++
    ([Category.registerWrite, Category.registerWrite] ++
      ([Category.registerWrite, Category.registerWrite, Category.arithmetic,
          Category.arithmetic] ++
        (legSetupCats ++
          (catsC ++
            ([Category.registerWrite, Category.registerWrite] ++
              mergeCats (bpCandidateMerge? valA valB) valC)))))

/-- What the three-leg combiner LEAVES ALONE. -/
abbrev CrossLegUntouched (r : Nat) : Prop :=
  TwoLegUntouched r ∧ r ≠ vSV ∧ r ≠ vSP

/-- THE FOUR CROSS-BLOCK-ARM OPERANDS SURVIVE THE WHOLE THREE-LEG BLOCK. -/
theorem crossLegUntouched_at_crossBlockArm_operands :
    CrossLegUntouched 70 ∧ CrossLegUntouched 71 ∧ CrossLegUntouched 75 ∧
      CrossLegUntouched 76 :=
  ⟨⟨twoLegUntouched_at_crossBlockArm_operands.1, by decide, by decide⟩,
    ⟨twoLegUntouched_at_crossBlockArm_operands.2.1, by decide, by decide⟩,
    ⟨twoLegUntouched_at_crossBlockArm_operands.2.2.1, by decide, by decide⟩,
    ⟨twoLegUntouched_at_crossBlockArm_operands.2.2.2, by decide, by decide⟩⟩

/-- **THE WHOLE WRITE SET LIES BELOW `146`**, so `#9` can carry a dispatch
bank across a three-leg arm. -/
theorem crossLegUntouched_of_ge {r : Nat} (h : 146 ≤ r) : CrossLegUntouched r :=
  ⟨twoLegUntouched_of_ge (by omega), show r ≠ 144 by omega,
    show r ≠ 145 by omega⟩

/--
EXACT SIMULATION OF THE THREE-LEG COMBINER.

Exit `Q + 1574`.  The receipt is the THREE sub-legs' receipts
concatenated; the value is the route's own
`bpCandidateMerge? (bpCandidateMerge? v1 v2) v3`, which
`merge3_eq_two_merges` identifies with `bpCandidateMerge3?`.

NO STORE HYPOTHESIS AND NO VALIDITY HYPOTHESIS.
-/
theorem crossLegBlock_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {GL1 GS1 GL2 GS2 GL3 GS3 : TableGeom}
    {M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2 macroSize
      Q : Nat}
    {macroStart localStart mid right start2 n2 : Nat} {regs : RegFile}
    (hHost : HostedAt program Q
      (crossLegBlock (canonicalSummaryLayout shape) GL1 GS1 GL2 GS2 GL3 GS3
        M1 D1 M2 D2 M3 D3 kA1 kO1 kA2 kO2 kA3 kO3 srcStart2 srcN2 macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper Q))
    (hMacro : regs uMacro = macroStart) (hLocal : regs uLocal = localStart)
    (hMid : regs uMid = mid) (hRight : regs uRight = right)
    (hbS2 : 136 ≤ srcStart2) (hbN2 : 136 ≤ srcN2)
    (hS2 : ∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r srcStart2 = start2)
    (hN2 : ∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = mid → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r srcN2 = n2)
    (hL1Pos : 0 < GL1.chunkCount) (hL1Cap : GL1.chunkCount ≤ 8)
    (hS1Pos : 0 < GS1.chunkCount) (hS1Cap : GS1.chunkCount ≤ 8)
    (hL2Pos : 0 < GL2.chunkCount) (hL2Cap : GL2.chunkCount ≤ 8)
    (hS2Pos : 0 < GS2.chunkCount) (hS2Cap : GS2.chunkCount ≤ 8)
    (hL3Pos : 0 < GL3.chunkCount) (hL3Cap : GL3.chunkCount ≤ 8)
    (hS3Pos : 0 < GS3.chunkCount) (hS3Cap : GS3.chunkCount ≤ 8) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 1574, false⟩
          (twoSpanEvents shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1) ++
            twoSpanEvents shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2) ++
            twoSpanEvents shape GL3 GS3
              ((macroStart + 1 + mid) * kA3) M3 D3 0 right
              ((macroStart + 1 + mid) * kO3))
          (crossLegCats
            (twoSpanCats shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1))
            (twoSpanCats shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2))
            (twoSpanCats shape GL3 GS3 ((macroStart + 1 + mid) * kA3) M3 D3
              0 right ((macroStart + 1 + mid) * kO3))
            (twoSpanValue shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
              (macroSize - localStart) (macroStart * kO1))
            (twoSpanValue shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
              start2 n2 ((macroStart + 1) * kO2))
            (twoSpanValue shape GL3 GS3 ((macroStart + 1 + mid) * kA3) M3 D3
              0 right ((macroStart + 1 + mid) * kO3))) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          bpCandidateMerge?
            (bpCandidateMerge?
              (twoSpanValue shape GL1 GS1 (macroStart * kA1) M1 D1 localStart
                (macroSize - localStart) (macroStart * kO1))
              (twoSpanValue shape GL2 GS2 ((macroStart + 1) * kA2) M2 D2
                start2 n2 ((macroStart + 1) * kO2)))
            (twoSpanValue shape GL3 GS3 ((macroStart + 1 + mid) * kA3) M3 D3
              0 right ((macroStart + 1 + mid) * kO3)) ∧
        (∀ r, CrossLegUntouched r → regs' r = regs r) := by
  -- ## hosting
  have hTwoH : HostedAt program Q
      (twoLegBlock (canonicalSummaryLayout shape) GL1 GS1 GL2 GS2
        M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2 macroSize
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper Q) :=
    hHost.append_left
  have hT1 := hHost.append_right
    (code₁ := twoLegBlock (canonicalSummaryLayout shape) GL1 GS1 GL2 GS2
      M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2 macroSize
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper Q)
  rw [show Q + (twoLegBlock (canonicalSummaryLayout shape) GL1 GS1 GL2 GS2
      M1 D1 M2 D2 kA1 kO1 kA2 kO2 srcStart2 srcN2 macroSize
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper Q).length = Q + 1044
    from by simp only [twoLegBlock_length]] at hT1
  have hStash3 : HostedAt program (Q + 1044)
      [Instr.move vSV mMV, Instr.move vSP mMP] := hT1.append_left
  have hT2 := hT1.append_right
    (code₁ := [Instr.move vSV mMV, Instr.move vSP mMP])
  rw [show Q + 1044 + [Instr.move vSV mMV, Instr.move vSP mMP].length
    = Q + 1046 from rfl] at hT2
  have hPro3 : HostedAt program (Q + 1046)
      [Instr.const uZero 0, Instr.const uT 1, Instr.add uT uMacro uT,
        Instr.add uT uT uMid] := hT2.append_left
  have hT3 := hT2.append_right
    (code₁ := [Instr.const uZero 0, Instr.const uT 1,
      Instr.add uT uMacro uT, Instr.add uT uT uMid])
  rw [show Q + 1046 + [Instr.const uZero 0, Instr.const uT 1,
      Instr.add uT uMacro uT, Instr.add uT uT uMid].length = Q + 1050
    from rfl] at hT3
  have hSet3 : HostedAt program (Q + 1050)
      (legSetup kA3 kO3 uT uZero uRight) := hT3.append_left
  have hT4 := hT3.append_right (code₁ := legSetup kA3 kO3 uT uZero uRight)
  rw [show Q + 1050 + (legSetup kA3 kO3 uT uZero uRight).length = Q + 1054
    from by simp only [legSetup_length]] at hT4
  have hSpan3 : HostedAt program (Q + 1054)
      (twoSpanBlock (canonicalSummaryLayout shape) GL3 GS3 M3 D3
        (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1054)) :=
    hT4.append_left
  have hT5 := hT4.append_right
    (code₁ := twoSpanBlock (canonicalSummaryLayout shape) GL3 GS3 M3 D3
      (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1054))
  rw [show Q + 1054 + (twoSpanBlock (canonicalSummaryLayout shape) GL3 GS3
      M3 D3 (RelativeRmm.canonicalLayout shape).blockSize
      (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 1054)).length
      = Q + 1563 from by
    simp only [E1InteriorTwoSpan.twoSpanBlock_length]] at hT5
  have hRest3 : HostedAt program (Q + 1563)
      [Instr.move qLV vSV, Instr.move qLP vSP] := hT5.append_left
  have hMergeH : HostedAt program (Q + 1565) (mergeBlock (Q + 1565)) := by
    have h := hT5.append_right
      (code₁ := [Instr.move qLV vSV, Instr.move qLP vSP])
    rw [show Q + 1563 + [Instr.move qLV vSV, Instr.move qLP vSP].length
      = Q + 1565 from rfl] at h
    exact h
  -- ## Q .. Q+1043: the two-leg sub-block, unchanged
  obtain ⟨w1, sTwo, hVal12, hPres12⟩ :=
    twoLegBlock_runsTo shape hTwoH hMacro hLocal hMid hRight hbS2 hbN2 hS2 hN2
      hL1Pos hL1Cap hS1Pos hS1Cap hL2Pos hL2Cap hS2Pos hS2Cap
  -- ## Q+1044, Q+1045: the OUTERMOST stash
  have f1044 : program[Q + 1044]? = some (Instr.move vSV mMV) := hStash3.head
  have f1045 : program[Q + 1045]? = some (Instr.move vSP mMP) := by
    have h := hStash3.tail.head
    have harith : Q + 1044 + 1 = Q + 1045 := by omega
    rwa [harith] at h
  obtain ⟨w2, hw2⟩ : ∃ z : RegFile, z = w1.write vSV (w1 mMV) := ⟨_, rfl⟩
  have s1044 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w1, Q + 1044, false⟩ ⟨w2, Q + 1045, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w1, Q + 1044, false⟩ : State)) rfl f1044
    simpa [hw2] using h
  have hw2P : w2 mMP = w1 mMP := by
    rw [hw2, RegFile.write_other _ _ (by decide)]
  obtain ⟨w3, hw3⟩ : ∃ z : RegFile, z = w2.write vSP (w1 mMP) := ⟨_, rfl⟩
  have s1045 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w2, Q + 1045, false⟩ ⟨w3, Q + 1046, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w2, Q + 1045, false⟩ : State)) rfl f1045
    simpa [hw3, hw2P] using h
  -- ## Q+1046 .. Q+1049: re-seed `uZero`, then `rightMacroStart`
  have f1046 : program[Q + 1046]? = some (Instr.const uZero 0) := hPro3.head
  have f1047 : program[Q + 1047]? = some (Instr.const uT 1) := by
    have h := hPro3.tail.head
    have harith : Q + 1046 + 1 = Q + 1047 := by omega
    rwa [harith] at h
  have f1048 : program[Q + 1048]? = some (Instr.add uT uMacro uT) := by
    have h := hPro3.tail.tail.head
    have harith : Q + 1046 + 1 + 1 = Q + 1048 := by omega
    rwa [harith] at h
  have f1049 : program[Q + 1049]? = some (Instr.add uT uT uMid) := by
    have h := hPro3.tail.tail.tail.head
    have harith : Q + 1046 + 1 + 1 + 1 = Q + 1049 := by omega
    rwa [harith] at h
  obtain ⟨w4, hw4⟩ : ∃ z : RegFile, z = w3.write uZero 0 := ⟨_, rfl⟩
  have s1046 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w3, Q + 1046, false⟩ ⟨w4, Q + 1047, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w3, Q + 1046, false⟩ : State)) rfl f1046
    simpa [hw4] using h
  obtain ⟨w5, hw5⟩ : ∃ z : RegFile, z = w4.write uT 1 := ⟨_, rfl⟩
  have s1047 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w4, Q + 1047, false⟩ ⟨w5, Q + 1048, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w4, Q + 1047, false⟩ : State)) rfl f1047
    simpa [hw5] using h
  -- the caller's bank survives the two-leg sub-block and the stash
  have hBank3 : ∀ r : Nat, TwoLegUntouched r → r ≠ vSV → r ≠ vSP →
      r ≠ uZero → r ≠ uT → w5 r = regs r := by
    intro r hr hV hP hZ hT
    rw [hw5, RegFile.write_other _ _ hT, hw4, RegFile.write_other _ _ hZ,
      hw3, RegFile.write_other _ _ hP, hw2, RegFile.write_other _ _ hV,
      hPres12 r hr]
  have hInBank : ∀ r : Nat, 136 ≤ r → r ≠ uT → r ≠ uZero → r ≠ uSV →
      r ≠ uSP → r ≠ vSV → r ≠ vSP → w5 r = regs r := by
    intro r hge hT hZ hV hP hV3 hP3
    exact hBank3 r (twoLegUntouched_of_bank hge hT hZ hV hP) hV3 hP3 hZ hT
  have h5M : w5 uMacro = macroStart := by
    rw [hInBank uMacro (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)]
    exact hMacro
  have h5T : w5 uT = 1 := by rw [hw5, RegFile.write_same]
  obtain ⟨w6, hw6⟩ : ∃ z : RegFile, z = w5.write uT (macroStart + 1) :=
    ⟨_, rfl⟩
  have s1048 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w5, Q + 1048, false⟩ ⟨w6, Q + 1049, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w5, Q + 1048, false⟩ : State)) rfl f1048
    simpa [hw6, h5M, h5T] using h
  have h6T : w6 uT = macroStart + 1 := by rw [hw6, RegFile.write_same]
  have h6Mid : w6 uMid = mid := by
    rw [hw6, RegFile.write_other _ _ (by decide),
      hInBank uMid (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact hMid
  obtain ⟨w7, hw7⟩ : ∃ z : RegFile, z = w6.write uT (macroStart + 1 + mid) :=
    ⟨_, rfl⟩
  have s1049 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w6, Q + 1049, false⟩ ⟨w7, Q + 1050, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w6, Q + 1049, false⟩ : State)) rfl f1049
    simpa [hw7, h6T, h6Mid] using h
  have h7T : w7 uT = macroStart + 1 + mid := by rw [hw7, RegFile.write_same]
  have h7Z : w7 uZero = 0 := by
    rw [hw7, RegFile.write_other _ _ (by decide), hw6,
      RegFile.write_other _ _ (by decide), hw5,
      RegFile.write_other _ _ (by decide), hw4, RegFile.write_same]
  have h7R : w7 uRight = right := by
    rw [hw7, RegFile.write_other _ _ (by decide), hw6,
      RegFile.write_other _ _ (by decide),
      hInBank uRight (by decide) (by decide) (by decide) (by decide)
        (by decide) (by decide) (by decide)]
    exact hRight
  -- ## Q+1050 .. Q+1053: the third leg's setup
  obtain ⟨w8, sSet3, h8A, h8S, h8N, h8O, h8P⟩ :=
    legSetup_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (regs := w7) hSet3 (by decide) (by decide) (by decide)
  rw [h7T] at h8A h8O
  rw [h7Z] at h8S
  rw [h7R] at h8N
  -- ## Q+1054 .. Q+1562: the third sub-leg
  obtain ⟨w9, sSpan3, hVal3, hPres3⟩ :=
    E1InteriorTwoSpan.twoSpanBlock_runsTo shape hSpan3 h8A h8S h8N h8O
      hL3Pos hL3Cap hS3Pos hS3Cap
  -- ## Q+1563, Q+1564: the outermost RESTORE
  have f1563 : program[Q + 1563]? = some (Instr.move qLV vSV) := hRest3.head
  have f1564 : program[Q + 1564]? = some (Instr.move qLP vSP) := by
    have h := hRest3.tail.head
    have harith : Q + 1563 + 1 = Q + 1564 := by omega
    rwa [harith] at h
  have h9V : w9 vSV = w1 mMV := by
    rw [hPres3 vSV (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
      h8P vSV (by decide) (by decide) (by decide) (by decide), hw7,
      RegFile.write_other _ _ (by decide), hw6,
      RegFile.write_other _ _ (by decide), hw5,
      RegFile.write_other _ _ (by decide), hw4,
      RegFile.write_other _ _ (by decide), hw3,
      RegFile.write_other _ _ (by decide), hw2, RegFile.write_same]
  have h9P : w9 vSP = w1 mMP := by
    rw [hPres3 vSP (E1InteriorTwoSpan.twoSpanUntouched_of_ge (by decide)),
      h8P vSP (by decide) (by decide) (by decide) (by decide), hw7,
      RegFile.write_other _ _ (by decide), hw6,
      RegFile.write_other _ _ (by decide), hw5,
      RegFile.write_other _ _ (by decide), hw4,
      RegFile.write_other _ _ (by decide), hw3, RegFile.write_same]
  obtain ⟨w10, hw10⟩ : ∃ z : RegFile, z = w9.write qLV (w1 mMV) := ⟨_, rfl⟩
  have s1563 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w9, Q + 1563, false⟩ ⟨w10, Q + 1564, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w9, Q + 1563, false⟩ : State)) rfl f1563
    simpa [hw10, h9V] using h
  have hw10P : w10 vSP = w1 mMP := by
    rw [hw10, RegFile.write_other _ _ (by decide)]; exact h9P
  obtain ⟨w11, hw11⟩ : ∃ z : RegFile, z = w10.write qLP (w1 mMP) := ⟨_, rfl⟩
  have s1564 : RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      program ⟨w10, Q + 1564, false⟩ ⟨w11, Q + 1565, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.move
      (store := concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (s := (⟨w10, Q + 1564, false⟩ : State)) rfl f1564
    simpa [hw11, hw10P] using h
  -- ## Q+1565 .. Q+1573: the outermost merge
  have h11LV : w11 qLV = w1 mMV := by
    rw [hw11, RegFile.write_other _ _ (by decide), hw10, RegFile.write_same]
  have h11LP : w11 qLP = w1 mMP := by rw [hw11, RegFile.write_same]
  have h11MV : w11 mMV = w9 mMV := by
    rw [hw11, RegFile.write_other _ _ (by decide), hw10,
      RegFile.write_other _ _ (by decide)]
  have h11MP : w11 mMP = w9 mMP := by
    rw [hw11, RegFile.write_other _ _ (by decide), hw10,
      RegFile.write_other _ _ (by decide)]
  obtain ⟨w12, sMerge, hValM, hPresM⟩ :=
    E1InteriorMerge.mergeBlock_runsTo
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) hMergeH w11
      (w1 mMV) (w1 mMP) (w9 mMV) (w9 mMP) h11LV h11LP h11MV h11MP
  rw [hVal12, hVal3] at sMerge hValM
  have harithEnd : Q + 1565 + 9 = Q + 1574 := by omega
  rw [harithEnd] at sMerge
  refine ⟨w12, ?_, ?_, ?_⟩
  · have h := ((((((((sTwo.trans s1044).trans s1045).trans s1046).trans
      s1047).trans s1048).trans s1049).trans sSet3).trans sSpan3).trans
      ((s1563.trans s1564).trans sMerge)
    simpa [crossLegCats, twoLegCats, legSetupCats, List.append_assoc] using h
  · exact hValM
  · intro r hr
    obtain ⟨hTL, hV3, hP3⟩ := hr
    obtain ⟨hTS, hM, hSh, hTA, hTSt, hTN, hTO, hUT, hUZ, hUSV, hUSP⟩ := hTL
    rw [hPresM r hM, hw11, RegFile.write_other _ _ hSh.2, hw10,
      RegFile.write_other _ _ hSh.1, hPres3 r hTS,
      h8P r hTA hTSt hTN hTO, hw7, RegFile.write_other _ _ hUT, hw6,
      RegFile.write_other _ _ hUT, hw5, RegFile.write_other _ _ hUT, hw4,
      RegFile.write_other _ _ hUZ, hw3, RegFile.write_other _ _ hP3, hw2,
      RegFile.write_other _ _ hV3]
    exact hPres12 r ⟨hTS, hM, hSh, hTA, hTSt, hTN, hTO, hUT, hUZ, hUSV, hUSP⟩

/-- **`#8` INSTANTIATED.** The three-leg combiner's value, at LOCAL /
GLOBAL / LOCAL geometries and the route's own parameters, IS the value of
`canonicalRelativeRmmMachineCrossMacroCandidateComputation`.

The route's terminal combination is `bpCandidateMerge3? left middle
right`, and the machine's is two two-way merges; the two agree
DEFINITIONALLY (`merge3_eq_two_merges`), which is why no reassociation
step appears below.

NO VALIDITY, CAP OR STORE HYPOTHESIS. -/
theorem crossLegValue_crossMacro_eq_routeValue
    (shape : Cartesian.CartesianShape)
    (macroStart localStart middleMacroCount rightCount : Nat) :
    bpCandidateMerge?
        (bpCandidateMerge?
          (twoSpanValue shape (E1InteriorTwoSpan.localLevelGeom shape)
            (E1InteriorSpanBlock.localSpanGeom shape)
            (macroStart * ((RelativeRmm.canonicalLayout shape).levelCount *
              (RelativeRmm.canonicalLayout shape).macroSize))
            (RelativeRmm.canonicalLayout shape).macroSize
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
            localStart
            ((RelativeRmm.canonicalLayout shape).macroSize - localStart)
            (macroStart * (RelativeRmm.canonicalLayout shape).macroSize))
          (twoSpanValue shape (E1InteriorTwoSpan.globalLevelGeom shape)
            (E1InteriorSpanBlock.globalSpanGeom shape)
            ((macroStart + 1) * 0)
            (RelativeRmm.canonicalLayout shape).macroSampleCount
            (bpSparseLevelDomain
              (RelativeRmm.canonicalLayout shape).macroSampleCount)
            (macroStart + 1) middleMacroCount ((macroStart + 1) * 0)))
        (twoSpanValue shape (E1InteriorTwoSpan.localLevelGeom shape)
          (E1InteriorSpanBlock.localSpanGeom shape)
          ((macroStart + 1 + middleMacroCount) *
            ((RelativeRmm.canonicalLayout shape).levelCount *
              (RelativeRmm.canonicalLayout shape).macroSize))
          (RelativeRmm.canonicalLayout shape).macroSize
          (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize)
          0 rightCount
          ((macroStart + 1 + middleMacroCount) *
            (RelativeRmm.canonicalLayout shape).macroSize)) =
      ((canonicalRelativeRmmMachineCrossMacroCandidateComputation shape
            macroStart localStart middleMacroCount rightCount).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).value := by
  simp only [Nat.mul_zero]
  rw [E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue,
    E1InteriorTwoSpan.twoSpanValue_global_eq_routeValue,
    E1InteriorTwoSpan.twoSpanValue_local_eq_routeValue]
  unfold canonicalRelativeRmmMachineCrossMacroCandidateComputation
  simp only [FlatStoreComputation.bind, FlatStoreComputation.map,
    FlatStoreExecution.append]
  rfl

/-- `#8`'s second-leg sources are `#7`'s: `(uT, uMid)`.  Its THIRD leg's
sources are program-fixed (`uZero`, `uRight`) and appear directly in
`crossLegBlock`, so they need no witness -- only the second leg's are
parametric. -/
theorem crossMacro_src_witnesses
    (macroStart localStart middleMacroCount right : Nat) :
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = middleMacroCount → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r uT = macroStart + 1) ∧
    (∀ r : RegFile, r uMacro = macroStart → r uLocal = localStart →
      r uMid = middleMacroCount → r uRight = right → r uZero = 0 →
      r uT = macroStart + 1 → r uMid = middleMacroCount) :=
  ⟨fun _ _ _ _ _ _ ht => ht, fun _ _ _ hm _ _ _ => hm⟩

end E1InteriorCombine
end WordRAM
end RMQ
