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

**PROVED:** `legSetup_runsTo` (exact simulation of one leg's four-input
setup, with the bank premise that makes it sound).

**DEFINED BUT NOT YET SIMULATED:** `twoLegBlock`, its length, its charge
log `twoLegCats`, and `TwoLegUntouched` with its cross-block-arm
evaluation.  **`twoLegBlock_runsTo` DOES NOT EXIST**, so nothing here yet
entitles anyone to say `#6` or `#7` is closed.  The definition is
committed rather than dropped because it encodes a design CORRECTION that
cost a rebuild to find, described next.

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

/-- What the combiner LEAVES ALONE. -/
abbrev TwoLegUntouched (r : Nat) : Prop :=
  TwoSpanUntouched r ∧ MergeUntouched r ∧ ShuttleUntouched r ∧
    r ≠ uT ∧ r ≠ uZero ∧ r ≠ uSV ∧ r ≠ uSP

/-- THE FOUR CROSS-BLOCK-ARM OPERANDS SURVIVE THE WHOLE COMBINER. -/
theorem twoLegUntouched_at_crossBlockArm_operands :
    TwoLegUntouched 70 ∧ TwoLegUntouched 71 ∧ TwoLegUntouched 75 ∧
      TwoLegUntouched 76 :=
  ⟨⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.1,
      by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.2.1,
      by decide, by decide, by decide, by decide, by decide, by decide⟩,
    ⟨E1InteriorTwoSpan.twoSpanUntouched_at_crossBlockArm_operands.2.2.2,
      by decide, by decide, by decide, by decide, by decide, by decide⟩⟩

end E1InteriorCombine
end WordRAM
end RMQ
