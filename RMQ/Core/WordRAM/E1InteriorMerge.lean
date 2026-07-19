import RMQ.Core.WordRAM.E1InteriorSpanBlock

/-! # E1 amended machine: the interior's TWO-WAY CANDIDATE MERGE

`#4`, `#5`, `#6` and `#7` of the interior route ladder all end in
`bpCandidateMerge?` over two `Option (Nat × Nat)` sub-leg results
(`InteriorDirectory.lean:2351`, `:2376`, `:2400`, `:2413`).  **No block on
the machine side computed that**, and this module supplies it.

## Why `candMerge3` is not it, stated exactly

`E1CandMerge3.candMerge3` is the fringe's THREE-way combiner and its
`candMerge3_runsTo` hypotheses pin BOTH outer arms to occupied biased form
(`regs mLV = lv + 1`, `regs mRV = rv + 1`), matching
`bpCandidateMerge3?_some_left_right`, which takes `left right : Nat × Nat`
as BARE PAIRS.  That is the fringe's situation -- `bpFringeCandGlobal` is
total -- and it is NOT the interior's, where all sub-legs are genuinely
`Option`.

SUPERSEDES a claim recorded in `E1_LIVE_STATE.md` §2 that `candMerge3`'s
epilogue "writes the closed position where the combiners need the
candidate left in the bank".  That is WRONG and the correction matters,
because it misidentifies the reason: `candMerge3Close` is ADDITIVE, and
`candMerge3_runsTo` already exports `bestOfRegs (regs' mAV) (regs' mAP)`
holding the merged candidate alongside the `fRes` clause.  The real
obstacles are (a) the occupancy hypotheses above, and (b) the `fRes` (69)
write, which is the shared dispatch output register and must not be
touched by a combiner running mid-leg.  The headline conclusion -- that no
two-way `bpCandidateMerge?` block exists -- is unaffected.

`candMerge3Mid` (`E1CandMerge3.lean:157`) is the closest existing thing: a
proved occupied-left / optional-middle merge, i.e. two of the four option
combinations.  It is not reused because its left arm is unconditionally
occupied, which is exactly the case this block must not assume.

## Where the result lands, and why

In `mMV`/`mMP`, the same pair `spanBlock` and the 177-leg write, because
`crossBlockArmProgramAt_runsTo`'s `hInterior` (`E1CrossBlockArm.lean:1199`)
reads the interior's answer from `bestOfRegs (regsI mMV) (regsI mMP)`.
Every interior producer landing in one pair is what lets `#4`-`#9` compose
without shuffling.  The block therefore merges a STASHED left candidate
with whatever the most recent sub-leg left in `mMV`/`mMP`, in place.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorMerge

open E1Machine
open RMQ.SuccinctClose
open E1FringeFoldBlock (bestOfRegs)
open E1CandMerge3 (mMV mMP)

/-! ## Registers

The interior's second new bank.  `75..84` (merge), `89..99` (chunk fold),
`105..117` (summary + min-candidate) and `118..122` (span block) are
taken; this block opens at `123`.  `qLV` and `qLP` are INPUTS the caller
stashes before running the right-hand sub-leg; the rest are scratch. -/

/-- Input: the STASHED left candidate's biased value (`0` = `none`). -/
abbrev qLV : Nat := 123

/-- Input: the stashed left candidate's position. -/
abbrev qLP : Nat := 124

/-- Scratch: the comparison result. -/
abbrev qT : Nat := 125

/-- Constant `1`, making the two skip branches unconditional.  Set by the
block itself rather than inherited as an `hOne` hypothesis, following
`spanBlock`'s `pOne`: the fold's preservation certificate does not cover
`fOne`, so a combiner that runs after a fold cannot rely on it. -/
abbrev qOne : Nat := 126

/-! ## The block -/

/--
THE TWO-WAY CANDIDATE MERGE (9 instructions, exit `Q + 9` on ALL FOUR
arms).

Merges the stashed left candidate `bestOfRegs qLV qLP` with the right
candidate `bestOfRegs mMV mMP`, IN PLACE in `mMV`/`mMP`.

The two arms that keep the RIGHT candidate do nothing at all -- it is
already in the destination pair -- which is why `Q + 2` and `Q + 6` both
jump straight to the exit.

`Q + 5` is the whole arithmetic content.  Both operands are biased by the
same `+1`, so `natLt qT mMV qLV` computes `right.1 < left.1` DIRECTLY,
with no unbiasing, and that is exactly `bpCandidateBetter`'s test.  It is
STRICT, so a tie keeps the LEFT candidate -- see `mergeTie_discriminates`.
-/
def mergeBlock (Q : Nat) : List Instr :=
  [ Instr.const qOne 1        -- Q+0
  , Instr.brNZ qLV (Q + 3)    -- Q+1  left present? -> test the right
  , Instr.brNZ qOne (Q + 9)   -- Q+2  left none: the result IS the right arm
  , Instr.brNZ mMV (Q + 5)    -- Q+3  right present? -> compare
  , Instr.brNZ qOne (Q + 7)   -- Q+4  right none: the result is the left arm
  , Instr.natLt qT mMV qLV    -- Q+5  biased test IS `right.1 < left.1`
  , Instr.brNZ qT (Q + 9)     -- Q+6  right strictly better: leave it in place
  , Instr.move mMV qLV        -- Q+7  the result is the left arm
  , Instr.move mMP qLP ]      -- Q+8

@[simp] theorem mergeBlock_length (Q : Nat) : (mergeBlock Q).length = 9 := rfl

/-- The block performs no memory read: the route's combiner rides a
`FlatStoreComputation.map`, which contributes no read event. -/
theorem mergeBlock_readFree (Q : Nat) :
    ∀ instr ∈ mergeBlock Q, instr.category ≠ Category.memoryRead := by
  intro instr hinstr
  simp only [mergeBlock, List.mem_cons, List.not_mem_nil, or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [Instr.category]

/-- The block's charge log, as a FUNCTION of the route-side branch
conditions -- the two occupancies and the `bpCandidateBetter` comparison
-- never a numeral.  The four arms differ in LENGTH as well as content. -/
def mergeCats (left right : Option (Nat × Nat)) : List Category :=
  match left, right with
  | none, _ => [.registerWrite, .branch, .branch]
  | some _, none =>
      [.registerWrite, .branch, .branch, .branch, .registerWrite,
        .registerWrite]
  | some l, some r =>
      if r.1 < l.1 then
        [.registerWrite, .branch, .branch, .comparison, .branch]
      else
        [.registerWrite, .branch, .branch, .comparison, .branch,
          .registerWrite, .registerWrite]

/-! ## Preservation

Stated in NUMERALS: with the register abbrevs `omega` treats the names as
unanalysed atoms and fails.  The block writes exactly `mMV` (77), `mMP`
(78), `qT` (125) and `qOne` (126). -/

/-- What the merge block LEAVES ALONE.

Ask of this predicate what its consumer needs, not what the block happens
to avoid: `crossBlockArmProgramAt_runsTo`'s `hInterior` requires `fClose`
(70), `fRight` (71), `mLV` (75) and `mLP` (76) to survive, and
`mergeUntouched_at_crossBlockArm_operands` below PROVES all four do rather
than leaving it to inspection. -/
abbrev MergeUntouched (r : Nat) : Prop :=
  r ≠ 77 ∧ r ≠ 78 ∧ r ≠ 125 ∧ r ≠ 126

/-- THE FOUR CROSS-BLOCK-ARM OPERANDS SURVIVE THE MERGE BLOCK, evaluated
on numerals rather than eyeballed.  The write set is a numeral predicate,
so this DECIDES. -/
theorem mergeUntouched_at_crossBlockArm_operands :
    MergeUntouched 70 ∧ MergeUntouched 71 ∧ MergeUntouched 75 ∧
      MergeUntouched 76 := by
  decide

/-! ## Exact simulation -/

/--
EXACT SIMULATION OF THE TWO-WAY MERGE, ALL FOUR OPTION COMBINATIONS.

All four arms exit at `Q + 9`.  The block is READ-FREE, so the receipt is
`[]` on every arm -- stated as the literal, not as a length.

The value clause is stated against the ROUTE's own `bpCandidateMerge?`
rather than against the block's arithmetic, for the reason DD-20260719-050
records for the span block: a value clause phrased in the block's own
terms is satisfied by its own impostors.

NO STORE HYPOTHESIS.  The only premises are the hosting and the four
register readings.
-/
theorem mergeBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q (mergeBlock Q))
    (regs : RegFile) (lv lp rv rp : Nat)
    (hLV : regs qLV = lv) (hLP : regs qLP = lp)
    (hMV : regs mMV = rv) (hMP : regs mMP = rp) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 9, false⟩ []
        (mergeCats (bestOfRegs lv lp) (bestOfRegs rv rp)) ∧
      bestOfRegs (regs' mMV) (regs' mMP) =
        bpCandidateMerge? (bestOfRegs lv lp) (bestOfRegs rv rp) ∧
      (∀ r, MergeUntouched r → regs' r = regs r) := by
  -- fetch facts for the nine positions
  have hf : ∀ (k m : Nat) (instr : Instr), k < 9 →
      (mergeBlock Q)[k]? = some instr → Q + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.const qOne 1) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.brNZ qLV (Q + 3)) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.brNZ qOne (Q + 9)) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.brNZ mMV (Q + 5)) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[Q + 4]? = some (.brNZ qOne (Q + 7)) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[Q + 5]? = some (.natLt qT mMV qLV) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[Q + 6]? = some (.brNZ qT (Q + 9)) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[Q + 7]? = some (.move mMV qLV) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have h8 : program[Q + 8]? = some (.move mMP qLP) :=
    hf 8 _ _ (by omega) rfl (by omega)
  -- the unit seed, common to all four arms
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write qOne 1 := ⟨_, rfl⟩
  have hseed : RunsTo store program ⟨regs, Q, false⟩
      ⟨r1, Q + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.const (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr1] using h
  have hr1One : r1 qOne = 1 := by simp [hr1, RegFile.write]
  have hr1LV : r1 qLV = lv := by
    simp [hr1, RegFile.write, qOne, qLV, hLV]
  have hr1LP : r1 qLP = lp := by
    simp [hr1, RegFile.write, qOne, qLP, hLP]
  have hr1MV : r1 mMV = rv := by
    simp [hr1, RegFile.write, qOne, mMV, hMV]
  have hr1MP : r1 mMP = rp := by
    simp [hr1, RegFile.write, qOne, mMP, hMP]
  cases lv with
  | zero =>
      -- ARM (i): the LEFT candidate is absent; the result is the right arm,
      -- already in the destination pair.
      have hbr1 : RunsTo store program ⟨r1, Q + 1, false⟩
          ⟨r1, Q + 2, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_not_taken (store := store)
          (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1 (by simpa using hr1LV)
        simpa using h
      have hbr2 : RunsTo store program ⟨r1, Q + 2, false⟩
          ⟨r1, Q + 9, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_taken (store := store)
          (s := (⟨r1, Q + 2, false⟩ : State)) rfl h2 (by simp [hr1One])
        simpa using h
      refine ⟨r1, ?_, ?_, ?_⟩
      · have hrun := (hseed.trans hbr1).trans hbr2
        simpa [mergeCats, bestOfRegs] using hrun
      · simp [hr1MV, hr1MP, bestOfRegs, bpCandidateMerge?]
      · intro r hr
        obtain ⟨_, _, _, hOne⟩ := hr
        simp [hr1, RegFile.write, hOne]
  | succ l =>
      -- the left candidate is present
      have hbr1 : RunsTo store program ⟨r1, Q + 1, false⟩
          ⟨r1, Q + 3, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_taken (store := store)
          (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1 (by simp [hr1LV])
        simpa using h
      have hleft := hseed.trans hbr1
      cases rv with
      | zero =>
          -- ARM (ii): the RIGHT candidate is absent; the result is the left arm.
          have hbr3 : RunsTo store program ⟨r1, Q + 3, false⟩
              ⟨r1, Q + 4, false⟩ [] [Category.branch] := by
            have h := RunsTo.brNZ_not_taken (store := store)
              (s := (⟨r1, Q + 3, false⟩ : State)) rfl h3 (by simpa using hr1MV)
            simpa using h
          have hbr4 : RunsTo store program ⟨r1, Q + 4, false⟩
              ⟨r1, Q + 7, false⟩ [] [Category.branch] := by
            have h := RunsTo.brNZ_taken (store := store)
              (s := (⟨r1, Q + 4, false⟩ : State)) rfl h4 (by simp [hr1One])
            simpa using h
          obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write mMV (l + 1) := ⟨_, rfl⟩
          have hmv : RunsTo store program ⟨r1, Q + 7, false⟩
              ⟨r2, Q + 8, false⟩ [] [Category.registerWrite] := by
            have h := RunsTo.move (store := store)
              (s := (⟨r1, Q + 7, false⟩ : State)) rfl h7
            simpa [hr2, hr1LV] using h
          obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write mMP lp := ⟨_, rfl⟩
          have hmp : RunsTo store program ⟨r2, Q + 8, false⟩
              ⟨r3, Q + 9, false⟩ [] [Category.registerWrite] := by
            have h := RunsTo.move (store := store)
              (s := (⟨r2, Q + 8, false⟩ : State)) rfl h8
            simpa [hr3, hr2, RegFile.write, mMV, qLP, hr1LP] using h
          refine ⟨r3, ?_, ?_, ?_⟩
          · have hrun := (((hleft.trans hbr3).trans hbr4).trans hmv).trans hmp
            simpa [mergeCats, bestOfRegs] using hrun
          · have hMV3 : r3 mMV = l + 1 := by
              simp [hr3, hr2, RegFile.write, mMV, mMP]
            have hMP3 : r3 mMP = lp := by simp [hr3, RegFile.write]
            simp [hMV3, hMP3, bestOfRegs, bpCandidateMerge?]
          · intro r hr
            obtain ⟨hMVr, hMPr, _, hOne⟩ := hr
            simp [hr3, hr2, hr1, RegFile.write, hMVr, hMPr, hOne]
      | succ r =>
          -- both candidates present: compare
          have hbr3 : RunsTo store program ⟨r1, Q + 3, false⟩
              ⟨r1, Q + 5, false⟩ [] [Category.branch] := by
            have h := RunsTo.brNZ_taken (store := store)
              (s := (⟨r1, Q + 3, false⟩ : State)) rfl h3 (by simp [hr1MV])
            simpa using h
          obtain ⟨r2, hr2⟩ : ∃ z : RegFile,
              z = r1.write qT (if r + 1 < l + 1 then 1 else 0) := ⟨_, rfl⟩
          have hlt : RunsTo store program ⟨r1, Q + 5, false⟩
              ⟨r2, Q + 6, false⟩ [] [Category.comparison] := by
            have h := RunsTo.natLt (store := store)
              (s := (⟨r1, Q + 5, false⟩ : State)) rfl h5
            simpa [hr2, hr1MV, hr1LV] using h
          have hr2LV : r2 qLV = l + 1 := by
            simp [hr2, RegFile.write, qT, qLV, hr1LV]
          have hr2LP : r2 qLP = lp := by
            simp [hr2, RegFile.write, qT, qLP, hr1LP]
          have hr2MV : r2 mMV = r + 1 := by
            simp [hr2, RegFile.write, qT, mMV, hr1MV]
          have hr2MP : r2 mMP = rp := by
            simp [hr2, RegFile.write, qT, mMP, hr1MP]
          have hcmp := (hleft.trans hbr3).trans hlt
          by_cases hbetter : r < l
          · -- ARM (iii): the RIGHT candidate is strictly better; leave it.
            have hcond : r2 qT = 1 := by
              rw [hr2, RegFile.write_same]
              exact if_pos (by omega)
            have hbr6 : RunsTo store program ⟨r2, Q + 6, false⟩
                ⟨r2, Q + 9, false⟩ [] [Category.branch] := by
              have h := RunsTo.brNZ_taken (store := store)
                (s := (⟨r2, Q + 6, false⟩ : State)) rfl h6 (by simp [hcond])
              simpa using h
            refine ⟨r2, ?_, ?_, ?_⟩
            · have hrun := hcmp.trans hbr6
              simpa [mergeCats, bestOfRegs, hbetter] using hrun
            · simp [hr2MV, hr2MP, bestOfRegs, bpCandidateMerge?,
                bpCandidateBetter, hbetter]
            · intro rr hrr
              obtain ⟨_, _, hT, hOne⟩ := hrr
              simp [hr2, hr1, RegFile.write, hT, hOne]
          · -- ARM (iv): the LEFT candidate wins, INCLUDING ON A TIE.
            have hcond : r2 qT = 0 := by
              rw [hr2, RegFile.write_same]
              exact if_neg (by omega)
            have hbr6 : RunsTo store program ⟨r2, Q + 6, false⟩
                ⟨r2, Q + 7, false⟩ [] [Category.branch] := by
              have h := RunsTo.brNZ_not_taken (store := store)
                (s := (⟨r2, Q + 6, false⟩ : State)) rfl h6 (by simp [hcond])
              simpa using h
            obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write mMV (l + 1) := ⟨_, rfl⟩
            have hmv : RunsTo store program ⟨r2, Q + 7, false⟩
                ⟨r3, Q + 8, false⟩ [] [Category.registerWrite] := by
              have h := RunsTo.move (store := store)
                (s := (⟨r2, Q + 7, false⟩ : State)) rfl h7
              simpa [hr3, hr2LV] using h
            obtain ⟨r4, hr4⟩ : ∃ z : RegFile, z = r3.write mMP lp := ⟨_, rfl⟩
            have hmp : RunsTo store program ⟨r3, Q + 8, false⟩
                ⟨r4, Q + 9, false⟩ [] [Category.registerWrite] := by
              have h := RunsTo.move (store := store)
                (s := (⟨r3, Q + 8, false⟩ : State)) rfl h8
              simpa [hr4, hr3, RegFile.write, mMV, qLP, hr2LP] using h
            refine ⟨r4, ?_, ?_, ?_⟩
            · have hrun := ((hcmp.trans hbr6).trans hmv).trans hmp
              simpa [mergeCats, bestOfRegs, hbetter] using hrun
            · have hMV4 : r4 mMV = l + 1 := by
                simp [hr4, hr3, RegFile.write, mMV, mMP]
              have hMP4 : r4 mMP = lp := by simp [hr4, RegFile.write]
              simp [hMV4, hMP4, bestOfRegs, bpCandidateMerge?,
                bpCandidateBetter, hbetter]
            · intro rr hrr
              obtain ⟨hMVr, hMPr, hT, hOne⟩ := hrr
              simp [hr4, hr3, hr2, hr1, RegFile.write, hMVr, hMPr, hT, hOne]

/-! ## THE DISCRIMINATORS, AND WHERE THE CHECKS RUN OUT

Two impostors, chosen at the two places this block's index differs from
its neighbours': the STRICTNESS of the comparison at `Q + 5`, and the
SOURCE REGISTER of the position move at `Q + 8`.

They are deliberately a PAIR, because they fall on opposite sides of the
category-log boundary.  The span block's `none`-arm impostor
(DD-20260719-050) was caught by a positional category comparison even
though receipt, read count, exit code and preservation all failed to
catch it; recording only that case would leave the false impression that
a category log is a sufficient backstop.  It is not: the SECOND impostor
below takes the SAME PATH as the correct block and is therefore invisible
to the category log as well. -/

/-- The empty store.  No arm may depend on the store, and using the empty
one makes that manifest. -/
def mergeStore : ReadStore := ⟨fun _ _ => none⟩

/-- The block at base `0`, with a halt at `9`, PARAMETRIC in the two
places an impostor can differ.  `cmp` is the comparison at `5` and
`posSrc` the source of the position move at `8`; everything else is held
fixed, so each fixture below varies exactly one thing. -/
def mergeProgram (cmp : Instr) (posSrc : Nat) : E1Machine.Program :=
  [ Instr.const qOne 1
  , Instr.brNZ qLV 3
  , Instr.brNZ qOne 9
  , Instr.brNZ mMV 5
  , Instr.brNZ qOne 7
  , cmp
  , Instr.brNZ qT 9
  , Instr.move mMV qLV
  , Instr.move mMP posSrc
  , Instr.halt ]

/-- The correct block is `mergeProgram` at the strict test and the
position register -- definitionally `mergeBlock 0` plus its halt. -/
theorem mergeProgram_correct_eq_mergeBlock :
    mergeProgram (Instr.natLt qT mMV qLV) qLP =
      mergeBlock 0 ++ [Instr.halt] := by rfl

/-- Both candidates entered biased; `qOne` starts at `0` and the block
sets it. -/
def mergeRegs (lv lp rv rp : Nat) : RegFile := fun r =>
  if r = qLV then lv
  else if r = qLP then lp
  else if r = mMV then rv
  else if r = mMP then rp
  else 0

/-- The arm's value, in the form the route's combiners consume. -/
def mergeOut (cmp : Instr) (posSrc lv lp rv rp : Nat) : Option (Nat × Nat) :=
  let final :=
    (E1Machine.run mergeStore (mergeProgram cmp posSrc) 20
      ⟨mergeRegs lv lp rv rp, 0, false⟩).final.regs
  bestOfRegs (final mMV) (final mMP)

/-- The arm's receipt. -/
def mergeReadLog (cmp : Instr) (posSrc lv lp rv rp : Nat) : List TraceEvent :=
  (E1Machine.run mergeStore (mergeProgram cmp posSrc) 20
    ⟨mergeRegs lv lp rv rp, 0, false⟩).readLog

/-- The arm's charge log. -/
def mergeCatLog (cmp : Instr) (posSrc lv lp rv rp : Nat) : List Category :=
  (E1Machine.run mergeStore (mergeProgram cmp posSrc) 20
    ⟨mergeRegs lv lp rv rp, 0, false⟩).catLog

/-! ### IMPOSTOR ONE: the tie, `natLe` for `natLt`

`bpCandidateBetter` is `if right.1 < left.1 then right else left` --
STRICT, so a tie keeps the LEFT candidate.  A block spelling that test
`natLe` agrees everywhere except on ties, and ties are not rare: they are
the generic case whenever two sub-ranges share a minimum excess, which is
what an RMQ over a balanced-parenthesis sequence produces constantly.

The fixture is a TIE: left `some (5, 11)`, right `some (5, 22)`. -/

/-- The correct block keeps the LEFT candidate on a tie. -/
theorem mergeTie_correct :
    mergeOut (Instr.natLt qT mMV qLV) qLP 6 11 6 22 = some (5, 11) := by rfl

/-- The `natLe` impostor takes the RIGHT one. -/
theorem mergeTie_impostor :
    mergeOut (Instr.natLe qT mMV qLV) qLP 6 11 6 22 = some (5, 22) := by rfl

/-- THE DISCRIMINATOR: strictness is load-bearing, and a block that
spelled the test `natLe` would be WRONG, not merely differently spelled. -/
theorem mergeTie_discriminates :
    mergeOut (Instr.natLt qT mMV qLV) qLP 6 11 6 22 ≠
      mergeOut (Instr.natLe qT mMV qLV) qLP 6 11 6 22 := by decide

/-- NON-ENTAILMENT: the two receipts are equal, and both are empty, so
neither a receipt check nor a read COUNT separates them. -/
theorem mergeTie_traces_agree :
    mergeReadLog (Instr.natLt qT mMV qLV) qLP 6 11 6 22 =
        mergeReadLog (Instr.natLe qT mMV qLV) qLP 6 11 6 22 ∧
      mergeReadLog (Instr.natLt qT mMV qLV) qLP 6 11 6 22 = [] :=
  ⟨by rfl, by rfl⟩

/-- What DOES catch this one, besides the value: the charge logs differ,
because the impostor branches to the exit where the correct block falls
through into two moves.  Recorded so the boundary is exact -- and so that
the CONTRAST with impostor two below is visible. -/
theorem mergeTie_catLogs_differ :
    mergeCatLog (Instr.natLt qT mMV qLV) qLP 6 11 6 22 ≠
      mergeCatLog (Instr.natLe qT mMV qLV) qLP 6 11 6 22 := by decide

/-! ### IMPOSTOR TWO: the position move's source, `qLV` for `qLP`

THE SHARPER ONE. `Q + 7` and `Q + 8` move the left candidate's two
components from ADJACENT registers, so "copy the source from the
instruction above" is a live error rather than a hypothetical one -- the
same shape of defect as the stale receipt head recorded in
DD-20260719-019.

It takes the SAME PATH as the correct block: same instructions executed,
in the same order, differing only in one operand.  So of receipt, read
count, exit code, preservation AND POSITIONAL CATEGORY LOG, **not one
rejects it**.  Only the value does.

The fixture keeps the left candidate strictly (`8 < 5` is false), so both
blocks reach the moves. -/

/-- The correct block takes the position from `qLP`. -/
theorem mergePos_correct :
    mergeOut (Instr.natLt qT mMV qLV) qLP 6 11 9 22 = some (5, 11) := by rfl

/-- The impostor takes it from `qLV`, returning the left candidate's own
BIASED VALUE as its position. -/
theorem mergePos_impostor :
    mergeOut (Instr.natLt qT mMV qLV) qLV 6 11 9 22 = some (5, 6) := by rfl

/-- THE DISCRIMINATOR. -/
theorem mergePos_discriminates :
    mergeOut (Instr.natLt qT mMV qLV) qLP 6 11 9 22 ≠
      mergeOut (Instr.natLt qT mMV qLV) qLV 6 11 9 22 := by decide

/-- NON-ENTAILMENT: equal receipts, both empty. -/
theorem mergePos_traces_agree :
    mergeReadLog (Instr.natLt qT mMV qLV) qLP 6 11 9 22 =
        mergeReadLog (Instr.natLt qT mMV qLV) qLV 6 11 9 22 ∧
      mergeReadLog (Instr.natLt qT mMV qLV) qLP 6 11 9 22 = [] :=
  ⟨by rfl, by rfl⟩

/-- **THE SHARP NON-ENTAILMENT, AND THE POINT OF THIS PAIR.** The charge
logs are EQUAL too.

So the positional category comparison that caught the span block's
`none`-arm impostor (`spanNoneArm_catLogs_differ`) is FORMALLY INCAPABLE
of rejecting this one.  A category log constrains which instructions ran;
it says nothing about their operands. -/
theorem mergePos_catLogs_agree :
    mergeCatLog (Instr.natLt qT mMV qLV) qLP 6 11 9 22 =
      mergeCatLog (Instr.natLt qT mMV qLV) qLV 6 11 9 22 := by rfl

/-- NON-ENTAILMENT: both halt, so the exit code does not separate them. -/
theorem mergePos_both_halt :
    (E1Machine.run mergeStore (mergeProgram (Instr.natLt qT mMV qLV) qLP) 20
        ⟨mergeRegs 6 11 9 22, 0, false⟩).final.halted = true ∧
      (E1Machine.run mergeStore (mergeProgram (Instr.natLt qT mMV qLV) qLV) 20
        ⟨mergeRegs 6 11 9 22, 0, false⟩).final.halted = true :=
  ⟨by rfl, by rfl⟩

/-! ### The preservation clause, EXECUTED

A clause that is proved but never executed passes every check in the
battery.  `mergeBlock_runsTo`'s third clause is therefore run here, with
the four cross-block-arm operands seeded with DISTINCT MARKS so survival
is discriminating rather than trivially true at zero. -/

/-- The fixture's register file with `70`, `71`, `75`, `76` marked.  None
is read by the block, so the marks cannot perturb the values above. -/
def mergeRegsMarked (lv lp rv rp : Nat) : RegFile := fun r =>
  if r = 70 then 91
  else if r = 71 then 92
  else if r = 75 then 93
  else if r = 76 then 94
  else mergeRegs lv lp rv rp r

/-- The four operands as the run leaves them. -/
def mergeOperands (cmp : Instr) (posSrc lv lp rv rp : Nat) : List Nat :=
  let final :=
    (E1Machine.run mergeStore (mergeProgram cmp posSrc) 20
      ⟨mergeRegsMarked lv lp rv rp, 0, false⟩).final.regs
  [final 70, final 71, final 75, final 76]

/-- EXECUTED: the marks survive the correct block on the moving arm. -/
theorem mergeOperands_preserved_correct :
    mergeOperands (Instr.natLt qT mMV qLV) qLP 6 11 9 22 = [91, 92, 93, 94] := by
  rfl

/-- EXECUTED: they survive the branch-to-exit arm too, which is the arm
that writes NOTHING and so is the one where a preservation claim is
weakest evidence. -/
theorem mergeOperands_preserved_exitArm :
    mergeOperands (Instr.natLt qT mMV qLV) qLP 6 11 3 22 = [91, 92, 93, 94] := by
  rfl

/-- EXECUTED, AND THE LAST NON-ENTAILMENT: the marks survive the POSITION
IMPOSTOR too.

Collecting the four: receipt, read count, exit code and preservation all
agree with the correct block, AND SO DOES THE CATEGORY LOG. For this
impostor the value is the ONLY instrument. That is why
`mergeBlock_runsTo`'s value clause is stated against the route's own
`bpCandidateMerge?` rather than against the block's arithmetic. -/
theorem mergeOperands_preserved_impostor :
    mergeOperands (Instr.natLt qT mMV qLV) qLV 6 11 9 22 = [91, 92, 93, 94] := by
  rfl

/-! ## COMPOSING: what `#6`, `#7` and `#8` need beyond this block

Two small facts, both cheaper than they look, recorded here so the next
lane budgets them correctly. -/

/-- **`#8` NEEDS NO THREE-WAY PRIMITIVE.**

`bpCandidateMerge3?` (`Candidate.lean:24`) is DEFINITIONALLY
`bpCandidateMerge? (bpCandidateMerge? left middle) right`, left-
associated, so `CrossMacroCandidateComputation` is this block run TWICE
and the reassociation is `rfl` rather than a proof obligation.

Stated as a checked one-liner rather than left as a remark: the
`E1_LIVE_STATE.md` ladder labelled `#8` "merge3", which reads as a third
primitive owed. It is not one. -/
theorem merge3_eq_two_merges (left middle right : Option (Nat × Nat)) :
    bpCandidateMerge3? left middle right =
      bpCandidateMerge? (bpCandidateMerge? left middle) right := rfl

/-- THE SHUTTLE: two moves restaging a merge result as the NEXT merge's
left input.

`mergeBlock` merges `qLV`/`qLP` into `mMV`/`mMP` IN PLACE, which is what
makes the interior's output pair uniform -- but it also means chaining two
merges needs the accumulated result moved back to the left slots first.
Two instructions, no branch, no read, and independent of its own base. -/
def mergeShuttle : List Instr :=
  [ Instr.move qLV mMV
  , Instr.move qLP mMP ]

@[simp] theorem mergeShuttle_length : mergeShuttle.length = 2 := rfl

/-- What the shuttle leaves alone: everything but the two left slots. -/
abbrev ShuttleUntouched (r : Nat) : Prop := r ≠ 123 ∧ r ≠ 124

/-- The four cross-block-arm operands survive the shuttle too, so a
chained combiner still discharges `hInterior`'s preservation half. -/
theorem shuttleUntouched_at_crossBlockArm_operands :
    ShuttleUntouched 70 ∧ ShuttleUntouched 71 ∧ ShuttleUntouched 75 ∧
      ShuttleUntouched 76 := by
  decide

/-- Exact simulation of the shuttle.  Read-free, two register writes, and
it leaves BOTH pairs holding the candidate -- the left pair because that
is the point, the output pair because the next merge reads it as its right
operand when the chain continues. -/
theorem mergeShuttle_runsTo
    (store : ReadStore) {program : E1Machine.Program} {Q : Nat}
    (hHost : HostedAt program Q mergeShuttle)
    (regs : RegFile) (v p : Nat)
    (hMV : regs mMV = v) (hMP : regs mMP = p) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 2, false⟩ []
        [Category.registerWrite, Category.registerWrite] ∧
      regs' qLV = v ∧ regs' qLP = p ∧
      regs' mMV = v ∧ regs' mMP = p ∧
      (∀ r, ShuttleUntouched r → regs' r = regs r) := by
  have hf : ∀ (k m : Nat) (instr : Instr), k < 2 →
      mergeShuttle[k]? = some instr → Q + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.move qLV mMV) :=
    hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.move qLP mMP) :=
    hf 1 _ _ (by omega) rfl (by omega)
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write qLV v := ⟨_, rfl⟩
  have hs0 : RunsTo store program ⟨regs, Q, false⟩
      ⟨r1, Q + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr1, hMV] using h
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write qLP p := ⟨_, rfl⟩
  have hs1 : RunsTo store program ⟨r1, Q + 1, false⟩
      ⟨r2, Q + 2, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨r1, Q + 1, false⟩ : State)) rfl h1
    simpa [hr2, hr1, RegFile.write, qLV, mMP, hMP] using h
  refine ⟨r2, hs0.trans hs1, ?_, ?_, ?_, ?_, ?_⟩
  · simp [hr2, hr1, RegFile.write, qLV, qLP]
  · simp [hr2, RegFile.write]
  · simp [hr2, hr1, RegFile.write, qLV, qLP, mMV, hMV]
  · simp [hr2, hr1, RegFile.write, qLV, qLP, mMP, hMP]
  · intro r hr
    obtain ⟨hLV, hLP⟩ := hr
    simp [hr2, hr1, RegFile.write, hLV, hLP]

end E1InteriorMerge
end WordRAM
end RMQ
