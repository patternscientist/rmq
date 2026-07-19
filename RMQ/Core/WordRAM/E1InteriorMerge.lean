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
`crossBlockArmProgramAt_runsTo`'s `hInterior` (`E1CrossBlockArm.lean:1143`)
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

end E1InteriorMerge
end WordRAM
end RMQ
