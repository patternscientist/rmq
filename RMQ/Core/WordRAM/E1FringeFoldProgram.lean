import RMQ.Core.WordRAM.E1FringeFoldBlock

/-!
# A STANDALONE host for the fringe fold (M3d-8)

`FringeFoldUntouched` (`E1FringeFoldBlock.lean:962`) is the fringe fold's
own preservation clause.  Until this module there was nowhere to execute it.

WHY THE ARM'S HOST WILL NOT DO.  The validator's phase 3h runs the whole
fringe ARM (`E1FringeArmProgram.armWitnessProgram`) and checks
`FringeArmUntouched` (`r < 40 ∨ (63 ≤ r ∧ r ≠ 67 ∧ r ≠ 68)`).  That is a
STRICTLY WEAKER predicate than `FringeFoldUntouched` (`r < 40 ∨ 63 ≤ r`),
and the gap is not slack: the arm's PROLOGUE writes `67` and `68`, which the
fold itself never touches.  Running the arm and checking the fold's clause
would therefore fail at `67`/`68` CORRECTLY, and the failure would say
nothing about the fold.  The fold has to be run BY ITSELF, at its own loop
base, which is what this module supplies.

The bank is `40..62` exactly (`fOne = 40` through `fX = 62`,
`E1FringeFoldBlock.lean:62-106`), so `FringeFoldUntouched` is precisely
"outside the bank" -- it is checked here against the fold's OWN write set,
not against a neighbouring block's.

DD-20260719-145.
-/

namespace RMQ
namespace WordRAM
namespace E1FringeFoldProgram

open E1Machine
open E1FringeFoldBlock

/-- Advance a hosting fact past a leading segment.  A per-module private
copy, matching `E1FringeArmProgram.lean:62` and `E1CrossBlockArm.lean:126`;
those are `private`, so this is not a duplicate that could have been
imported. -/
private theorem hostedAt_step {program : E1Machine.Program} {base : Nat}
    {code₁ code₂ : List Instr} {n : Nat}
    (h : HostedAt program base (code₁ ++ code₂))
    (hn : base + code₁.length = n) :
    HostedAt program n code₂ := hn ▸ h.append_right

/-- Witness store: every read succeeds with the supplied word, so the run is
driven by the fold's own arithmetic rather than by absent reads. -/
def foldWitnessStore (w : List Bool) : ReadStore := ⟨fun _ _ => some w⟩

/--
STANDALONE FOLD HOST.  Two instructions of padding, the 66-instruction loop
body at base `2`, the back edge, then `halt`.

The padding is what makes the loop base NONZERO, so an address the fold
computes absolutely instead of relative to its base shows up as a wrong
target rather than typechecking by accident.  This is the same discipline
`armWitnessProgram` (`E1FringeArmProgram.lean:240`) applies, and it is the
reason the base is `2` rather than `0`.
-/
def foldWitnessProgram (S c L : Nat) : E1Machine.Program :=
  [Instr.const 200 0, Instr.const 200 0] ++
    (fringePrefix S c ++
      (fringeMerge 2 ++
        ((fringeShift c L ++ fringeAdvance) ++
          ([Instr.brNZ fCnt 2] ++ [Instr.halt]))))

@[simp] theorem foldWitnessProgram_length (S c L : Nat) :
    (foldWitnessProgram S c L).length = 70 := by
  simp [foldWitnessProgram]

/-- The three segments this program lays out ARE the fold body's three
groups, at loop base `2`.  Written out because the layout above is
right-associated for the hosting proof, and without this the module would
only be asserting that it hosts a fold rather than showing it hosts THE
fold. -/
theorem foldWitnessProgram_fold_eq (S c L : Nat) :
    fringePrefix S c ++
        (fringeMerge 2 ++ (fringeShift c L ++ fringeAdvance)) =
      fringeLoopBody S c L 2 := rfl

/-! ## The hosting hypotheses of `fringeFoldLoop_runsTo_accepted`, discharged

Each of the four is discharged against THIS program, so the validator's run
is a run of the very object the accepted theorem talks about. -/

/-- EVERY hosting hypothesis of `fringeFoldLoop_runsTo_accepted`, discharged
against this program at once.  Each offset is FORCED by the preceding
segments' lengths through `hostedAt_step`, so the layout is checked rather
than asserted: an off-by-one anywhere makes this fail to typecheck. -/
theorem foldWitnessProgram_hosts (S c L : Nat) :
    HostedAt (foldWitnessProgram S c L) 2 (fringePrefix S c) ∧
      HostedAt (foldWitnessProgram S c L) (2 + 32) (fringeMerge 2) ∧
      HostedAt (foldWitnessProgram S c L) (2 + 45)
        (fringeShift c L ++ fringeAdvance) ∧
      (foldWitnessProgram S c L)[2 + 66]? = some (Instr.brNZ fCnt 2) := by
  have hHost := hostedAt_self (foldWitnessProgram S c L)
  rw [foldWitnessProgram] at hHost
  have h1 := hostedAt_step (n := 2) hHost (by simp)
  have h2 := hostedAt_step (n := 2 + 32) h1 (by simp)
  have h3 := hostedAt_step (n := 2 + 45) h2 (by simp)
  have h4 := hostedAt_step (n := 2 + 66) h3 (by simp)
  refine ⟨h1.append_left, h2.append_left, h3.append_left, ?_⟩
  exact h4.append_left 0 (by simp)

/-- Zero-seeded register file carrying exactly the fold's declared inputs.
The validator re-runs each fixture on this and compares the answer, which is
what shows the fold reads no register it does not initialise. -/
def foldWitnessRegs (c relLo relHi seed count w0 w1 w2 w3 : Nat) : RegFile :=
  RegFile.write (RegFile.write (RegFile.write (RegFile.write
    (RegFile.write (RegFile.write (RegFile.write (RegFile.write
      (RegFile.write (RegFile.write (RegFile.write (RegFile.write
        (fun _ => 0) fOne 1) fC c) fLo relLo) fHi relHi)
        fJC 0) fCnt count) fAcc seed) fBV 0)
        fW0 w0) fW1 w1) fW2 w2) fW3 w3

end E1FringeFoldProgram
end WordRAM
end RMQ
