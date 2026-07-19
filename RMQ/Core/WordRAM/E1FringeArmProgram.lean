import RMQ.Core.WordRAM.E1FringeArmBlock

/-!
# E1 amended machine: the fringe ARM's INSTRUCTION-LIST form (M3d-8)

`fringeArm_runsTo` (`E1FringeArmBlock.lean:940`) simulates a whole charged
fringe arm, but it is stated entirely against HOSTING HYPOTHESES: six
separate `HostedAt` facts plus one `program[_]?` fact, one per segment.
Until this module there was no arm PROGRAM -- `rg` for `fringeArmProgram`
returned nothing -- so no caller could discharge those seven hypotheses
from a single assumption, and the cross-block arm (which needs TWO arms in
one layout) had nothing to lay out.

This is the counterpart of `sameBlockLegProgramAt`
(`E1SameBlockLeg.lean:595`) for the arm.

## BASE-PARAMETRIC FROM THE START, AND WHY

`sameBlockLegProgram` was originally built pinned at base `0`, hard-coding
FOUR internal addresses (`fringeMerge 97`, the `brNZ fCnt 97` back edge,
`fringeCandGlobal 164`, and the rank block's segment base `5`).  Hosting it
behind a dispatch then required a full rebuild plus a `_zero` specialisation
lemma to keep the landed base-`0` results from regressing (M3d-6).

`fringeArmProgramAt` takes the host base `A` as a parameter from the
outset.  Its THREE internal addresses -- the fold merge target `A + 21`,
the fold back edge `A + 21`, and the epilogue's own base `A + 88` -- are
all `A`-relative, so there is no base-`0` version to specialise from and no
rebuild to schedule.  The witness section below runs the arm at base `2`,
where the internal targets are `23` and `90`, precisely so that the layout
cannot typecheck by the base-`0` accident (`0 + 21 = 21`).

## Layout

    A          fringeArmPrologue c              (21)   init + 4 window reads
    A + 21     fringePrefix S c                 (32)   fold body, part 1
    A + 53     fringeMerge (A + 21)             (13)   fold body, part 2
    A + 66     fringeShift c L ++ fringeAdvance (21)   fold body, part 3
    A + 87     brNZ fCnt (A + 21)               (1)    fold back edge
    A + 88     fringeCandGlobal (A + 88)        (7)    global rebase
    A + 95                                             arm exit

The three middle segments are exactly the three groups of
`fringeLoopBody S c L (A + 21)` (`E1FringeFoldBlock.lean:255`), which is
what lets the width certificate delegate to `fringeLoopBody_fits` rather
than re-enumerate 66 instructions.
-/

namespace RMQ
namespace WordRAM
namespace E1FringeArmProgram

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open RMQ.SuccinctClose
open RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory

/-- Peel one segment off a hosted concatenation, landing the remainder at
a named address.  (`E1SameBlockLeg` has a `private` copy; re-declared here
rather than de-privatising a frozen module.) -/
private theorem hostedAt_step {program : E1Machine.Program} {base : Nat}
    {code₁ code₂ : List Instr} {n : Nat}
    (h : HostedAt program base (code₁ ++ code₂))
    (hn : base + code₁.length = n) :
    HostedAt program n code₂ := hn ▸ h.append_right

/-! ## The layout -/

/-- The 95-instruction charged fringe arm laid out for host base `A`.
All three internal addresses are `A`-relative. -/
def fringeArmProgramAt (S c L A : Nat) : List Instr :=
  fringeArmPrologue c ++
    (fringePrefix S c ++
      (fringeMerge (A + 21) ++
        ((fringeShift c L ++ fringeAdvance) ++
          ([Instr.brNZ fCnt (A + 21)] ++ fringeCandGlobal (A + 88)))))

@[simp] theorem fringeArmProgramAt_length (S c L A : Nat) :
    (fringeArmProgramAt S c L A).length = 95 := by
  simp [fringeArmProgramAt]

/-- The arm's three fold segments ARE the fold body's three groups.  This
is the identity the width certificate delegates through, and it also
records that the arm hosts a genuine `fringeLoopBody` rather than a
look-alike. -/
theorem fringeArmProgramAt_fold_eq (S c L A : Nat) :
    fringePrefix S c ++
        (fringeMerge (A + 21) ++ (fringeShift c L ++ fringeAdvance)) =
      fringeLoopBody S c L (A + 21) := rfl

/-! ## Hosting decomposition -/

/--
EVERY hosting hypothesis of `fringeArm_runsTo` at base `A` follows from
the single assumption that `fringeArmProgramAt ... A` is hosted at `A`.

Each offset is FORCED by the preceding segments' lengths through
`append_right`, so the layout table in the module header is checked, not
asserted: an off-by-one anywhere makes this fail to typecheck.
-/
theorem fringeArmProgramAt_hosts {program : E1Machine.Program}
    (S c L A : Nat)
    (hHost : HostedAt program A (fringeArmProgramAt S c L A)) :
    HostedAt program A (fringeArmPrologue c) ∧
      HostedAt program (A + 21) (fringePrefix S c) ∧
      HostedAt program (A + 21 + 32) (fringeMerge (A + 21)) ∧
      HostedAt program (A + 21 + 45) (fringeShift c L ++ fringeAdvance) ∧
      program[A + 21 + 66]? = some (.brNZ fCnt (A + 21)) ∧
      HostedAt program (A + 88) (fringeCandGlobal (A + 88)) := by
  rw [fringeArmProgramAt] at hHost
  have h1 := hostedAt_step (n := A + 21) hHost (by simp)
  have h2 := hostedAt_step (n := A + 21 + 32) h1 (by simp)
  have h3 := hostedAt_step (n := A + 21 + 45) h2 (by simp)
  have h4 := hostedAt_step (n := A + 21 + 66) h3 (by simp)
  have h5 := hostedAt_step (n := A + 88) h4 (by simp)
  refine ⟨hHost.append_left, h1.append_left, h2.append_left,
    h3.append_left, ?_, h5⟩
  -- NOTE: `decide` refuses this with `A` free (M3d-7 gotcha 5); the side
  -- condition `0 < [_].length` is computed by `simp` instead.
  exact h4.append_left 0 (by simp)

/-! ## The arm at a host base -/

/--
THE CHARGED FRINGE ARM AT AN ARBITRARY HOST BASE.

`fringeArm_runsTo` restated so that the seven hosting facts are replaced by
the single hypothesis that the arm's own layout is hosted at `A`.  The
conclusion is unchanged: four charged window reads followed positionally by
the accepted fold object's trace, the frozen `fringeArmCats`, the route's
`bpFringeCandGlobal` of the fold's best candidate in `fRV`/`fRP`, and
(M3d-9) the arm's REGISTER PRESERVATION clause on `FringeArmUntouched`.

The preservation clause is what the cross-block composition consumes: the
left stash's merge slots `mLV` (75) and `mLP` (76) satisfy
`FringeArmUntouched` (`by decide`), so they survive the RIGHT arm.
-/
theorem fringeArmProgramAt_runsTo
    (store : ReadStore) {program : E1Machine.Program} {A S c L : Nat}
    (hc : c ≤ L)
    (hHost : HostedAt program A (fringeArmProgramAt S c L A))
    (base bb relLo relHi seed start : Nat)
    (hL : 0 < L) (hW : WindowDense store base L)
    (regs : RegFile)
    (hBase : regs fBase = base) (hLo : regs fLo = relLo)
    (hHi : regs fHi = relHi) (hAcc : regs fAcc = seed)
    (hBB : regs fBB = bb) (hSeed : regs fSeed = seed)
    (hStart : regs fStart = start) :
    ∃ regsF : RegFile,
      RunsTo store program ⟨regs, A, false⟩ ⟨regsF, A + 95, false⟩
        (windowReadEvents store base ++
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
            (windowBitsOfStore store base) seed relLo relHi
            (Nat.min (relHi / c + 1) 33)).trace)
        (fringeArmCats store S c (windowBitsOfStore store base)
          relLo relHi seed (Nat.min (relHi / c + 1) 33)) ∧
      some (regsF fRV, regsF fRP) =
        bpFringeCandGlobal bb seed start
          (bpFringeChunkFoldTraceResultAtSegmentWithStore store S c
            (windowBitsOfStore store base) seed relLo relHi
            (Nat.min (relHi / c + 1) 33)).value.2 ∧
      (∀ r, FringeArmUntouched r -> regsF r = regs r) := by
  obtain ⟨p0, p1, p2, p3, p4, p5⟩ := fringeArmProgramAt_hosts S c L A hHost
  exact fringeArm_runsTo store hc p0 p1 p2 p3 p4 p5 base bb relLo relHi
    seed start hL hW regs hBase hLo hHi hAcc hBB hSeed hStart

/-! ## Width certificate (REQ-E1-02 machinery, arm scope) -/

/--
CONSTRUCTOR-EXHAUSTIVE WIDTH CERTIFICATE FOR THE WHOLE ARM.

Every one of the 95 instructions satisfies `Instr.FieldsFit w`
(`E1Machine.lean:503`), which matches on every constructor and has NO
wildcard arm returning `True`.  The three fold segments delegate to
`fringeLoopBody_fits`, whose `divConst` positivity arms are discharged from
`hcpos`/`hc` rather than assumed.

The single `A`-dependent hypothesis `A + 95 < 2 ^ w` is what forces the
three rebased internal addresses to fit: the fold target `A + 21`, the back
edge `A + 21`, and the epilogue at `A + 88` (needing `A + 95`).
-/
theorem fringeArmProgramAt_fits {w S c L A : Nat}
    (hreg : 68 < 2 ^ w) (hS : S < 2 ^ w)
    (hcpos : 0 < c) (hc : c ≤ L)
    (hpow : 2 ^ L < 2 ^ w)
    (hmix : (c + 1) * (2 * c + 2) < 2 ^ w)
    (hA : A + 95 < 2 ^ w) :
    ∀ instr ∈ fringeArmProgramAt S c L A, Instr.FieldsFit w instr := by
  have hcw : c < 2 ^ w := by
    have : 2 ^ c ≤ 2 ^ L := Nat.pow_le_pow_right (by omega) hc
    have hlt : c < 2 ^ c := Nat.lt_two_pow_self
    omega
  have hbody : ∀ instr ∈ fringeLoopBody S c L (A + 21),
      Instr.FieldsFit w instr :=
    fringeLoopBody_fits (by omega) hS hcpos hc hpow hmix (by omega)
  intro instr hinstr
  simp only [fringeArmProgramAt, List.mem_append, List.mem_singleton,
    or_assoc] at hinstr
  rcases hinstr with h | h | h | h | h | h | h
  · exact fringeArmPrologue_fits (by omega) hcpos hcw instr h
  · exact hbody instr (List.mem_append.mpr (Or.inl h))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inl h))))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inl h))))))
  · exact hbody instr
      (List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr
        (List.mem_append.mpr (Or.inr h))))))
  · -- the fold back edge; `fCnt` is an abbrev and opaque to `omega`
    subst h
    refine ⟨?_, by omega⟩
    show (52 : Nat) < 2 ^ w
    omega
  · exact fringeCandGlobal_fits w (A + 88) hreg (by omega) instr h

/-! ## EXECUTION WITNESS: the arm hosted at a NONZERO base, and run

A layout theorem plus a width certificate would both still typecheck if
the arm never actually ran.  This section RUNS it.

The host base is `2`, not `0`, deliberately: at base `0` the internal
addresses `A + 21` and `A + 88` coincide with their own offsets and the
layout typechecks by accident.  At base `2` the fold back edge targets
`23` and the epilogue sits at `90`, and `fringeArmWitness_internalAddresses`
observes both in the emitted instruction list.

Unlike the merge block (`E1CandMerge3`, read-free), the arm is
READ-BEARING, so the executed read log is nonempty and is itself an
observable -- see `fringeArmWitness_readsAreCharged`.
-/

/-- Witness store: every read succeeds with the supplied word, so the run
is driven by the arm's own arithmetic rather than by absent reads. -/
def armWitnessStore (w : List Bool) : ReadStore := ⟨fun _ _ => some w⟩

/-- Witness program: two instructions of padding, the arm at base `2`,
then `halt`.  The padding is what makes the base nonzero. -/
def armWitnessProgram (S c L : Nat) : E1Machine.Program :=
  [Instr.const 200 0, Instr.const 200 0] ++
    fringeArmProgramAt S c L 2 ++ [Instr.halt]

@[simp] theorem armWitnessProgram_length (S c L : Nat) :
    (armWitnessProgram S c L).length = 98 := by
  simp [armWitnessProgram]

/-- The witness program hosts the arm at base `2`. -/
theorem armWitnessProgram_hosts (S c L : Nat) :
    HostedAt (armWitnessProgram S c L) 2 (fringeArmProgramAt S c L 2) := by
  have h : HostedAt (armWitnessProgram S c L) 0
      ([Instr.const 200 0, Instr.const 200 0] ++
        (fringeArmProgramAt S c L 2 ++ [Instr.halt])) := by
    simpa [armWitnessProgram, List.append_assoc] using
      hostedAt_self (armWitnessProgram S c L)
  exact (hostedAt_step (n := 2) h (by simp)).append_left

/-- THE INTERNAL ADDRESSES REALLY MOVED WITH THE BASE.  At base `2` the
fold back edge targets `23` and the epilogue's presence branch targets
`95`; at base `0` these would read `21` and `93`.  Stated as executable
equalities so the rebasing is CHECKED, not described. -/
theorem fringeArmWitness_internalAddresses :
    ((fringeArmProgramAt 7 2 4 2)[87]? = some (Instr.brNZ fCnt 23)) ∧
      ((fringeArmProgramAt 7 2 4 2)[89]? = some (Instr.brNZ fBV 95)) :=
  ⟨rfl, rfl⟩

/-- Register file for one witness fixture. -/
def armWitnessRegs (base relLo relHi seed bb start : Nat) : RegFile :=
  RegFile.write (RegFile.write (RegFile.write (RegFile.write
    (RegFile.write (RegFile.write (RegFile.write
      (fun _ => 0) fBase base) fLo relLo) fHi relHi) fAcc seed)
        fBB bb) fSeed seed) fStart start

/-- Observable outcome of one witness run: exit pc, halted flag, modeled
steps, the rebased candidate value and position, and the number of charged
reads. -/
def armWitnessOutcome (w : List Bool)
    (S c L base relLo relHi seed bb start : Nat) :
    Nat × Bool × Nat × Nat × Nat × Nat :=
  let r := run (armWitnessStore w) (armWitnessProgram S c L) 4000
    ⟨armWitnessRegs base relLo relHi seed bb start, 0, false⟩
  (r.final.pc, r.final.halted, r.steps, r.final.regs fRV, r.final.regs fRP,
    r.readLog.length)

-- The multi-pass fixtures below run 143-271 modeled steps, each unfolding
-- `run`'s fuel recursion once; the default elaboration recursion budget is
-- not enough to reduce them.  (Precedent: `E1DenseSelectBlock.lean`'s
-- 193-instruction hosting peel, M3c-5c.)
set_option maxRecDepth 40000

/-- PATH 1: one fold pass, occupied best at window offset `2`. -/
theorem armWitness_path1 :
    armWitnessOutcome [true, false, true, false] 7 2 4 100 0 1 0 500 900 =
      (97, true, 88, 0, 502, 5) := rfl

/-- PATH 2: one fold pass, occupied best at window offset `0`. -/
theorem armWitness_path2 :
    armWitnessOutcome [false, false, false, false] 7 2 4 100 0 1 0 500 900 =
      (97, true, 88, 0, 500, 5) := rfl

/-- PATH 3: one fold pass, occupied best carrying a nonzero VALUE. -/
theorem armWitness_path3 :
    armWitnessOutcome [true, true, true, true] 7 2 4 100 0 1 0 500 900 =
      (97, true, 88, 3, 500, 5) := rfl

/-- PATH 4: TWO fold passes -- the back edge at `23` is taken. -/
theorem armWitness_path4 :
    armWitnessOutcome [true, false, true, false] 7 2 4 100 0 5 0 500 900 =
      (97, true, 210, 0, 502, 7) := rfl

/-- PATH 5: THREE fold passes at chunk width `1`. -/
theorem armWitness_path5 :
    armWitnessOutcome [true, false, true, false] 7 1 4 100 0 3 0 500 900 =
      (97, true, 271, 1, 501, 8) := rfl

/-- PATH 6: the fold's window gate excludes every chunk, so the epilogue
takes its SEED-FALLBACK arm and the position is the seed's `start`
(`900`), not a window rebase. -/
theorem armWitness_path6 :
    armWitnessOutcome [true, false, true, false] 7 2 4 100 9 1 0 500 900 =
      (97, true, 86, 0, 900, 5) := rfl

/-- PATH 7: seed fallback after TWO fold passes. -/
theorem armWitness_path7 :
    armWitnessOutcome [true, false, true, false] 7 2 4 100 4 3 0 500 900 =
      (97, true, 143, 0, 900, 6) := rfl

/-- THE SEVEN EXECUTED PATHS ARE PAIRWISE DISTINGUISHABLE on the
`(steps, value, position, reads)` observable.  This is the statement that
would fail if any two control paths collapsed -- in particular if the
epilogue's seed-fallback arm (paths 6, 7) were unreachable, or if the fold
back edge never fired (paths 4, 5, 7). -/
theorem armWitness_paths_distinguishable :
    let obs := fun (o : Nat × Bool × Nat × Nat × Nat × Nat) =>
      (o.2.2.1, o.2.2.2.1, o.2.2.2.2.1, o.2.2.2.2.2)
    [ obs (armWitnessOutcome [true, false, true, false] 7 2 4 100 0 1 0 500 900)
    , obs (armWitnessOutcome [false, false, false, false] 7 2 4 100 0 1 0 500 900)
    , obs (armWitnessOutcome [true, true, true, true] 7 2 4 100 0 1 0 500 900)
    , obs (armWitnessOutcome [true, false, true, false] 7 2 4 100 0 5 0 500 900)
    , obs (armWitnessOutcome [true, false, true, false] 7 1 4 100 0 3 0 500 900)
    , obs (armWitnessOutcome [true, false, true, false] 7 2 4 100 9 1 0 500 900)
    , obs (armWitnessOutcome [true, false, true, false] 7 2 4 100 4 3 0 500 900)
    ].Nodup := by decide

/-- EVERY witness path charges at least the four window reads, and the
multi-pass paths charge strictly more.  The arm is read-BEARING, so unlike
the merge block its receipt is a live discriminator. -/
theorem fringeArmWitness_readsAreCharged :
    [ (armWitnessOutcome [true, false, true, false] 7 2 4 100 0 1 0 500 900).2.2.2.2.2
    , (armWitnessOutcome [true, false, true, false] 7 2 4 100 0 5 0 500 900).2.2.2.2.2
    , (armWitnessOutcome [true, false, true, false] 7 1 4 100 0 3 0 500 900).2.2.2.2.2
    , (armWitnessOutcome [true, false, true, false] 7 2 4 100 4 3 0 500 900).2.2.2.2.2 ]
      = [5, 7, 8, 6] := rfl

end E1FringeArmProgram
end WordRAM
end RMQ
