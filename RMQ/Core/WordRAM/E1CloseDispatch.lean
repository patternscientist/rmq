import RMQ.Core.WordRAM.E1SameBlockLeg

/-!
# E1 amended machine: the same-block / cross-block BRANCH DISPATCH (M3d-5)

The accepted close/LCA route branches ONCE, at the top, on whether the two
query close positions fall in the same summary block:

    let blockSize := canonicalBPRelativeSummaryBlockSizeRaw shape
    if blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose then
      bpChunkedSameBlockCloseDecoded... else bpChunkedCrossBlockClose...

(`ChargedFringeWiring.lean:496`, and identically at `:39` for the costed
twin and `:57` for the structural trace twin.)

This module encodes that test.

## Why this block needs no new instruction, and is NOT the blocked leg

`blockOfClose blockSize close` is `close / blockSize`
(`BlockLocal.lean:864`), and on the accepted route the divisor is always
`canonicalBPRelativeSummaryBlockSizeRaw shape = 2 * (Nat.log2 shape.size + 1)`
(`RelativeSummary.lean:1240`/`:1237`) -- a function of `shape` ALONE.  It
does not depend on `leftClose`, `rightClose`, the store, or any value read
from memory, so it is an ENCODABLE IMMEDIATE and `divConst` applies
directly.  Positivity, which `divConst`'s width arm additionally demands,
is `canonicalBPRelativeSummaryBlockSizeRaw_pos`
(`RelativeSummary.lean:2488`).

This is exactly the distinction that keeps the interior leg blocked while
this block is not.  The interior leg's `bpSparseLogSpan blockCount`
(`EndpointFringe/PrefixRange/SparseArgMin.lean:598`) takes `Nat.log2` of a
RUNTIME-DERIVED `blockCount` and feeds the result to an accepted read
address; no immediate can encode it.  Here the `Nat.log2` is applied to
`shape.size`, is fully determined before the machine starts, and never
reaches a read address.  Nothing in this module computes a logarithm at
run time.

## The dispatch is four instructions

Two constant divisions, one equality, one branch.  The branch is TAKEN on
the same-block case, matching the route's `then`; the cross-block arm is
the fall-through.  The two endpoint registers `fClose` and `fRight` are
READ ONLY -- both arms consume them afterwards, so the block computes into
three fresh bank slots and clobbers nothing the arms need.
-/

namespace RMQ
namespace WordRAM
namespace E1CloseDispatch

open E1Machine
open E1FringeArmBlock
open E1SameBlockArm
open RMQ.SuccinctClose

/-! ## Bank slots

The fringe/same-block bank runs to `fRight = 71`
(`E1SameBlockArm.lean:442`).  The dispatch takes the next three. -/

/-- The left endpoint's summary block index. -/
abbrev dLB : Nat := 72

/-- The right endpoint's summary block index. -/
abbrev dRB : Nat := 73

/-- The same-block indicator: `1` when the two blocks agree, else `0`. -/
abbrev dSame : Nat := 74

/-! ## The block -/

/-- The straight-line part of the dispatch: both block indices and the
comparison.  Split out because `brNZ` is not straight-line and so cannot
go through `RunsTo.straight`. -/
def closeDispatchPrefix (blockSize : Nat) : List Instr :=
  [ .divConst dLB fClose blockSize   -- D+0  leftBlock  = leftClose  / bs
  , .divConst dRB fRight blockSize   -- D+1  rightBlock = rightClose / bs
  , .natEq dSame dLB dRB ]           -- D+2  same-block indicator

/-- The same-block / cross-block dispatch at base `D` (four instructions).
On the same-block case control transfers to `target`; on the cross-block
case it falls through to `D + 4`. -/
def closeDispatch (blockSize target : Nat) : List Instr :=
  closeDispatchPrefix blockSize ++ [ Instr.brNZ dSame target ]

@[simp] theorem closeDispatchPrefix_length (blockSize : Nat) :
    (closeDispatchPrefix blockSize).length = 3 := rfl

@[simp] theorem closeDispatch_length (blockSize target : Nat) :
    (closeDispatch blockSize target).length = 4 := rfl

/-- Category log of the dispatch: two arithmetic ticks, one comparison,
one branch.  No read; the dispatch touches no memory. -/
def closeDispatchCats : List Category :=
  [.arithmetic, .arithmetic, .comparison, .branch]

/-- The dispatch charges no `memoryRead` tick. -/
theorem closeDispatchCats_no_read :
    Category.memoryRead ∉ closeDispatchCats := by decide

/-- Constructor-exhaustive width certificate for the dispatch.  No
wildcard arm.  `divConst` additionally requires a POSITIVE divisor, which
is why `hpos` is a hypothesis and not an afterthought. -/
theorem closeDispatch_fits (w blockSize target : Nat)
    (hpos : 0 < blockSize) (hbs : blockSize < 2 ^ w) (ht : target < 2 ^ w)
    (hw : 74 < 2 ^ w) :
    ∀ instr ∈ closeDispatch blockSize target, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h70 : (70 : Nat) < 2 ^ w := by omega
  have h71 : (71 : Nat) < 2 ^ w := by omega
  have h72 : (72 : Nat) < 2 ^ w := by omega
  have h73 : (73 : Nat) < 2 ^ w := by omega
  have h74 : (74 : Nat) < 2 ^ w := hw
  simp only [closeDispatch, closeDispatchPrefix, List.cons_append,
    List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hinstr
  rcases hinstr with h | h | h | h <;> subst h
  · exact ⟨h72, h70, hpos, hbs⟩
  · exact ⟨h73, h71, hpos, hbs⟩
  · exact ⟨h74, h72, h73⟩
  · exact ⟨h74, ht⟩

/-- Every prefix instruction is straight-line. -/
theorem closeDispatchPrefix_straight (blockSize : Nat) :
    ∀ instr ∈ closeDispatchPrefix blockSize, instr.isStraight = true := by
  intro instr hinstr
  simp only [closeDispatchPrefix, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with rfl | rfl | rfl <;> rfl

local macro "dispatch_eval" : tactic =>
  `(tactic| straight_eval [closeDispatchPrefix, dLB, dRB, dSame, fClose,
      fRight])

/-- The dispatch writes only its own three scratch slots.  Stated in
NUMERALS, not the register abbrevs, so `omega` can use it downstream. -/
abbrev CloseDispatchUntouched (r : Nat) : Prop :=
  r ≠ 72 ∧ r ≠ 73 ∧ r ≠ 74

/-- Exact simulation of the straight-line prefix: no receipt, three ticks,
and the same-block indicator in `dSame` stated in the ROUTE's own
`blockOfClose` vocabulary. -/
theorem closeDispatchPrefix_runsTo
    (store : ReadStore) {program : E1Machine.Program} {D : Nat}
    {blockSize : Nat}
    (hHost : HostedAt program D (closeDispatchPrefix blockSize))
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, D, false⟩ ⟨regs', D + 3, false⟩ []
        [Category.arithmetic, Category.arithmetic, Category.comparison] ∧
      regs' dLB = blockOfClose blockSize leftClose ∧
      regs' dRB = blockOfClose blockSize rightClose ∧
      regs' dSame =
        (if blockOfClose blockSize leftClose =
            blockOfClose blockSize rightClose then 1 else 0) ∧
      (∀ r, CloseDispatchUntouched r → regs' r = regs r) := by
  have hrun := RunsTo.straight store (closeDispatchPrefix blockSize)
    (closeDispatchPrefix_straight blockSize) D hHost regs
  refine ⟨straightRegs store (closeDispatchPrefix blockSize) regs, ?_, ?_, ?_,
    ?_, ?_⟩
  · simpa using hrun
  · subst hClose
    dispatch_eval
    rfl
  · subst hRight
    dispatch_eval
    rfl
  · subst hClose
    subst hRight
    dispatch_eval
    rfl
  · intro r hr
    obtain ⟨h72, h73, h74⟩ := hr
    dispatch_eval
    simp [h72, h73, h74]

/-! ## The two branch directions

Both theorems below are stated against the ROUTE condition, so a caller
discharges exactly the hypothesis the route's `if` scrutinises -- there is
no separate machine-side notion of "same block" to keep in sync. -/

/-- SAME-BLOCK: the route condition holds, so the branch is TAKEN and
control lands at `target`.  Four ticks, no receipt, endpoints preserved. -/
theorem closeDispatch_runsTo_same
    (store : ReadStore) {program : E1Machine.Program} {D : Nat}
    {blockSize target : Nat}
    (hHost : HostedAt program D (closeDispatch blockSize target))
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hsame : blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, D, false⟩ ⟨regs', target, false⟩ []
        closeDispatchCats ∧
      regs' fClose = leftClose ∧ regs' fRight = rightClose ∧
      (∀ r, CloseDispatchUntouched r → regs' r = regs r) := by
  have hPre : HostedAt program D (closeDispatchPrefix blockSize) := by
    exact hHost.append_left
  obtain ⟨regs', hrun, _hlb, _hrb, hsm, hpres⟩ :=
    closeDispatchPrefix_runsTo store hPre regs leftClose rightClose
      hClose hRight
  have hbr : program[D + 3]? = some (.brNZ dSame target) := by
    have := hHost.append_right (code₁ := closeDispatchPrefix blockSize)
    exact this.head
  have hcond : regs' dSame ≠ 0 := by
    rw [hsm, if_pos hsame]
    decide
  have hstep :
      RunsTo store program ⟨regs', D + 3, false⟩ ⟨regs', target, false⟩ []
        [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regs', D + 3, false⟩) rfl hbr hcond
  refine ⟨regs', ?_, ?_, ?_, hpres⟩
  · have := hrun.trans hstep
    simpa [closeDispatchCats] using this
  · rw [hpres fClose (by decide), hClose]
  · rw [hpres fRight (by decide), hRight]

/-- CROSS-BLOCK: the route condition fails, so the branch is NOT taken and
control falls through to `D + 4`.  Four ticks, no receipt, endpoints
preserved. -/
theorem closeDispatch_runsTo_cross
    (store : ReadStore) {program : E1Machine.Program} {D : Nat}
    {blockSize target : Nat}
    (hHost : HostedAt program D (closeDispatch blockSize target))
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross : blockOfClose blockSize leftClose ≠
      blockOfClose blockSize rightClose) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, D, false⟩ ⟨regs', D + 4, false⟩ []
        closeDispatchCats ∧
      regs' fClose = leftClose ∧ regs' fRight = rightClose ∧
      (∀ r, CloseDispatchUntouched r → regs' r = regs r) := by
  have hPre : HostedAt program D (closeDispatchPrefix blockSize) := by
    exact hHost.append_left
  obtain ⟨regs', hrun, _hlb, _hrb, hsm, hpres⟩ :=
    closeDispatchPrefix_runsTo store hPre regs leftClose rightClose
      hClose hRight
  have hbr : program[D + 3]? = some (.brNZ dSame target) := by
    have := hHost.append_right (code₁ := closeDispatchPrefix blockSize)
    exact this.head
  have hcond : regs' dSame = 0 := by
    rw [hsm, if_neg hcross]
  have hstep :
      RunsTo store program ⟨regs', D + 3, false⟩ ⟨regs', D + 3 + 1, false⟩ []
        [Category.branch] :=
    RunsTo.brNZ_not_taken (s := ⟨regs', D + 3, false⟩) rfl hbr hcond
  refine ⟨regs', ?_, ?_, ?_, hpres⟩
  · have := hrun.trans hstep
    have hpc : D + 3 + 1 = D + 4 := by omega
    rw [hpc] at this
    simpa [closeDispatchCats] using this
  · rw [hpres fClose (by decide), hClose]
  · rw [hpres fRight (by decide), hRight]

/-! ## ANTI-VACUITY: a concrete hosting witness

`closeDispatch_runsTo_same` / `_cross` are hypothetical in `program`, and
a `HostedAt` hypothesis that no program can satisfy would make them
true-but-empty.  Worse, the branch `target` is a bare `Nat`: a theorem
about a target that is off the end of the program would be equally true
and equally worthless.

The witness below is a real program in which the dispatch sits at base
`0`, the CROSS-BLOCK fall-through at `4` is a real instruction, and the
SAME-BLOCK target is a real instruction too, at an address forced by the
cross arm's length rather than asserted.  Both branch directions are then
run END TO END on it, so the layout arithmetic is executed, not assumed.
-/

/-- A dispatch hosted in front of two arms.  The same-block target is
`4 + crossArm.length`, i.e. it is COMPUTED from the layout; getting it
wrong makes `closeDispatchProgram_hosts` fail to typecheck. -/
def closeDispatchProgram (blockSize : Nat) (crossArm sameArm : List Instr) :
    List Instr :=
  closeDispatch blockSize (4 + crossArm.length) ++ (crossArm ++ sameArm)

@[simp] theorem closeDispatchProgram_length
    (blockSize : Nat) (crossArm sameArm : List Instr) :
    (closeDispatchProgram blockSize crossArm sameArm).length =
      4 + crossArm.length + sameArm.length := by
  simp [closeDispatchProgram, Nat.add_assoc]

/-- Every hosting hypothesis holds simultaneously of a single concrete
program: the dispatch at `0`, the cross arm at the fall-through address
`4`, and the same arm at the branch target.  Each offset is forced by the
preceding segments' lengths through `append_left`/`append_right`. -/
theorem closeDispatchProgram_hosts
    (blockSize : Nat) (crossArm sameArm : List Instr) :
    HostedAt (closeDispatchProgram blockSize crossArm sameArm) 0
        (closeDispatch blockSize (4 + crossArm.length)) ∧
      HostedAt (closeDispatchProgram blockSize crossArm sameArm) 4
        crossArm ∧
      HostedAt (closeDispatchProgram blockSize crossArm sameArm)
        (4 + crossArm.length) sameArm := by
  have h0 : HostedAt (closeDispatchProgram blockSize crossArm sameArm) 0
      (closeDispatchProgram blockSize crossArm sameArm) :=
    hostedAt_self _
  rw [closeDispatchProgram] at h0
  have h1 : HostedAt (closeDispatchProgram blockSize crossArm sameArm) 4
      (crossArm ++ sameArm) := by
    have := h0.append_right
      (code₁ := closeDispatch blockSize (4 + crossArm.length))
    simpa using this
  exact ⟨h0.append_left, h1.append_left, h1.append_right⟩

/-! ### End-to-end execution on the witness

The two theorems below take the SAME concrete program and run the machine
on it in both directions, landing on a `halt` in each arm.  A wrong branch
target, a wrong fall-through offset, or a wrong segment length anywhere in
the layout makes them unprovable. -/

/-- A minimal but REAL two-arm witness: each arm is a distinguishable
register write followed by `halt`, so the final register file records
which arm actually ran. -/
def witnessCrossArm : List Instr := [ .const dSame 7, .halt ]

/-- The same-block arm of the witness. -/
def witnessSameArm : List Instr := [ .const dSame 9, .halt ]

/-- The concrete witness program: dispatch, cross arm, same arm. -/
def witnessProgram (blockSize : Nat) : List Instr :=
  closeDispatchProgram blockSize witnessCrossArm witnessSameArm

@[simp] theorem witnessProgram_length (blockSize : Nat) :
    (witnessProgram blockSize).length = 8 := by
  simp [witnessProgram, closeDispatchProgram, witnessCrossArm,
    witnessSameArm]

/-- ANTI-VACUITY, SAME-BLOCK DIRECTION.  On the witness program the
machine really does reach the same-block arm and halt there, leaving that
arm's marker `9` in `dSame`. -/
theorem witnessProgram_runs_same (store : ReadStore) (blockSize : Nat)
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hsame : blockOfClose blockSize leftClose =
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo store (witnessProgram blockSize) ⟨regs, 0, false⟩
          ⟨regsF, 7, true⟩ []
          (closeDispatchCats ++ [Category.registerWrite, Category.control]) ∧
      regsF dSame = 9 := by
  obtain ⟨hD, _hC, hS⟩ :=
    closeDispatchProgram_hosts blockSize witnessCrossArm witnessSameArm
  have hDisp : HostedAt (witnessProgram blockSize) 0
      (closeDispatch blockSize 6) := by
    simpa [witnessProgram, witnessCrossArm] using hD
  obtain ⟨regs', hrun, _hc, _hr, _hp⟩ :=
    closeDispatch_runsTo_same store hDisp regs leftClose rightClose
      hClose hRight hsame
  have hSame : HostedAt (witnessProgram blockSize) 6 witnessSameArm := by
    simpa [witnessProgram, witnessCrossArm] using hS
  have hf6 : (witnessProgram blockSize)[6]? = some (.const dSame 9) := by
    exact hSame 0 (by decide)
  have hf7 : (witnessProgram blockSize)[7]? = some Instr.halt := by
    exact hSame 1 (by decide)
  have s6 : RunsTo store (witnessProgram blockSize) ⟨regs', 6, false⟩
      ⟨regs'.write dSame 9, 7, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs', 6, false⟩) rfl hf6
  have s7 : RunsTo store (witnessProgram blockSize)
      ⟨regs'.write dSame 9, 7, false⟩
      ⟨regs'.write dSame 9, 7, true⟩ [] [Category.control] :=
    RunsTo.halt (s := ⟨regs'.write dSame 9, 7, false⟩) rfl hf7
  refine ⟨regs'.write dSame 9, ?_, ?_⟩
  · have := (hrun.trans s6).trans s7
    simpa using this
  · simp [RegFile.write, dSame]

/-- ANTI-VACUITY, CROSS-BLOCK DIRECTION.  On the SAME witness program the
machine falls through to the cross arm and halts there, leaving that arm's
marker `7` in `dSame`.  Together with `witnessProgram_runs_same` this
shows both dispatch outcomes are reachable on one real program. -/
theorem witnessProgram_runs_cross (store : ReadStore) (blockSize : Nat)
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross : blockOfClose blockSize leftClose ≠
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo store (witnessProgram blockSize) ⟨regs, 0, false⟩
          ⟨regsF, 5, true⟩ []
          (closeDispatchCats ++ [Category.registerWrite, Category.control]) ∧
      regsF dSame = 7 := by
  obtain ⟨hD, hC, _hS⟩ :=
    closeDispatchProgram_hosts blockSize witnessCrossArm witnessSameArm
  have hDisp : HostedAt (witnessProgram blockSize) 0
      (closeDispatch blockSize 6) := by
    simpa [witnessProgram, witnessCrossArm] using hD
  obtain ⟨regs', hrun, _hc, _hr, _hp⟩ :=
    closeDispatch_runsTo_cross store hDisp regs leftClose rightClose
      hClose hRight hcross
  have hCross : HostedAt (witnessProgram blockSize) 4 witnessCrossArm := by
    simpa [witnessProgram] using hC
  have hf4 : (witnessProgram blockSize)[4]? = some (.const dSame 7) := by
    exact hCross 0 (by decide)
  have hf5 : (witnessProgram blockSize)[5]? = some Instr.halt := by
    exact hCross 1 (by decide)
  have s4 : RunsTo store (witnessProgram blockSize) ⟨regs', 4, false⟩
      ⟨regs'.write dSame 7, 5, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs', 4, false⟩) rfl hf4
  have s5 : RunsTo store (witnessProgram blockSize)
      ⟨regs'.write dSame 7, 5, false⟩
      ⟨regs'.write dSame 7, 5, true⟩ [] [Category.control] :=
    RunsTo.halt (s := ⟨regs'.write dSame 7, 5, false⟩) rfl hf5
  refine ⟨regs'.write dSame 7, ?_, ?_⟩
  · have := (hrun.trans s4).trans s5
    simpa using this
  · simp [RegFile.write, dSame]

/-! ## THE CROSS ARM HAS NO TERMINATOR: a latent fall-through

RECORDED BECAUSE NOTHING IN THE TREE RECORDED IT.

`crossBlockArmProgramAt_runsTo` (`E1CrossBlockArm.lean`) exits with
`halted = false` at `A + 370 + interior.length`, and
`crossBlockArmProgramAt_length` (`E1CrossBlockArm.lean:809`) is exactly
`370 + interior.length`.  `closeDispatchProgram` hosts the cross arm at
`4` and the same-block arm at `4 + crossArm.length`.  Instantiating the
first at `A = 4` makes the cross arm's exit address

    4 + 370 + interior.length  =  4 + crossArm.length

which IS the same-block arm's base.  A real cross arm would therefore run
off its own end into the same-block leg and execute all 173 of its
instructions on the wrong data.

Nothing caught this because `witnessCrossArm` ends in `.halt` -- the
witness composition works precisely because the witness does the thing the
real arm does not.

The two sections below (a) exhibit the fall-through BY EXECUTION and (b)
supply the terminator that fixes it.  Both keep `closeDispatchProgram` and
`sameBlockDispatchProgram_runsTo` untouched and parametric: the terminator
is appended to the `crossArm` ARGUMENT, not built into the layout.
-/

/-- A cross arm with NO terminator.  Identical to `witnessCrossArm` except
that its second instruction is an ordinary register write instead of
`.halt`, so it models the real arm's exit condition (`halted = false` at
its own end) rather than the witness's. -/
def unterminatedCrossArm : List Instr := [ .const dSame 7, .const dLB 0 ]

/-- The same two-arm layout, hosting the unterminated cross arm. -/
def fallThroughProgram (blockSize : Nat) : List Instr :=
  closeDispatchProgram blockSize unterminatedCrossArm witnessSameArm

@[simp] theorem fallThroughProgram_length (blockSize : Nat) :
    (fallThroughProgram blockSize).length = 8 := by
  simp [fallThroughProgram, closeDispatchProgram, unterminatedCrossArm,
    witnessSameArm]

/--
THE DISCRIMINATOR.  On a query whose endpoints are in DIFFERENT blocks --
so the dispatch correctly declines to branch and correctly enters the
cross arm -- the unterminated layout runs off the cross arm's end, EXECUTES
THE SAME-BLOCK ARM, and halts carrying the same-block marker `9`.

Compare `witnessProgram_runs_cross`, which is the identical layout with a
terminated cross arm and which halts at `5` carrying the cross marker `7`.
The only difference between the two programs is one instruction.

This is the right-shape/wrong-content class at the PROGRAM LAYOUT level:
the dispatch is correct, the branch is correct, the arm is correct, and the
answer is still the other arm's.
-/
theorem unterminatedCrossArm_falls_through (store : ReadStore)
    (blockSize : Nat) (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross : blockOfClose blockSize leftClose ≠
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo store (fallThroughProgram blockSize) ⟨regs, 0, false⟩
          ⟨regsF, 7, true⟩ []
          (closeDispatchCats ++
            [Category.registerWrite, Category.registerWrite,
              Category.registerWrite, Category.control]) ∧
      regsF dSame = 9 := by
  obtain ⟨hD, hC, hS⟩ :=
    closeDispatchProgram_hosts blockSize unterminatedCrossArm witnessSameArm
  have hDisp : HostedAt (fallThroughProgram blockSize) 0
      (closeDispatch blockSize 6) := by
    simpa [fallThroughProgram, unterminatedCrossArm] using hD
  obtain ⟨regs', hrun, _hc, _hr, _hp⟩ :=
    closeDispatch_runsTo_cross store hDisp regs leftClose rightClose
      hClose hRight hcross
  have hCross : HostedAt (fallThroughProgram blockSize) 4
      unterminatedCrossArm := by
    simpa [fallThroughProgram] using hC
  have hSame : HostedAt (fallThroughProgram blockSize) 6 witnessSameArm := by
    simpa [fallThroughProgram, unterminatedCrossArm] using hS
  have hf4 : (fallThroughProgram blockSize)[4]? = some (.const dSame 7) :=
    hCross 0 (by decide)
  have hf5 : (fallThroughProgram blockSize)[5]? = some (.const dLB 0) :=
    hCross 1 (by decide)
  have hf6 : (fallThroughProgram blockSize)[6]? = some (.const dSame 9) :=
    hSame 0 (by decide)
  have hf7 : (fallThroughProgram blockSize)[7]? = some Instr.halt :=
    hSame 1 (by decide)
  have s4 : RunsTo store (fallThroughProgram blockSize) ⟨regs', 4, false⟩
      ⟨regs'.write dSame 7, 5, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs', 4, false⟩) rfl hf4
  have s5 : RunsTo store (fallThroughProgram blockSize)
      ⟨regs'.write dSame 7, 5, false⟩
      ⟨(regs'.write dSame 7).write dLB 0, 6, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs'.write dSame 7, 5, false⟩) rfl hf5
  have s6 : RunsTo store (fallThroughProgram blockSize)
      ⟨(regs'.write dSame 7).write dLB 0, 6, false⟩
      ⟨((regs'.write dSame 7).write dLB 0).write dSame 9, 7, false⟩ []
      [Category.registerWrite] :=
    RunsTo.const (s := ⟨(regs'.write dSame 7).write dLB 0, 6, false⟩) rfl hf6
  have s7 : RunsTo store (fallThroughProgram blockSize)
      ⟨((regs'.write dSame 7).write dLB 0).write dSame 9, 7, false⟩
      ⟨((regs'.write dSame 7).write dLB 0).write dSame 9, 7, true⟩ []
      [Category.control] :=
    RunsTo.halt
      (s := ⟨((regs'.write dSame 7).write dLB 0).write dSame 9, 7, false⟩)
      rfl hf7
  refine ⟨((regs'.write dSame 7).write dLB 0).write dSame 9, ?_, ?_⟩
  · have := ((hrun.trans s4).trans s5).trans (s6.trans s7)
    simpa using this
  · simp [RegFile.write, dSame]

/-! ### The non-entailments

Which checks CANNOT tell the two layouts apart.  Recorded so the boundary
is exact rather than implied, in the style of `spanNoneArm_discriminates`
(`E1InteriorSpanBlock.lean:540`).
-/

/--
THE NON-ENTAILMENTS, carried by the two REAL runs rather than by identities
on literals.  On one and the same cross-block query, the defective layout
and the terminated one BOTH halt (`halted = true` in each final state) and
BOTH produce an EMPTY receipt.  So neither the halt flag, nor any receipt
comparison, nor any read COUNT can separate them; both facts are readable
directly off this statement's type.

What does separate them is the final value -- `dSame` is `9`, the
SAME-BLOCK marker, on the defective layout and `7`, the cross marker, on
the terminated one -- and the category log
(`unterminatedCrossArm_catLogs_differ`).
-/
theorem unterminatedCrossArm_nonEntailments (store : ReadStore)
    (blockSize : Nat) (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross : blockOfClose blockSize leftClose ≠
      blockOfClose blockSize rightClose) :
    (∃ regsF : RegFile,
        RunsTo store (fallThroughProgram blockSize) ⟨regs, 0, false⟩
            ⟨regsF, 7, true⟩ []
            (closeDispatchCats ++
              [Category.registerWrite, Category.registerWrite,
                Category.registerWrite, Category.control]) ∧
          regsF dSame = 9) ∧
      (∃ regsF : RegFile,
        RunsTo store (witnessProgram blockSize) ⟨regs, 0, false⟩
            ⟨regsF, 5, true⟩ []
            (closeDispatchCats ++
              [Category.registerWrite, Category.control]) ∧
          regsF dSame = 7) :=
  ⟨unterminatedCrossArm_falls_through store blockSize regs leftClose
      rightClose hClose hRight hcross,
    witnessProgram_runs_cross store blockSize regs leftClose rightClose
      hClose hRight hcross⟩

/-- The category logs DO differ -- the fall-through executes two extra
instructions -- so a positional category comparison catches this one.
Stated because the honest boundary is "value and category log catch it,
receipt and halt-flag do not". -/
theorem unterminatedCrossArm_catLogs_differ :
    closeDispatchCats ++
        [Category.registerWrite, Category.registerWrite,
          Category.registerWrite, Category.control] ≠
      closeDispatchCats ++ [Category.registerWrite, Category.control] := by
  simp [closeDispatchCats]

/-! ## THE TERMINATOR

The machine has no unconditional jump, so one is synthesised from a pinned
nonzero constant and a conditional branch on it.  `dSame` is the dispatch's
own scratch (`CloseDispatchUntouched`), dead once the branch has been
resolved, so the terminator clobbers nothing live.
-/

/-- Two-instruction unconditional jump to `target`. -/
def jumpTo (scratch target : Nat) : List Instr :=
  [ .const scratch 1, .brNZ scratch target ]

@[simp] theorem jumpTo_length (scratch target : Nat) :
    (jumpTo scratch target).length = 2 := rfl

/-- The synthesised jump really is unconditional: it transfers control to
`target` from ANY entry register file. -/
theorem jumpTo_runsTo (store : ReadStore) {program : E1Machine.Program}
    {A scratch target : Nat}
    (hHost : HostedAt program A (jumpTo scratch target)) (regs : RegFile) :
    RunsTo store program ⟨regs, A, false⟩
      ⟨regs.write scratch 1, target, false⟩ []
      [Category.registerWrite, Category.branch] := by
  have hf0 : program[A]? = some (.const scratch 1) := by
    simpa using hHost 0 (by simp [jumpTo])
  have hf1 : program[A + 1]? = some (.brNZ scratch target) := by
    simpa using hHost 1 (by simp [jumpTo])
  have s0 : RunsTo store program ⟨regs, A, false⟩
      ⟨regs.write scratch 1, A + 1, false⟩ [] [Category.registerWrite] :=
    RunsTo.const (s := ⟨regs, A, false⟩) rfl hf0
  have hcond : (regs.write scratch 1) scratch ≠ 0 := by
    simp [RegFile.write]
  have s1 : RunsTo store program ⟨regs.write scratch 1, A + 1, false⟩
      ⟨regs.write scratch 1, target, false⟩ [] [Category.branch] :=
    RunsTo.brNZ_taken (s := ⟨regs.write scratch 1, A + 1, false⟩) rfl hf1
      hcond
  simpa using s0.trans s1

/-- THE FIX.  A cross arm suffixed with a jump past the same-block arm, so
the two dispatch arms CONVERGE at the layout's exit instead of the cross
arm falling into the same-block leg.

Appending to the `crossArm` argument is what keeps `closeDispatchProgram`
and `sameBlockDispatchProgram_runsTo` parametric and unchanged. -/
def crossArmTerminated (crossArm : List Instr) (exit : Nat) : List Instr :=
  crossArm ++ jumpTo dSame exit

@[simp] theorem crossArmTerminated_length (crossArm : List Instr)
    (exit : Nat) :
    (crossArmTerminated crossArm exit).length = crossArm.length + 2 := by
  simp [crossArmTerminated]

/-- The exit address the terminator must target: past the dispatch, the
terminated cross arm, and the same-block arm.  Written as a function of
the layout's own lengths so it cannot drift from them. -/
def closeDispatchExit (crossArm sameArm : List Instr) : Nat :=
  4 + (crossArm.length + 2) + sameArm.length

/--
CONVERGENCE, BY EXECUTION.  With the terminator in place the cross
direction reaches the layout's exit -- PAST the same-block arm -- instead
of falling into it.  The stub cross arm's marker `7` survives, so the
answer is the cross arm's.

This is `unterminatedCrossArm_falls_through`'s counterpart on the repaired
layout: same dispatch, same arms, one appended terminator, and the
same-block arm is no longer reached.
-/
theorem crossArmTerminated_converges (store : ReadStore) (blockSize : Nat)
    (regs : RegFile) (leftClose rightClose : Nat)
    (hClose : regs fClose = leftClose) (hRight : regs fRight = rightClose)
    (hcross : blockOfClose blockSize leftClose ≠
      blockOfClose blockSize rightClose) :
    ∃ regsF : RegFile,
      RunsTo store
          (closeDispatchProgram blockSize
            (crossArmTerminated unterminatedCrossArm
              (closeDispatchExit unterminatedCrossArm witnessSameArm))
            witnessSameArm)
          ⟨regs, 0, false⟩ ⟨regsF, 10, false⟩ []
          (closeDispatchCats ++
            [Category.registerWrite, Category.registerWrite,
              Category.registerWrite, Category.branch]) ∧
      regsF dSame = 1 := by
  obtain ⟨hD, hC, _hS⟩ :=
    closeDispatchProgram_hosts blockSize
      (crossArmTerminated unterminatedCrossArm
        (closeDispatchExit unterminatedCrossArm witnessSameArm))
      witnessSameArm
  have hDisp : HostedAt
      (closeDispatchProgram blockSize
        (crossArmTerminated unterminatedCrossArm
          (closeDispatchExit unterminatedCrossArm witnessSameArm))
        witnessSameArm) 0 (closeDispatch blockSize 8) := by
    simpa [crossArmTerminated, unterminatedCrossArm, jumpTo] using hD
  obtain ⟨regs', hrun, _hc, _hr, _hp⟩ :=
    closeDispatch_runsTo_cross store hDisp regs leftClose rightClose
      hClose hRight hcross
  have hArm := hC
  have hf4 : (closeDispatchProgram blockSize
      (crossArmTerminated unterminatedCrossArm
        (closeDispatchExit unterminatedCrossArm witnessSameArm))
      witnessSameArm)[4]? = some (.const dSame 7) := by
    simpa using hArm 0 (by decide)
  have hf5 : (closeDispatchProgram blockSize
      (crossArmTerminated unterminatedCrossArm
        (closeDispatchExit unterminatedCrossArm witnessSameArm))
      witnessSameArm)[5]? = some (.const dLB 0) := by
    simpa using hArm 1 (by decide)
  have hf6 : (closeDispatchProgram blockSize
      (crossArmTerminated unterminatedCrossArm
        (closeDispatchExit unterminatedCrossArm witnessSameArm))
      witnessSameArm)[6]? = some (.const dSame 1) := by
    simpa [crossArmTerminated, unterminatedCrossArm, jumpTo] using
      hArm 2 (by decide)
  have hf7 : (closeDispatchProgram blockSize
      (crossArmTerminated unterminatedCrossArm
        (closeDispatchExit unterminatedCrossArm witnessSameArm))
      witnessSameArm)[7]? = some (.brNZ dSame 10) := by
    simpa [crossArmTerminated, unterminatedCrossArm, jumpTo,
      closeDispatchExit, witnessSameArm] using hArm 3 (by decide)
  have s4 := RunsTo.const (store := store) (s := ⟨regs', 4, false⟩) rfl hf4
  have s5 := RunsTo.const (store := store)
    (s := ⟨regs'.write dSame 7, 5, false⟩) rfl hf5
  have s6 := RunsTo.const (store := store)
    (s := ⟨(regs'.write dSame 7).write dLB 0, 6, false⟩) rfl hf6
  have hcond : (((regs'.write dSame 7).write dLB 0).write dSame 1) dSame
      ≠ 0 := by
    simp [RegFile.write]
  have s7 := RunsTo.brNZ_taken (store := store)
    (s := ⟨((regs'.write dSame 7).write dLB 0).write dSame 1, 7, false⟩)
    rfl hf7 hcond
  refine ⟨((regs'.write dSame 7).write dLB 0).write dSame 1, ?_, ?_⟩
  · have := ((hrun.trans s4).trans s5).trans (s6.trans s7)
    simpa using this
  · simp [RegFile.write, dSame]

end E1CloseDispatch
end WordRAM
end RMQ
