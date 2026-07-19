import RMQ.Core.WordRAM.E1InteriorSummaryGroup

/-! # E1 amended machine: the interior's MIN-CANDIDATE CONSUMER (M3d-21)

`canonicalRelativeRmmMachineMinCandidateComputation`
(`InteriorDirectory.lean:2300`) consumes the summary group's four cells:

    FlatStoreComputation.map
      (fun summary =>
        summary.map
          (bpRelativeSummaryMinCandidate layout.blockSize
            layout.blocksPerSuper block))
      (canonicalRelativeRmmMachineSummaryComputation shape block)

This module is the machine block that simulates it.  It performs NO
memory read: the four reads belong to the summary group, and the route's
`map` contributes no trace event.  Its receipt is `[]`.

## WHY ALL FOUR PRESENCE TESTS ARE HERE, INCLUDING `maxRel`

`bpRelativeSummaryMinCandidate` (`RelativeSummaryCandidate.lean:15`,
under `EndpointFringe/PrefixRange/`) reads `summary.1`, `summary.2.1` and
`summary.2.2.2` only.  `maxRel` is `summary.2.2.1` and is NEVER READ.

It does not follow that the `maxRel` test may be dropped.  The summary's
own assembly (`InteriorDirectory.lean:2293-2296`) is

    match baseline, minRel, maxRel, argOffset with
    | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
    | _, _, _, _                         => none

so `maxRel = none` forces the whole summary to `none`, hence the
min-candidate to `none`.  `maxRel` is discarded by the FUNCTION and
load-bearing through the OPTION STRUCTURE.  A block that kept the
`maxRel` READ (satisfying the positional receipt, the read count and the
trace length) but ignored its VALUE would return `some` exactly where the
route returns `none` -- right shape, wrong content, invisible to every
aggregate check.

THE `none` ARM IS REACHABLE, NOT HYPOTHETICAL.
`FixedWidthNatTable.machineReadComputationAt`
(`SuccinctSpace/MachineChunkedTableProgram.lean:343`) reads
`[deadAddress]` when the index is out of range, and that decodes to
`none`.

The alternative -- proving `maxRel.entriesLen = minRel.entriesLen` and
collapsing the four tests to two -- is rejected on two grounds.  The
equality is evaluated equal at four sizes and proved nowhere in the tree,
so assuming it would be unsound; and even proved, it would make the
machine's control flow DIVERGE from the route's, where the unimpeachable
option is structural correspondence a reviewer can diff.  See
DD-20260719-015.

## The default is `none`, which is the route's catch-all arm

The block writes `none` into the output pair FIRST and then conditionally
skips the value computation.  That mirrors `| _, _, _, _ => none`: the
absent case is the fallthrough, not a branch destination, so the block
needs no unconditional jump and no always-nonzero register.

## The shift does not cancel, and the order of truncation is load-bearing

The saved cells are option-shifted (`0` = `none`, `v + 1` = `some v`, the
`geomRouteDecode` convention, `E1InteriorSummaryGroup.lean:651`), and the
output pair is `bestOfRegs` (`E1FringeFoldBlock.lean:114`), the same
shift on the value and a raw position.  With
`span := bpSuperblockSpan blockSize blocksPerSuper = blocksPerSuper * blockSize`
(`RelativeSummary.lean:82`) and
`blockStartOf blockSize block = block * blockSize`
(`BlockLocal.lean:868`), the route's pair is

    (baseline + minRel - span, blockStartOf blockSize block + argOffset)

and the machine must leave `value + 1` in `mMV` and `position` in `mMP`.
Both subtractions are Nat-truncated.  The block computes

    (cB + cMn) - (span + 2)     then     + 1

and NOT `(cB + cMn) - 1 - span + 1` in some other order: `a + k - (b + k)
= a - b` holds in `Nat` unconditionally, which is why the `+ 2` may be
folded into the constant, whereas adding the `+ 1` BEFORE the truncating
subtraction would give `(b + mn + 1) - span`, which differs from
`(b + mn - span) + 1` at every `span > b + mn`.  The `+ 1` is last.

## Register bank extension (min-candidate consumer, `105 .. 117`)

`100 .. 104` are the summary group's.  This block opens at `105` and the
next block opens at `118`.  Every register here satisfies
`ChunkFoldUntouched r := r < 89 \/ 99 < r`
(`E1InteriorChunkFold.lean:928`), so the scratch survives any later fold.
The outputs are `mMV` (`77`) and `mMP` (`78`) -- the interior interface
`crossBlockArmProgramAt_runsTo` names at `E1CrossBlockArm.lean:1184`.
-/

open RMQ
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

namespace RMQ
namespace WordRAM
namespace E1InteriorMinCandidate

open E1Machine
open RMQ.SuccinctClose
open E1FringeFoldBlock (bestOfRegs)
open E1CandMerge3 (mMV mMP)
open E1InteriorSummaryGroup (sBlock sBase sMin sMax sArg)
-- the group's own vocabulary, for the composite at the end of this module
open E1InteriorSummaryGroup (canonicalSummaryLayout summaryGroup
  summaryGroup_length geomEvents geomCats geomRouteDecode
  canonicalSummaryGroup_runsTo geomCell_baseline_eq_routeDecode
  geomCell_minRel_eq_routeDecode geomCell_maxRel_eq_routeDecode
  geomCell_argOffset_eq_routeDecode)

/-! ## Registers

Scratch only; the inputs are the summary group's `100 .. 104` and the
outputs are the arm's `mMV` / `mMP`. -/

/-- Constant `0`, the left operand of the four presence tests. -/
abbrev cZero : Nat := 105
/-- Presence flag for the baseline cell. -/
abbrev fB : Nat := 106
/-- Presence flag for the `minRel` cell. -/
abbrev fMn : Nat := 107
/-- Presence flag for the `maxRel` cell.  NOT optimisable away: see the
module header. -/
abbrev fMx : Nat := 108
/-- Presence flag for the `argOffset` cell. -/
abbrev fA : Nat := 109
/-- Sum of the four presence flags. -/
abbrev fSum : Nat := 110
/-- Constant `4`, the all-present threshold. -/
abbrev cFour : Nat := 111
/-- `1` exactly when NOT all four cells are present. -/
abbrev fNone : Nat := 112
/-- Value accumulator. -/
abbrev tV : Nat := 113
/-- Constant `span + 2`: the superblock span plus the two option shifts. -/
abbrev cSpan2 : Nat := 114
/-- Constant `1`, the output shift. -/
abbrev cOne : Nat := 115
/-- Position accumulator. -/
abbrev tP : Nat := 116
/-- The unshifted `argOffset`. -/
abbrev tA : Nat := 117

/-! ## The route's option structure, in the machine's terms -/

/-- A saved cell read back as the option it encodes: `0` is `none`, `v + 1`
is `some v`.  This is `geomRouteDecode`'s shift, inverted. -/
def cellOpt (c : Nat) : Option Nat :=
  if c = 0 then none else some (c - 1)

@[simp] theorem cellOpt_zero : cellOpt 0 = none := rfl

@[simp] theorem cellOpt_succ (v : Nat) : cellOpt (v + 1) = some v := by
  simp [cellOpt]

/--
The summary tuple the four saved cells encode, WRITTEN AS THE ROUTE
WRITES IT.  This is arm-for-arm `InteriorDirectory.lean:2293-2296` with
each route read replaced by the cell in the register that holds it; the
`mx` binder is present and unused on the left exactly as it is there.
-/
def summaryOfCells (cB cMn cMx cA : Nat) : Option (Nat × Nat × Nat × Nat) :=
  match cellOpt cB, cellOpt cMn, cellOpt cMx, cellOpt cA with
  | some b, some mn, some mx, some arg => some (b, mn, mx, arg)
  | _, _, _, _ => none

/-- All four cells present is exactly the summary being `some`. -/
theorem summaryOfCells_isSome (cB cMn cMx cA : Nat) :
    (summaryOfCells cB cMn cMx cA).isSome =
      (decide (cB ≠ 0) && decide (cMn ≠ 0) && decide (cMx ≠ 0) &&
        decide (cA ≠ 0)) := by
  cases cB <;> cases cMn <;> cases cMx <;> cases cA <;>
    simp [summaryOfCells]

/-- The summary is `some` exactly when all four cells are present, and its
payload is the four cells unshifted. -/
theorem summaryOfCells_eq_some {cB cMn cMx cA : Nat}
    (hB : 0 < cB) (hMn : 0 < cMn) (hMx : 0 < cMx) (hA : 0 < cA) :
    summaryOfCells cB cMn cMx cA = some (cB - 1, cMn - 1, cMx - 1, cA - 1) := by
  unfold summaryOfCells cellOpt
  rw [if_neg (by omega), if_neg (by omega), if_neg (by omega),
    if_neg (by omega)]

/-- ANY absent cell forces the summary to `none` -- INCLUDING `maxRel`,
whose value no consumer reads.  This is the fact that makes the `Q + 5`
presence test load-bearing rather than decorative. -/
theorem summaryOfCells_eq_none {cB cMn cMx cA : Nat}
    (h : ¬ (0 < cB ∧ 0 < cMn ∧ 0 < cMx ∧ 0 < cA)) :
    summaryOfCells cB cMn cMx cA = none := by
  cases cB <;> cases cMn <;> cases cMx <;> cases cA <;>
    simp_all [summaryOfCells]

/-- The `maxRel` test is not decorative: at an absent `maxRel` with the
other three cells present, the route's min-candidate is `none`.  A block
that dropped the `Q + 5` test would return `some` here. -/
theorem summaryOfCells_maxRel_absent (cB cMn cA : Nat) :
    summaryOfCells cB cMn 0 cA = none :=
  summaryOfCells_eq_none (by omega)

/-! ## The block -/

/--
THE MIN-CANDIDATE CONSUMER at base `Q` (21 instructions, exit `Q + 21`),
read-free.

`Q + 0 .. Q + 2` install the `none` default and the comparison zero.
`Q + 3 .. Q + 6` are the FOUR presence tests, one per summary field, in
the route's own field order.  `Q + 7 .. Q + 11` reduce them to a single
"not all present" flag, and `Q + 12` skips the value computation on it.
`Q + 13 .. Q + 20` are the value computation, reached only when all four
cells are present.
-/
def minCandidateBlock (blockSize blocksPerSuper Q : Nat) : List Instr :=
  [ .const mMV 0                                    -- Q+0   default: none
  , .const mMP 0                                    -- Q+1
  , .const cZero 0                                  -- Q+2
  , .natLt fB cZero sBase                           -- Q+3   baseline present?
  , .natLt fMn cZero sMin                           -- Q+4   minRel present?
  , .natLt fMx cZero sMax                           -- Q+5   maxRel present?
  , .natLt fA cZero sArg                            -- Q+6   argOffset present?
  , .add fSum fB fMn                                -- Q+7
  , .add fSum fSum fMx                              -- Q+8
  , .add fSum fSum fA                               -- Q+9
  , .const cFour 4                                  -- Q+10
  , .natLt fNone fSum cFour                         -- Q+11  some cell absent?
  , .brNZ fNone (Q + 21)                            -- Q+12  -> keep none
  , .add tV sBase sMin                              -- Q+13  b + mn + 2
  , .const cSpan2 (blocksPerSuper * blockSize + 2)  -- Q+14
  , .sub tV tV cSpan2                               -- Q+15  b + mn - span
  , .const cOne 1                                   -- Q+16
  , .add mMV tV cOne                                -- Q+17  shift LAST
  , .mulConst tP sBlock blockSize                   -- Q+18  block * blockSize
  , .sub tA sArg cOne                               -- Q+19  argOffset
  , .add mMP tP tA ]                                -- Q+20

@[simp] theorem minCandidateBlock_length (blockSize blocksPerSuper Q : Nat) :
    (minCandidateBlock blockSize blocksPerSuper Q).length = 21 := rfl

/-- The block performs no memory read: the route's consumer rides a
`FlatStoreComputation.map`, which contributes no trace event. -/
theorem minCandidateBlock_readFree (blockSize blocksPerSuper Q : Nat) :
    ∀ instr ∈ minCandidateBlock blockSize blocksPerSuper Q,
      instr.category ≠ Category.memoryRead := by
  intro instr hinstr
  simp only [minCandidateBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h <;> subst h <;> simp [Instr.category]

/-! ## Category log

A FUNCTION of the route-side branch condition -- whether the summary is
`some` -- never a numeral. -/

/-- Categories charged before the skip branch, and by it.  Unconditional:
every presence test runs on every arm. -/
def minCandidatePrefixCats : List Category :=
  [ .registerWrite, .registerWrite, .registerWrite
  , .comparison, .comparison, .comparison, .comparison
  , .arithmetic, .arithmetic, .arithmetic
  , .registerWrite, .comparison, .branch ]

/-- Categories charged by the value computation, on the arm the route
selects. -/
def minCandidateValueCats : List Category :=
  [ .arithmetic, .registerWrite, .arithmetic, .registerWrite
  , .arithmetic, .arithmetic, .arithmetic, .arithmetic ]

/-- Category log of the whole block on the arm the route selects. -/
def minCandidateCats (allPresent : Bool) : List Category :=
  minCandidatePrefixCats ++ (if allPresent then minCandidateValueCats else [])

@[simp] theorem minCandidateCats_length_true :
    (minCandidateCats true).length = 21 := rfl

@[simp] theorem minCandidateCats_length_false :
    (minCandidateCats false).length = 13 := rfl

/-! ## Width certificate

Constructor-exhaustive, no wildcard arm.  The block carries no divisor,
so no positivity side condition arises.  The two shape-dependent
constants -- the folded span and the block size -- carry their own
hypotheses rather than being bounded by a numeral. -/

theorem minCandidateBlock_fits (w blockSize blocksPerSuper Q : Nat)
    (hQ : Q + 21 < 2 ^ w) (hreg : 117 < 2 ^ w)
    (hspan : blocksPerSuper * blockSize + 2 < 2 ^ w)
    (hsize : blockSize < 2 ^ w) :
    ∀ instr ∈ minCandidateBlock blockSize blocksPerSuper Q,
      Instr.FieldsFit w instr := by
  intro instr hinstr
  have h0 : (0 : Nat) < 2 ^ w := by omega
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h4 : (4 : Nat) < 2 ^ w := by omega
  have h77 : (77 : Nat) < 2 ^ w := by omega
  have h78 : (78 : Nat) < 2 ^ w := by omega
  have h100 : (100 : Nat) < 2 ^ w := by omega
  have h101 : (101 : Nat) < 2 ^ w := by omega
  have h102 : (102 : Nat) < 2 ^ w := by omega
  have h103 : (103 : Nat) < 2 ^ w := by omega
  have h104 : (104 : Nat) < 2 ^ w := by omega
  have h105 : (105 : Nat) < 2 ^ w := by omega
  have h106 : (106 : Nat) < 2 ^ w := by omega
  have h107 : (107 : Nat) < 2 ^ w := by omega
  have h108 : (108 : Nat) < 2 ^ w := by omega
  have h109 : (109 : Nat) < 2 ^ w := by omega
  have h110 : (110 : Nat) < 2 ^ w := by omega
  have h111 : (111 : Nat) < 2 ^ w := by omega
  have h112 : (112 : Nat) < 2 ^ w := by omega
  have h113 : (113 : Nat) < 2 ^ w := by omega
  have h114 : (114 : Nat) < 2 ^ w := by omega
  have h115 : (115 : Nat) < 2 ^ w := by omega
  have h116 : (116 : Nat) < 2 ^ w := by omega
  have h117 : (117 : Nat) < 2 ^ w := hreg
  simp only [minCandidateBlock, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h | h | h | h | h | h <;> subst h
  · exact ⟨h77, h0⟩
  · exact ⟨h78, h0⟩
  · exact ⟨h105, h0⟩
  · exact ⟨h106, h105, h101⟩
  · exact ⟨h107, h105, h102⟩
  · exact ⟨h108, h105, h103⟩
  · exact ⟨h109, h105, h104⟩
  · exact ⟨h110, h106, h107⟩
  · exact ⟨h110, h110, h108⟩
  · exact ⟨h110, h110, h109⟩
  · exact ⟨h111, h4⟩
  · exact ⟨h112, h110, h111⟩
  · exact ⟨h112, hQ⟩
  · exact ⟨h113, h101, h102⟩
  · exact ⟨h114, hspan⟩
  · exact ⟨h113, h113, h114⟩
  · exact ⟨h115, h1⟩
  · exact ⟨h77, h113, h115⟩
  · exact ⟨h116, h100, hsize⟩
  · exact ⟨h117, h104, h115⟩
  · exact ⟨h78, h116, h117⟩

/-! ## Exact simulation -/

/-- What the block leaves alone: everything but the output pair and the
scratch bank `105 .. 117`.  In particular the summary group's inputs
`100 .. 104` all survive, so the block may be composed after the group
without re-establishing them. -/
abbrev MinCandUntouched (r : Nat) : Prop :=
  r ≠ mMV ∧ r ≠ mMP ∧ (r < 105 ∨ 117 < r)

/--
EXACT SIMULATION OF THE MIN-CANDIDATE CONSUMER.

The receipt is `[]` -- the block reads nothing.  The result is stated as
the ROUTE'S OWN EXPRESSION, `summary.map (bpRelativeSummaryMinCandidate
blockSize blocksPerSuper block)`, with the route's four reads replaced by
the four cells the summary group left in `sBase`, `sMin`, `sMax`, `sArg`.

The `maxRel` cell `cMx` appears on BOTH sides: on the right it gates
`summaryOfCells`, and on the left it is tested at `Q + 5`.  It is not an
argument the statement could drop -- at `cMx = 0` with the other three
present, the right-hand side is `none`, and only the `Q + 5` test makes
the left-hand side `none` too.
-/
theorem minCandidateBlock_runsTo
    (store : ReadStore) {program : E1Machine.Program}
    {blockSize blocksPerSuper Q block cB cMn cMx cA : Nat} {regs : RegFile}
    (hHost : HostedAt program Q (minCandidateBlock blockSize blocksPerSuper Q))
    (hBlock : regs sBlock = block)
    (hBase : regs sBase = cB) (hMin : regs sMin = cMn)
    (hMax : regs sMax = cMx) (hArg : regs sArg = cA) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, Q, false⟩ ⟨regs', Q + 21, false⟩ []
          (minCandidateCats (summaryOfCells cB cMn cMx cA).isSome) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          (summaryOfCells cB cMn cMx cA).map
            (bpRelativeSummaryMinCandidate blockSize blocksPerSuper block) ∧
        (∀ r, MinCandUntouched r → regs' r = regs r) := by
  -- fetch facts for the twenty-one positions
  have hf : ∀ (k m : Nat) (instr : Instr), k < 21 →
      (minCandidateBlock blockSize blocksPerSuper Q)[k]? = some instr →
      Q + k = m → program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hHost k hk, hget]
  have h0 : program[Q]? = some (.const mMV 0) := hf 0 Q _ (by omega) rfl (by omega)
  have h1 : program[Q + 1]? = some (.const mMP 0) := hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[Q + 2]? = some (.const cZero 0) := hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[Q + 3]? = some (.natLt fB cZero sBase) := hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[Q + 4]? = some (.natLt fMn cZero sMin) := hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[Q + 5]? = some (.natLt fMx cZero sMax) := hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[Q + 6]? = some (.natLt fA cZero sArg) := hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[Q + 7]? = some (.add fSum fB fMn) := hf 7 _ _ (by omega) rfl (by omega)
  have h8 : program[Q + 8]? = some (.add fSum fSum fMx) := hf 8 _ _ (by omega) rfl (by omega)
  have h9 : program[Q + 9]? = some (.add fSum fSum fA) := hf 9 _ _ (by omega) rfl (by omega)
  have h10 : program[Q + 10]? = some (.const cFour 4) := hf 10 _ _ (by omega) rfl (by omega)
  have h11 : program[Q + 11]? = some (.natLt fNone fSum cFour) := hf 11 _ _ (by omega) rfl (by omega)
  have h12 : program[Q + 12]? = some (.brNZ fNone (Q + 21)) := hf 12 _ _ (by omega) rfl (by omega)
  have h13 : program[Q + 13]? = some (.add tV sBase sMin) := hf 13 _ _ (by omega) rfl (by omega)
  have h14 : program[Q + 14]? =
      some (.const cSpan2 (blocksPerSuper * blockSize + 2)) :=
    hf 14 _ _ (by omega) rfl (by omega)
  have h15 : program[Q + 15]? = some (.sub tV tV cSpan2) := hf 15 _ _ (by omega) rfl (by omega)
  have h16 : program[Q + 16]? = some (.const cOne 1) := hf 16 _ _ (by omega) rfl (by omega)
  have h17 : program[Q + 17]? = some (.add mMV tV cOne) := hf 17 _ _ (by omega) rfl (by omega)
  have h18 : program[Q + 18]? = some (.mulConst tP sBlock blockSize) := hf 18 _ _ (by omega) rfl (by omega)
  have h19 : program[Q + 19]? = some (.sub tA sArg cOne) := hf 19 _ _ (by omega) rfl (by omega)
  have h20 : program[Q + 20]? = some (.add mMP tP tA) := hf 20 _ _ (by omega) rfl (by omega)
  -- the presence flags, as the semantics computes them
  obtain ⟨bB, hbB⟩ : ∃ z : Nat, z = if 0 < cB then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨bMn, hbMn⟩ : ∃ z : Nat, z = if 0 < cMn then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨bMx, hbMx⟩ : ∃ z : Nat, z = if 0 < cMx then 1 else 0 := ⟨_, rfl⟩
  obtain ⟨bA, hbA⟩ : ∃ z : Nat, z = if 0 < cA then 1 else 0 := ⟨_, rfl⟩
  have hb1 : bB ≤ 1 := by rw [hbB]; split <;> omega
  have hb2 : bMn ≤ 1 := by rw [hbMn]; split <;> omega
  have hb3 : bMx ≤ 1 := by rw [hbMx]; split <;> omega
  have hb4 : bA ≤ 1 := by rw [hbA]; split <;> omega
  -- the deterministic prefix, Q .. Q+11
  obtain ⟨r0, hr0⟩ : ∃ z : RegFile, z = regs.write mMV 0 := ⟨_, rfl⟩
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = r0.write mMP 0 := ⟨_, rfl⟩
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write cZero 0 := ⟨_, rfl⟩
  obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write fB bB := ⟨_, rfl⟩
  obtain ⟨r4, hr4⟩ : ∃ z : RegFile, z = r3.write fMn bMn := ⟨_, rfl⟩
  obtain ⟨r5, hr5⟩ : ∃ z : RegFile, z = r4.write fMx bMx := ⟨_, rfl⟩
  obtain ⟨r6, hr6⟩ : ∃ z : RegFile, z = r5.write fA bA := ⟨_, rfl⟩
  obtain ⟨r7, hr7⟩ : ∃ z : RegFile, z = r6.write fSum (bB + bMn) := ⟨_, rfl⟩
  obtain ⟨r8, hr8⟩ : ∃ z : RegFile, z = r7.write fSum (bB + bMn + bMx) := ⟨_, rfl⟩
  obtain ⟨r9, hr9⟩ : ∃ z : RegFile, z = r8.write fSum (bB + bMn + bMx + bA) := ⟨_, rfl⟩
  obtain ⟨r10, hr10⟩ : ∃ z : RegFile, z = r9.write cFour 4 := ⟨_, rfl⟩
  obtain ⟨r11, hr11⟩ : ∃ z : RegFile,
      z = r10.write fNone (if bB + bMn + bMx + bA < 4 then 1 else 0) := ⟨_, rfl⟩
  -- register lookups along the prefix
  have e2Z : r2 cZero = 0 := by rw [hr2, RegFile.write_same]
  have e2B : r2 sBase = cB := by
    rw [hr2, RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0,
      RegFile.write_other _ _ (by decide), hBase]
  have e3Z : r3 cZero = 0 := by rw [hr3, RegFile.write_other _ _ (by decide), e2Z]
  have e3M : r3 sMin = cMn := by
    rw [hr3, RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0,
      RegFile.write_other _ _ (by decide), hMin]
  have e4Z : r4 cZero = 0 := by rw [hr4, RegFile.write_other _ _ (by decide), e3Z]
  have e4X : r4 sMax = cMx := by
    rw [hr4, RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0,
      RegFile.write_other _ _ (by decide), hMax]
  have e5Z : r5 cZero = 0 := by rw [hr5, RegFile.write_other _ _ (by decide), e4Z]
  have e5A : r5 sArg = cA := by
    rw [hr5, RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0,
      RegFile.write_other _ _ (by decide), hArg]
  have e6B : r6 fB = bB := by
    rw [hr6, RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3, RegFile.write_same]
  have e6M : r6 fMn = bMn := by
    rw [hr6, RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4, RegFile.write_same]
  have e7S : r7 fSum = bB + bMn := by rw [hr7, RegFile.write_same]
  have e7X : r7 fMx = bMx := by
    rw [hr7, RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5, RegFile.write_same]
  have e8S : r8 fSum = bB + bMn + bMx := by rw [hr8, RegFile.write_same]
  have e8A : r8 fA = bA := by
    rw [hr8, RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6, RegFile.write_same]
  have e9S : r9 fSum = bB + bMn + bMx + bA := by rw [hr9, RegFile.write_same]
  have e10S : r10 fSum = bB + bMn + bMx + bA := by
    rw [hr10, RegFile.write_other _ _ (by decide), e9S]
  have e10F : r10 cFour = 4 := by rw [hr10, RegFile.write_same]
  have e11N : r11 fNone = (if bB + bMn + bMx + bA < 4 then 1 else 0) := by
    rw [hr11, RegFile.write_same]
  -- the prefix run
  have p0 : RunsTo store program ⟨regs, Q, false⟩ ⟨r0, Q + 1, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store) (s := (⟨regs, Q, false⟩ : State)) rfl h0
    simpa [hr0] using h
  have p1 : RunsTo store program ⟨r0, Q + 1, false⟩ ⟨r1, Q + 2, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store) (s := (⟨r0, Q + 1, false⟩ : State)) rfl h1
    simpa [hr1] using h
  have p2 : RunsTo store program ⟨r1, Q + 2, false⟩ ⟨r2, Q + 3, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store) (s := (⟨r1, Q + 2, false⟩ : State)) rfl h2
    simpa [hr2] using h
  have p3 : RunsTo store program ⟨r2, Q + 3, false⟩ ⟨r3, Q + 4, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store) (s := (⟨r2, Q + 3, false⟩ : State)) rfl h3
    simpa [hr3, e2Z, e2B, hbB] using h
  have p4 : RunsTo store program ⟨r3, Q + 4, false⟩ ⟨r4, Q + 5, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store) (s := (⟨r3, Q + 4, false⟩ : State)) rfl h4
    simpa [hr4, e3Z, e3M, hbMn] using h
  have p5 : RunsTo store program ⟨r4, Q + 5, false⟩ ⟨r5, Q + 6, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store) (s := (⟨r4, Q + 5, false⟩ : State)) rfl h5
    simpa [hr5, e4Z, e4X, hbMx] using h
  have p6 : RunsTo store program ⟨r5, Q + 6, false⟩ ⟨r6, Q + 7, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store) (s := (⟨r5, Q + 6, false⟩ : State)) rfl h6
    simpa [hr6, e5Z, e5A, hbA] using h
  have p7 : RunsTo store program ⟨r6, Q + 7, false⟩ ⟨r7, Q + 8, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add (store := store) (s := (⟨r6, Q + 7, false⟩ : State)) rfl h7
    simpa [hr7, e6B, e6M] using h
  have p8 : RunsTo store program ⟨r7, Q + 8, false⟩ ⟨r8, Q + 9, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add (store := store) (s := (⟨r7, Q + 8, false⟩ : State)) rfl h8
    simpa [hr8, e7S, e7X] using h
  have p9 : RunsTo store program ⟨r8, Q + 9, false⟩ ⟨r9, Q + 10, false⟩ []
      [Category.arithmetic] := by
    have h := RunsTo.add (store := store) (s := (⟨r8, Q + 9, false⟩ : State)) rfl h9
    simpa [hr9, e8S, e8A] using h
  have p10 : RunsTo store program ⟨r9, Q + 10, false⟩ ⟨r10, Q + 11, false⟩ []
      [Category.registerWrite] := by
    have h := RunsTo.const (store := store) (s := (⟨r9, Q + 10, false⟩ : State)) rfl h10
    simpa [hr10] using h
  have p11 : RunsTo store program ⟨r10, Q + 11, false⟩ ⟨r11, Q + 12, false⟩ []
      [Category.comparison] := by
    have h := RunsTo.natLt (store := store) (s := (⟨r10, Q + 11, false⟩ : State)) rfl h11
    simpa [hr11, e10S, e10F] using h
  have hprefix :
      RunsTo store program ⟨regs, Q, false⟩ ⟨r11, Q + 12, false⟩ []
        minCandidatePrefixCats.dropLast := by
    have h := ((((((((((p0.trans p1).trans p2).trans p3).trans p4).trans p5).trans
      p6).trans p7).trans p8).trans p9).trans p10).trans p11
    simpa [minCandidatePrefixCats] using h
  -- the block's inputs survive the prefix
  have e11B : r11 sBase = cB := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), e2B]
  have e11M : r11 sMin = cMn := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), e3M]
  have e11A : r11 sArg = cA := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), e5A]
  have e11K : r11 sBlock = block := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0,
      RegFile.write_other _ _ (by decide), hBlock]
  have e11V : r11 mMV = 0 := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1,
      RegFile.write_other _ _ (by decide), hr0, RegFile.write_same]
  have e11P : r11 mMP = 0 := by
    rw [hr11, RegFile.write_other _ _ (by decide), hr10,
      RegFile.write_other _ _ (by decide), hr9,
      RegFile.write_other _ _ (by decide), hr8,
      RegFile.write_other _ _ (by decide), hr7,
      RegFile.write_other _ _ (by decide), hr6,
      RegFile.write_other _ _ (by decide), hr5,
      RegFile.write_other _ _ (by decide), hr4,
      RegFile.write_other _ _ (by decide), hr3,
      RegFile.write_other _ _ (by decide), hr2,
      RegFile.write_other _ _ (by decide), hr1, RegFile.write_same]
  have hpres11 : ∀ r, MinCandUntouched r → r11 r = regs r := by
    intro r hr
    obtain ⟨hV, hP, hbank⟩ := hr
    rw [hr11, RegFile.write_other _ _ (show r ≠ 112 by omega), hr10,
      RegFile.write_other _ _ (show r ≠ 111 by omega), hr9,
      RegFile.write_other _ _ (show r ≠ 110 by omega), hr8,
      RegFile.write_other _ _ (show r ≠ 110 by omega), hr7,
      RegFile.write_other _ _ (show r ≠ 110 by omega), hr6,
      RegFile.write_other _ _ (show r ≠ 109 by omega), hr5,
      RegFile.write_other _ _ (show r ≠ 108 by omega), hr4,
      RegFile.write_other _ _ (show r ≠ 107 by omega), hr3,
      RegFile.write_other _ _ (show r ≠ 106 by omega), hr2,
      RegFile.write_other _ _ (show r ≠ 105 by omega), hr1,
      RegFile.write_other _ _ hP, hr0, RegFile.write_other _ _ hV]
  -- THE ROUTE-SIDE BRANCH: is the summary present?
  by_cases hall : 0 < cB ∧ 0 < cMn ∧ 0 < cMx ∧ 0 < cA
  · -- all four cells present: the summary is `some`, the value runs
    obtain ⟨hcB, hcMn, hcMx, hcA⟩ := hall
    have hsum : bB + bMn + bMx + bA = 4 := by
      rw [hbB, hbMn, hbMx, hbA]
      rw [if_pos hcB, if_pos hcMn, if_pos hcMx, if_pos hcA]
    have hnot : r11 fNone = 0 := by rw [e11N, hsum]; exact if_neg (by omega)
    have p12 : RunsTo store program ⟨r11, Q + 12, false⟩ ⟨r11, Q + 13, false⟩ []
        [Category.branch] := by
      have h := RunsTo.brNZ (store := store)
        (s := (⟨r11, Q + 12, false⟩ : State)) rfl h12
      simpa [hnot] using h
    obtain ⟨r12, hr12⟩ : ∃ z : RegFile, z = r11.write tV (cB + cMn) := ⟨_, rfl⟩
    obtain ⟨r13, hr13⟩ : ∃ z : RegFile,
        z = r12.write cSpan2 (blocksPerSuper * blockSize + 2) := ⟨_, rfl⟩
    obtain ⟨r14, hr14⟩ : ∃ z : RegFile,
        z = r13.write tV (cB + cMn - (blocksPerSuper * blockSize + 2)) := ⟨_, rfl⟩
    obtain ⟨r15, hr15⟩ : ∃ z : RegFile, z = r14.write cOne 1 := ⟨_, rfl⟩
    obtain ⟨r16, hr16⟩ : ∃ z : RegFile,
        z = r15.write mMV (cB + cMn - (blocksPerSuper * blockSize + 2) + 1) := ⟨_, rfl⟩
    obtain ⟨r17, hr17⟩ : ∃ z : RegFile, z = r16.write tP (block * blockSize) := ⟨_, rfl⟩
    obtain ⟨r18, hr18⟩ : ∃ z : RegFile, z = r17.write tA (cA - 1) := ⟨_, rfl⟩
    obtain ⟨r19, hr19⟩ : ∃ z : RegFile,
        z = r18.write mMP (block * blockSize + (cA - 1)) := ⟨_, rfl⟩
    have f13V : r13 tV = cB + cMn := by
      rw [hr13, RegFile.write_other _ _ (by decide), hr12, RegFile.write_same]
    have f13S : r13 cSpan2 = blocksPerSuper * blockSize + 2 := by
      rw [hr13, RegFile.write_same]
    have f15V : r15 tV = cB + cMn - (blocksPerSuper * blockSize + 2) := by
      rw [hr15, RegFile.write_other _ _ (by decide), hr14, RegFile.write_same]
    have f15O : r15 cOne = 1 := by rw [hr15, RegFile.write_same]
    have f16K : r16 sBlock = block := by
      rw [hr16, RegFile.write_other _ _ (by decide), hr15,
        RegFile.write_other _ _ (by decide), hr14,
        RegFile.write_other _ _ (by decide), hr13,
        RegFile.write_other _ _ (by decide), hr12,
        RegFile.write_other _ _ (by decide), e11K]
    have f17A : r17 sArg = cA := by
      rw [hr17, RegFile.write_other _ _ (by decide), hr16,
        RegFile.write_other _ _ (by decide), hr15,
        RegFile.write_other _ _ (by decide), hr14,
        RegFile.write_other _ _ (by decide), hr13,
        RegFile.write_other _ _ (by decide), hr12,
        RegFile.write_other _ _ (by decide), e11A]
    have f17O : r17 cOne = 1 := by
      rw [hr17, RegFile.write_other _ _ (by decide), hr16,
        RegFile.write_other _ _ (by decide), f15O]
    have f18P : r18 tP = block * blockSize := by
      rw [hr18, RegFile.write_other _ _ (by decide), hr17, RegFile.write_same]
    have f18A : r18 tA = cA - 1 := by rw [hr18, RegFile.write_same]
    have p13 : RunsTo store program ⟨r11, Q + 13, false⟩ ⟨r12, Q + 14, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.add (store := store) (s := (⟨r11, Q + 13, false⟩ : State)) rfl h13
      simpa [hr12, e11B, e11M] using h
    have p14 : RunsTo store program ⟨r12, Q + 14, false⟩ ⟨r13, Q + 15, false⟩ []
        [Category.registerWrite] := by
      have h := RunsTo.const (store := store) (s := (⟨r12, Q + 14, false⟩ : State)) rfl h14
      simpa [hr13] using h
    have p15 : RunsTo store program ⟨r13, Q + 15, false⟩ ⟨r14, Q + 16, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.sub (store := store) (s := (⟨r13, Q + 15, false⟩ : State)) rfl h15
      simpa [hr14, f13V, f13S] using h
    have p16 : RunsTo store program ⟨r14, Q + 16, false⟩ ⟨r15, Q + 17, false⟩ []
        [Category.registerWrite] := by
      have h := RunsTo.const (store := store) (s := (⟨r14, Q + 16, false⟩ : State)) rfl h16
      simpa [hr15] using h
    have p17 : RunsTo store program ⟨r15, Q + 17, false⟩ ⟨r16, Q + 18, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.add (store := store) (s := (⟨r15, Q + 17, false⟩ : State)) rfl h17
      simpa [hr16, f15V, f15O] using h
    have p18 : RunsTo store program ⟨r16, Q + 18, false⟩ ⟨r17, Q + 19, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.mulConst (store := store) (s := (⟨r16, Q + 18, false⟩ : State)) rfl h18
      simpa [hr17, f16K] using h
    have p19 : RunsTo store program ⟨r17, Q + 19, false⟩ ⟨r18, Q + 20, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.sub (store := store) (s := (⟨r17, Q + 19, false⟩ : State)) rfl h19
      simpa [hr18, f17A, f17O] using h
    have p20 : RunsTo store program ⟨r18, Q + 20, false⟩ ⟨r19, Q + 21, false⟩ []
        [Category.arithmetic] := by
      have h := RunsTo.add (store := store) (s := (⟨r18, Q + 20, false⟩ : State)) rfl h20
      simpa [hr19, f18P, f18A] using h
    -- the summary is `some` on this arm
    have hcell : summaryOfCells cB cMn cMx cA =
        some (cB - 1, cMn - 1, cMx - 1, cA - 1) :=
      summaryOfCells_eq_some hcB hcMn hcMx hcA
    refine ⟨r19, ?_, ?_, ?_⟩
    · have hrun := ((((((((hprefix.trans p12).trans p13).trans p14).trans p15).trans
        p16).trans p17).trans p18).trans p19).trans p20
      simpa [minCandidateCats, minCandidatePrefixCats, minCandidateValueCats,
        hcell] using hrun
    · have hV : r19 mMV = cB + cMn - (blocksPerSuper * blockSize + 2) + 1 := by
        rw [hr19, RegFile.write_other _ _ (by decide), hr18,
          RegFile.write_other _ _ (by decide), hr17,
          RegFile.write_other _ _ (by decide), hr16, RegFile.write_same]
      have hP : r19 mMP = block * blockSize + (cA - 1) := by
        rw [hr19, RegFile.write_same]
      -- THE SHIFT DOES NOT CANCEL: the truncating subtraction runs on the
      -- folded constant `span + 2`, and the `+ 1` is applied after it.
      have harith : cB + cMn - (blocksPerSuper * blockSize + 2) =
          cB - 1 + (cMn - 1) - blocksPerSuper * blockSize := by omega
      rw [hV, hP, hcell, harith]
      simp [bpRelativeSummaryMinCandidate, bpSuperblockSpan, blockStartOf,
        E1FringeFoldBlock.bestOfRegs]
    · intro r hr
      obtain ⟨hV, hP, hbank⟩ := hr
      rw [hr19, RegFile.write_other _ _ hP, hr18,
        RegFile.write_other _ _ (show r ≠ 117 by omega), hr17,
        RegFile.write_other _ _ (show r ≠ 116 by omega), hr16,
        RegFile.write_other _ _ hV, hr15,
        RegFile.write_other _ _ (show r ≠ 115 by omega), hr14,
        RegFile.write_other _ _ (show r ≠ 113 by omega), hr13,
        RegFile.write_other _ _ (show r ≠ 114 by omega), hr12,
        RegFile.write_other _ _ (show r ≠ 113 by omega)]
      exact hpres11 r ⟨hV, hP, hbank⟩
  · -- some cell absent: the summary is `none`, the default stands
    have hlt : bB + bMn + bMx + bA < 4 := by
      rcases Nat.eq_zero_or_pos cB with h | h
      · have hz : bB = 0 := by rw [hbB]; exact if_neg (by omega)
        omega
      · rcases Nat.eq_zero_or_pos cMn with h' | h'
        · have hz : bMn = 0 := by rw [hbMn]; exact if_neg (by omega)
          omega
        · rcases Nat.eq_zero_or_pos cMx with h'' | h''
          · have hz : bMx = 0 := by rw [hbMx]; exact if_neg (by omega)
            omega
          · rcases Nat.eq_zero_or_pos cA with h''' | h'''
            · have hz : bA = 0 := by rw [hbA]; exact if_neg (by omega)
              omega
            · exact absurd ⟨h, h', h'', h'''⟩ hall
    have htaken : r11 fNone = 1 := by rw [e11N]; exact if_pos hlt
    have p12 : RunsTo store program ⟨r11, Q + 12, false⟩ ⟨r11, Q + 21, false⟩ []
        [Category.branch] := by
      have h := RunsTo.brNZ (store := store)
        (s := (⟨r11, Q + 12, false⟩ : State)) rfl h12
      simpa [htaken] using h
    have hcell : summaryOfCells cB cMn cMx cA = none :=
      summaryOfCells_eq_none hall
    refine ⟨r11, ?_, ?_, hpres11⟩
    · have hrun := hprefix.trans p12
      simpa [minCandidateCats, minCandidatePrefixCats, hcell] using hrun
    · rw [e11V, e11P, hcell]
      simp

/-! ## Anti-vacuity: the `maxRel` test EXECUTES, and it DISCRIMINATES

The theorem above is stated over arbitrary cells, so it would hold
vacuously if the block were unreachable or if its two arms coincided.
Neither is the case, and the evidence below is EXECUTED rather than
argued: a concrete program is run by the kernel on two fixtures that
differ ONLY in the `maxRel` cell, and the outputs differ.

That is the exact mutation the "right shape, wrong content" defect class
would survive: dropping the `Q + 5` test leaves the trace, the read count
and the receipt untouched, and changes only the result -- which is what
these fixtures pin down. -/

/-- A store that answers nothing.  The block is read-free, so its
behaviour cannot depend on the store, and using the empty one makes that
manifest. -/
def witnessStore : ReadStore := ⟨fun _ _ => none⟩

/-- The block at `blockSize = 4`, `blocksPerSuper = 2`, hosted at `0`,
with a halt so the run terminates.  Superblock span is `2 * 4 = 8`. -/
def witnessProgram : E1Machine.Program := minCandidateBlock 4 2 0 ++ [.halt]

theorem witnessProgram_hosts :
    HostedAt witnessProgram 0 (minCandidateBlock 4 2 0) :=
  HostedAt.append_left (hostedAt_self witnessProgram)

/-- The four summary cells and the block index, in their registers. -/
def witnessRegs (block cB cMn cMx cA : Nat) : RegFile := fun r =>
  if r = sBlock then block
  else if r = sBase then cB
  else if r = sMin then cMn
  else if r = sMax then cMx
  else if r = sArg then cA
  else 0

/-- The output pair after running the block to completion. -/
def witnessOut (block cB cMn cMx cA : Nat) : Nat × Nat :=
  let final :=
    (E1Machine.run witnessStore witnessProgram 21
      ⟨witnessRegs block cB cMn cMx cA, 0, false⟩).final.regs
  (final mMV, final mMP)

/-- ALL FOUR CELLS PRESENT.  `baseline = 10`, `minRel = 5`, `maxRel = 7`,
`argOffset = 3`, `block = 1`, so the route's pair is
`(9 + 4 - 8, 1 * 4 + 2) = (5, 6)` and the machine's shifted pair is
`(6, 6)`. -/
theorem witnessOut_allPresent : witnessOut 1 10 5 7 3 = (6, 6) := by rfl

/-- `maxRel` ABSENT, EVERYTHING ELSE IDENTICAL.  The output is the `none`
encoding, even though no consumer reads `maxRel`'s value. -/
theorem witnessOut_maxRelAbsent : witnessOut 1 10 5 0 3 = (0, 0) := by rfl

/-- THE DISCRIMINATOR.  Two runs differing only in the `maxRel` cell
produce different outputs, so the `Q + 5` test is load-bearing and the
block genuinely consumes `maxRel`.  A block that dropped the test would
make these two equal. -/
theorem witness_maxRel_discriminates :
    witnessOut 1 10 5 7 3 ≠ witnessOut 1 10 5 0 3 := by decide

/-- The other three tests discriminate too, on the same fixture. -/
theorem witness_baseline_discriminates :
    witnessOut 1 10 5 7 3 ≠ witnessOut 1 0 5 7 3 := by decide

theorem witness_minRel_discriminates :
    witnessOut 1 10 5 7 3 ≠ witnessOut 1 10 0 7 3 := by decide

theorem witness_argOffset_discriminates :
    witnessOut 1 10 5 7 3 ≠ witnessOut 1 10 5 7 0 := by decide

/-- The block emits NO trace event on either arm: the receipt `[]` in the
theorem is the executed truth, not a modelling choice. -/
theorem witness_readLog_empty_allPresent :
    (E1Machine.run witnessStore witnessProgram 21
      ⟨witnessRegs 1 10 5 7 3, 0, false⟩).readLog = [] := by rfl

theorem witness_readLog_empty_maxRelAbsent :
    (E1Machine.run witnessStore witnessProgram 21
      ⟨witnessRegs 1 10 5 0 3, 0, false⟩).readLog = [] := by rfl

/-- THE THEOREM'S OWN HYPOTHESES ARE SATISFIABLE AT A CONCRETE FIXTURE,
and its conclusion at that fixture agrees with the executed run.  This is
the witness FOUND at the target rather than built for the premise: the
instantiation uses the same hosting fact the witness program supplies. -/
theorem witness_instantiates_theorem :
    ∃ regs' : RegFile,
      RunsTo witnessStore witnessProgram
          ⟨witnessRegs 1 10 5 7 3, 0, false⟩ ⟨regs', 0 + 21, false⟩ []
          (minCandidateCats (summaryOfCells 10 5 7 3).isSome) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          (summaryOfCells 10 5 7 3).map
            (bpRelativeSummaryMinCandidate 4 2 1) ∧
        (∀ r, MinCandUntouched r → regs' r = witnessRegs 1 10 5 7 3 r) :=
  minCandidateBlock_runsTo witnessStore witnessProgram_hosts rfl rfl rfl rfl rfl

/-- And that conclusion is not the trivial one: at this fixture the route's
min-candidate is genuinely `some (5, 6)`. -/
theorem witness_route_value :
    (summaryOfCells 10 5 7 3).map (bpRelativeSummaryMinCandidate 4 2 1) =
      some (5, 6) := by decide

/-- Whereas at the `maxRel`-absent fixture it is `none`. -/
theorem witness_route_value_maxRelAbsent :
    (summaryOfCells 10 5 0 3).map (bpRelativeSummaryMinCandidate 4 2 1) =
      none := by decide

/-- The two arms charge DIFFERENT category logs, so the block's cost is
data-dependent in the route's own terms and the `if` in
`minCandidateCats` is not decorative. -/
theorem witness_cats_differ :
    minCandidateCats (summaryOfCells 10 5 7 3).isSome ≠
      minCandidateCats (summaryOfCells 10 5 0 3).isSome := by decide

/-! ## THE GROUP AND THE CONSUMER, COMPOSED (M3d-22)

`canonicalSummaryGroup_runsTo` leaves four cells in `sBase`, `sMin`,
`sMax`, `sArg`; `minCandidateBlock_runsTo` consumes exactly those four.
Composing them on `RunsTo.trans` gives the interior's whole min-candidate
leg in one statement, stated in the ROUTE's own decode and carrying NO
VALIDITY HYPOTHESIS.

THAT IS WHAT THE UNCONDITIONAL BRIDGES BUY.  The consumer's `none` arm is
reached precisely when a cell is absent, and a cell is absent at indices
the interior's branch structure does not bound in advance.  A composite
carrying an `i < entriesLen` premise per read would have been unusable on
exactly the arm it most needs to cover.  Since M3d-22 the four
`geomCell_*_eq_routeDecode` bridges hold at every index, so the rewrite
below is unconditional and the `none` arm composes like any other. -/

/-- The summary tuple assembled from the four ROUTE DECODES of the summary
group's reads, at the canonical store and layout.

NAMED CAREFULLY.  This is the route's DECODE of the four cells, which is
what the value bridges deliver.

SCOPE NOTE SUPERSEDED (M3d-23).  Through M3d-22 this docstring recorded
that showing it equal to the value of
`canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) was a FURTHER step and NOT claimed, because
the link through `machineReadComputationAt` had not been built.  That link
now exists (`E1InteriorSummaryGroup.routeDecode_eq_machineReadComputation_value`)
and the equality IS claimed, at
`routeDecodedSummary_eq_summaryComputation_value` below. -/
def routeDecodedSummary (shape : Cartesian.CartesianShape) (block : Nat) :
    Option (Nat × Nat × Nat × Nat) :=
  summaryOfCells
    (geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).baseline
      (block / (canonicalSummaryLayout shape).blocksPerSuper))
    (geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).minRel
      block)
    (geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).maxRel
      block)
    (geomRouteDecode (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (canonicalSummaryLayout shape) (canonicalSummaryLayout shape).argOffset
      block)

/--
THE INTERIOR'S MIN-CANDIDATE LEG: the summary group followed by the
consumer, 177 instructions, exit `Q + 177`.

The receipt is the group's four route event lists in the route's bind
order and NOTHING ELSE -- the consumer is read-free, so composition adds
no event.  The category log is the group's followed by the consumer's, and
the consumer's arm is selected by the ROUTE's own summary being `some`.

NO VALIDITY HYPOTHESIS, and no store hypothesis. -/
theorem summaryMinCandidate_runsTo
    (shape : Cartesian.CartesianShape) {program : E1Machine.Program}
    {Q block : Nat} {regs : RegFile}
    (hHost : HostedAt program Q
      (summaryGroup (canonicalSummaryLayout shape) Q ++
        minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 156)))
    (hBlock : regs sBlock = block) :
    ∃ regs' : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape) program
          ⟨regs, Q, false⟩ ⟨regs', Q + 177, false⟩
          (geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).baseline
              (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).minRel block ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).maxRel block ++
            geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).argOffset block)
          ((geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).baseline Category.arithmetic
              (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).minRel
              Category.registerWrite block ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).maxRel
              Category.registerWrite block ++
            geomCats (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (canonicalSummaryLayout shape)
              (canonicalSummaryLayout shape).argOffset
              Category.registerWrite block) ++
            minCandidateCats (routeDecodedSummary shape block).isSome) ∧
        bestOfRegs (regs' mMV) (regs' mMP) =
          (routeDecodedSummary shape block).map
            (bpRelativeSummaryMinCandidate
              (RelativeRmm.canonicalLayout shape).blockSize
              (RelativeRmm.canonicalLayout shape).blocksPerSuper block) := by
  obtain ⟨regs1, hrun1, hB, hMn, hMx, hA, hpres1⟩ :=
    canonicalSummaryGroup_runsTo shape (HostedAt.append_left hHost) hBlock
  -- the four value bridges, UNCONDITIONAL in the index (M3d-22)
  rw [geomCell_baseline_eq_routeDecode] at hB
  rw [geomCell_minRel_eq_routeDecode] at hMn
  rw [geomCell_maxRel_eq_routeDecode] at hMx
  rw [geomCell_argOffset_eq_routeDecode] at hA
  -- the consumer is hosted immediately after the group's 156 instructions
  have hHost2 : HostedAt program (Q + 156)
      (minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
        (RelativeRmm.canonicalLayout shape).blocksPerSuper (Q + 156)) := by
    have h := HostedAt.append_right hHost
    rwa [summaryGroup_length] at h
  -- `sBlock` is 100, outside the group's write set
  have hBlock1 : regs1 sBlock = block := by
    rw [hpres1 sBlock (by decide)]; exact hBlock
  obtain ⟨regs2, hrun2, hval, _hpres2⟩ :=
    minCandidateBlock_runsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      hHost2 hBlock1 hB hMn hMx hA
  refine ⟨regs2, ?_, ?_⟩
  · have h := RunsTo.trans hrun1 hrun2
    have hpc : Q + 156 + 21 = Q + 177 := by omega
    rw [hpc] at h
    simpa [routeDecodedSummary] using h
  · simpa [routeDecodedSummary] using hval

/-! ### The composite's premises are satisfiable (rule 1)

`hHost` is an OWED premise, so it owes a witness that it can be met at the
intended instantiation -- not merely that it is well-formed. -/

/-- The leg hosts itself at `Q = 0`, with the consumer landing at exactly
`156`.  A wrong length would make this fail to match
`summaryMinCandidate_runsTo`'s premise. -/
theorem summaryMinCandidate_hosted_self (shape : Cartesian.CartesianShape) :
    HostedAt
      (summaryGroup (canonicalSummaryLayout shape) 0 ++
        minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (0 + 156)) 0
      (summaryGroup (canonicalSummaryLayout shape) 0 ++
        minCandidateBlock (RelativeRmm.canonicalLayout shape).blockSize
          (RelativeRmm.canonicalLayout shape).blocksPerSuper (0 + 156)) :=
  hostedAt_self _

/-- RULE 1 DISCHARGED: `hHost` and `hBlock` are JOINTLY satisfiable at the
intended instantiation.  The theorem is instantiated at the self-hosting
composite with `sBlock` actually holding `block`, and the existential is
carried through to a concrete consequence rather than left abstract. -/
theorem summaryMinCandidate_premises_satisfiable
    (shape : Cartesian.CartesianShape) (block : Nat) :
    ∃ regs' : RegFile,
      bestOfRegs (regs' mMV) (regs' mMP) =
        (routeDecodedSummary shape block).map
          (bpRelativeSummaryMinCandidate
            (RelativeRmm.canonicalLayout shape).blockSize
            (RelativeRmm.canonicalLayout shape).blocksPerSuper block) := by
  obtain ⟨regs', _, hval⟩ :=
    summaryMinCandidate_runsTo shape (summaryMinCandidate_hosted_self shape)
      (regs := RegFile.write (fun _ => 0) sBlock block) rfl
  exact ⟨regs', hval⟩

/-! ## The summary tuple, as the value of the ROUTE's own computation

M3d-22 named `routeDecodedSummary` carefully and recorded that equating it
with the value of `canonicalRelativeRmmMachineSummaryComputation`
(`InteriorDirectory.lean:2277`) was a FURTHER step, not claimed, because
the link through `machineReadComputationAt` had not been built.  M3d-23
built that link, so the step is now available and is taken here.

It is short because all four reads were already handled one at a time.
What remains is the OPTION-SHIFT bookkeeping: the links deliver each cell
option-shifted as a `Nat`, `summaryOfCells` re-inverts through `cellOpt`,
and the route's tuple `match` (`InteriorDirectory.lean:2294`-`:2296`) is
the same four-way split on the unshifted `Option`s. -/

/-- `cellOpt` INVERTS the shift the links produce.  This is the whole
bookkeeping content of the theorem below.

It fires only because the links state the shift as the NAMED
`E1InteriorSummaryGroup.optShift` rather than inline: an inline `match`
elaborates to a fresh auxiliary per declaration, so this lemma would be
defeq to the goal and still not apply. -/
@[simp] theorem cellOpt_optShift (v : Option Nat) :
    cellOpt (E1InteriorSummaryGroup.optShift v) = v := by
  cases v <;> rfl

/-- THE SUMMARY TUPLE IS THE ROUTE COMPUTATION'S VALUE.

No validity, cap or store hypothesis, inherited from the unconditional
bridges and the hypothesis-free links.  This supersedes the scope note on
`routeDecodedSummary`: that equality is no longer merely unclaimed, it
HOLDS. -/
theorem routeDecodedSummary_eq_summaryComputation_value
    (shape : Cartesian.CartesianShape) (block : Nat) :
    routeDecodedSummary shape block =
      ((canonicalRelativeRmmMachineSummaryComputation shape block).run
        (RMQ.SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape).segment)).value := by
  unfold routeDecodedSummary summaryOfCells
    canonicalRelativeRmmMachineSummaryComputation
  rw [E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
        (canonicalRelativeRmmSummaryTable shape).baselineTable _ _ _
        rfl rfl rfl,
      E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
        (canonicalRelativeRmmSummaryTable shape).minRelTable _ _ _
        rfl rfl rfl,
      E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
        (canonicalRelativeRmmSummaryTable shape).maxRelTable _ _ _
        rfl rfl rfl,
      E1InteriorSummaryGroup.geomRouteDecode_eq_readComputation_value shape _
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable _ _ _
        rfl rfl rfl]
  simp [FlatStoreExecution.append]
  rfl

/-! ## THE RECEIPT, POSITIONALLY, IN THE ROUTE'S BIND ORDER

The theorem above settles the summary tuple's VALUE.  IT DOES NOT SETTLE
THE RECEIPT, and the independence is not a technicality -- the fixtures at
the end of this section EXHIBIT two four-segment receipts that
* have the same number of segments,
* have the same total length,
* have segments of the same respective lengths, and
* PRODUCE THE SAME VALUE,
and that are nevertheless different receipts, because the head segment
reads the wrong CELL.  Every aggregate check the harness performs -- read
count, trace length, segment count, and the value equation proved above --
accepts both.  Only element-by-element comparison rejects the impostor.

THE DEFECT MODELLED IS THE ROUTE'S OWN MOST LIKELY ONE.  The baseline read
is issued at `block / blocksPerSuper`; the other three are issued at
`block`.  The head is therefore the ONE segment whose index differs from
its neighbours', which makes "copy the index from the segment below" a
live error.  The stale-head fixture is exactly that error.

The equation below is stated per-constructor and in issue order, with each
segment's INDEX written out, so the head's `block / blocksPerSuper` is
visible in the statement rather than buried in a definition. -/

/-- THE RECEIPT OF ONE SUMMARY COMPONENT READ, at the canonical store and
layout: the component's own address list, each address paired with the word
the canonical store returns there. -/
def summaryReadReceipt (shape : Cartesian.CartesianShape)
    (G : E1InteriorSummaryGroup.TableGeom) (i : Nat) :
    List (Prod Nat (Option (List Bool))) :=
  (E1InteriorChunkFold.chunkAddrs G.base
      (canonicalSummaryLayout shape).deadAddress G.entriesLen G.chunkCount i).map
    (fun a =>
      (a, (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        (canonicalSummaryLayout shape).segment a))

/-- THE SUMMARY COMPUTATION'S RECEIPT IS THE FOUR COMPONENT RECEIPTS,
CONCATENATED IN THE ROUTE'S BIND ORDER.

Baseline at the SUPERBLOCK index `block / blocksPerSuper`, then minRel,
maxRel and argOffset at `block` -- in that order, with no aggregation
anywhere in the statement.  No validity, cap or store hypothesis, inherited
from the hypothesis-free receipt lemma exactly as the value theorem above
inherits from the hypothesis-free links. -/
theorem summaryComputation_reads_eq_routeReceipt
    (shape : Cartesian.CartesianShape) (block : Nat) :
    ((canonicalRelativeRmmMachineSummaryComputation shape block).run
        (RMQ.SuccinctClose.flatWordStoreOfReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape).segment)).reads =
      summaryReadReceipt shape (canonicalSummaryLayout shape).baseline
            (block / (canonicalSummaryLayout shape).blocksPerSuper)
        ++ summaryReadReceipt shape (canonicalSummaryLayout shape).minRel block
        ++ summaryReadReceipt shape (canonicalSummaryLayout shape).maxRel block
        ++ summaryReadReceipt shape (canonicalSummaryLayout shape).argOffset
            block := by
  unfold canonicalRelativeRmmMachineSummaryComputation
    canonicalRelativeRmmMachineReadNatComputation summaryReadReceipt
  simp only [FlatStoreComputation.bind_run, FlatStoreComputation.map_run_reads,
    FlatStoreExecution.append]
  rw [E1InteriorSummaryGroup.machineReadComputation_reads
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) _
        (canonicalRelativeRmmSummaryTable shape).baselineTable _ _ _ _ _ _
        rfl rfl,
      E1InteriorSummaryGroup.machineReadComputation_reads
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) _
        (canonicalRelativeRmmSummaryTable shape).minRelTable _ _ _ _ _ _
        rfl rfl,
      E1InteriorSummaryGroup.machineReadComputation_reads
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) _
        (canonicalRelativeRmmSummaryTable shape).maxRelTable _ _ _ _ _ _
        rfl rfl,
      E1InteriorSummaryGroup.machineReadComputation_reads
        (concreteBPNativeSuccinctRMQGlobalReadStore shape) _
        (canonicalRelativeRmmSummaryTable shape).argOffsetTable _ _ _ _ _ _
        rfl rfl]
  simp [canonicalSummaryLayout]

/-- ONE SEGMENT, MACHINE AGAINST ROUTE.  The machine's emitted events for a
component read are that component's receipt, respelled event-wise.  Both
sides are the SAME `chunkAddrs` list under the SAME store lookup, so this
is a change of vocabulary and nothing more. -/
theorem geomEvents_eq_summaryReadReceipt_map
    (shape : Cartesian.CartesianShape)
    (G : E1InteriorSummaryGroup.TableGeom) (i : Nat) :
    geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
        (canonicalSummaryLayout shape) G i =
      (summaryReadReceipt shape G i).map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  simp [geomEvents, E1InteriorChunkFold.chunkRouteEvents, summaryReadReceipt,
    List.map_map, Function.comp]

/-- THE POSITIONAL RECEIPT EQUALITY, MACHINE AGAINST ROUTE.

The trace `summaryMinCandidate_runsTo` (`:929`) emits IS the read log the
route's summary computation records -- the same events, in the same
positions, carrying the same segment, addresses and words.

THIS IS THE OBLIGATION MISSION ITEM 1 NAMES, and it is what
`summaryComputation_reads_eq_routeReceipt` exists to support: the machine
side is four `geomEvents`, the route side is four `summaryReadReceipt`
segments, and both reduce to the SAME `chunkAddrs` list mapped through the
SAME store lookup.  Nothing here is an aggregate: the equation is between
two lists, so it constrains every position.

The map is the injection `(address, word) => TraceEvent.readWord segment
address word`, which is how the operational read log and the machine's
trace vocabulary differ; it is a change of spelling, not of content. -/
theorem summaryMachineTrace_eq_routeReads
    (shape : Cartesian.CartesianShape) (block : Nat) :
    (geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape)
          (canonicalSummaryLayout shape).baseline
          (block / (canonicalSummaryLayout shape).blocksPerSuper) ++
        geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape)
          (canonicalSummaryLayout shape).minRel block ++
        geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape)
          (canonicalSummaryLayout shape).maxRel block ++
        geomEvents (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalSummaryLayout shape)
          (canonicalSummaryLayout shape).argOffset block) =
      ((canonicalRelativeRmmMachineSummaryComputation shape block).run
          (RMQ.SuccinctClose.flatWordStoreOfReadStore
            (concreteBPNativeSuccinctRMQGlobalReadStore shape)
            (canonicalSummaryLayout shape).segment)).reads.map
        (fun p =>
          TraceEvent.readWord (canonicalSummaryLayout shape).segment p.1 p.2) := by
  rw [summaryComputation_reads_eq_routeReceipt, List.map_append,
    List.map_append, List.map_append, geomEvents_eq_summaryReadReceipt_map,
    geomEvents_eq_summaryReadReceipt_map, geomEvents_eq_summaryReadReceipt_map,
    geomEvents_eq_summaryReadReceipt_map]

/-! ### ANTI-VACUITY: THE STALE HEAD, EXECUTED

Parametric in `wordSize` for the reason recorded in the summary group: the
shape-level receipt routes through `machineWordBits`, hence `Nat.log2`,
which the kernel cannot evaluate.  These fixtures run the SAME receipt
lemma the theorem above consumes, at `wordSize = 8`.

DELIBERATELY MULTI-CHUNK, and the count is EVALUATED rather than inherited
(`receiptWitness_chunkCount` below), because the inherited figure is the
kind of quantity that goes stale silently. -/

/-- Fixture table: SIX entries, so that BOTH the true head index `1` and
the stale head index `5` are VALID cells.  That is the whole point -- if
the stale index fell off the end it would take the dead path, the segment
lengths would differ, and a length check would catch the defect.  It must
not. -/
def receiptWitnessTable : SuccinctSpace.FixedWidthNatTable [1, 2, 3, 4, 5, 6] 20 :=
  SuccinctSpace.FixedWidthNatTable.ofEntries [1, 2, 3, 4, 5, 6] 20 (by
    intro entry hmem
    cases hmem with
    | head => decide
    | tail _ h1 =>
      cases h1 with
      | head => decide
      | tail _ h2 =>
        cases h2 with
        | head => decide
        | tail _ h3 =>
          cases h3 with
          | head => decide
          | tail _ h4 =>
            cases h4 with
            | head => decide
            | tail _ h5 =>
              cases h5 with
              | head => decide
              | tail _ h6 => cases h6)

/-- Fixture store on segment `7`.  CELLS `1` AND `5` OF THE BASELINE TABLE
HOLD THE SAME WORDS -- addresses `203,204,205` and `215,216,217` carry
identical content.  So the two reads DECODE TO THE SAME VALUE and differ
only in the addresses they logged, which is what makes the value equation
blind to the substitution. -/
def receiptWitnessStore : ReadStore :=
  ⟨fun segment address =>
    if segment = 7 then
      if address = 203 then some [true, false, false]
      else if address = 204 then some [false]
      else if address = 205 then some [false]
      else if address = 215 then some [true, false, false]
      else if address = 216 then some [false]
      else if address = 217 then some [false]
      else if address = 315 then some [false, true, false]
      else if address = 316 then some [false]
      else if address = 317 then some [false]
      else if address = 415 then some [true, true]
      else if address = 416 then some [false]
      else if address = 417 then some [false]
      else if address = 515 then some [false, false, true]
      else if address = 516 then some [false]
      else if address = 517 then some [false]
      else if address = 999 then some [true, false, true]
      else none
    else none⟩

/-- RULE 3, APPLIED TO AN INHERITED COUNT: three chunks per cell at width
`20`, word size `8`, EVALUATED here rather than carried. -/
theorem receiptWitness_chunkCount :
    SuccinctSpace.fixedWidthNatTableMachineChunkCount 20 8 = 3 := rfl

/-- One component segment of the fixture receipt. -/
def receiptWitnessSegment (base i : Nat) : List (Prod Nat (Option (List Bool))) :=
  ((receiptWitnessTable.machineReadComputationAt 8 base 999 i).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore receiptWitnessStore 7)).reads

/-- One component segment's VALUE, for the agreement check below. -/
def receiptWitnessValue (base i : Nat) : Nat :=
  E1InteriorSummaryGroup.optShift
    ((receiptWitnessTable.machineReadComputationAt 8 base 999 i).run
      (RMQ.SuccinctClose.flatWordStoreOfReadStore receiptWitnessStore 7)).value

/-- RULE 1: the receipt lemma's two hypotheses are JOINTLY SATISFIABLE at a
real instantiation, and the instance is carried to concrete consequences
below rather than left existential. -/
theorem receiptWitness_reads_instantiated (base i : Nat) :
    receiptWitnessSegment base i =
      (E1InteriorChunkFold.chunkAddrs base 999 6 3 i).map
        (fun a => (a, receiptWitnessStore.readWord? 7 a)) :=
  E1InteriorSummaryGroup.machineReadComputation_reads receiptWitnessStore 7
    receiptWitnessTable 8 base 999 6 3 i rfl rfl

/-- THE ROUTE'S RECEIPT at `block = 5`, `blocksPerSuper = 4`: the head is
issued at the SUPERBLOCK index `5 / 4 = 1`, the other three at `5`. -/
def receiptWitnessTrue : List (Prod Nat (Option (List Bool))) :=
  receiptWitnessSegment 200 (5 / 4)
    ++ receiptWitnessSegment 300 5
    ++ receiptWitnessSegment 400 5
    ++ receiptWitnessSegment 500 5

/-- THE STALE HEAD: the head segment issued at `block` instead of
`block / blocksPerSuper`.  Everything else is identical -- same segments,
same order, same three trailing indices. -/
def receiptWitnessStaleHead : List (Prod Nat (Option (List Bool))) :=
  receiptWitnessSegment 200 5
    ++ receiptWitnessSegment 300 5
    ++ receiptWitnessSegment 400 5
    ++ receiptWitnessSegment 500 5

/-- THE RECEIPT, EXECUTED.  Not a length, not a count: the actual pairs, in
order, addresses and stored words both. -/
theorem receiptWitness_executed :
    receiptWitnessTrue =
      [ (203, some [true, false, false]), (204, some [false]), (205, some [false])
      , (315, some [false, true, false]), (316, some [false]), (317, some [false])
      , (415, some [true, true]), (416, some [false]), (417, some [false])
      , (515, some [false, false, true]), (516, some [false]), (517, some [false])
      ] := rfl

/-- VALUE EQUALITY DOES NOT ENTAIL RECEIPT EQUALITY, and this is the
instantiation that proves the non-entailment.  Here the true head and the
stale head decode to the SAME value while (below) logging DIFFERENT
receipts.  So a value equation of the form
`routeDecodedSummary_eq_summaryComputation_value` -- however strong -- is
formally incapable of rejecting the impostor, which is what makes the
receipt a genuinely separate obligation rather than a corollary.

WHAT THIS DOES NOT CLAIM: that the CANONICAL store makes these two cells
agree.  It claims only that agreement is possible, which is all that is
needed to show the value equation cannot be doing the receipt's work. -/
theorem receiptWitness_staleHead_value_agrees :
    receiptWitnessValue 200 (5 / 4) = receiptWitnessValue 200 5 := rfl

/-- AND THE AGGREGATE CHECKS ARE BLIND TOO: same total length, and the same
FOUR segment lengths respectively.  A harness comparing read counts,
segment counts, or per-segment lengths accepts the impostor. -/
theorem receiptWitness_staleHead_lengths_agree :
    (receiptWitnessTrue.length, receiptWitnessStaleHead.length,
      [ (receiptWitnessSegment 200 (5 / 4)).length
      , (receiptWitnessSegment 300 5).length
      , (receiptWitnessSegment 400 5).length
      , (receiptWitnessSegment 500 5).length ],
      [ (receiptWitnessSegment 200 5).length
      , (receiptWitnessSegment 300 5).length
      , (receiptWitnessSegment 400 5).length
      , (receiptWitnessSegment 500 5).length ])
      = (12, 12, [3, 3, 3, 3], [3, 3, 3, 3]) := rfl

/-- THE DISCRIMINATION.  Same length, same segment lengths, same value --
and STILL NOT EQUAL, because the head logged `215,216,217` where the route
logs `203,204,205`.  Positional comparison is the only check that sees it. -/
theorem receiptWitness_staleHead_discriminates :
    receiptWitnessTrue ≠ receiptWitnessStaleHead := by decide

/-- THE HEAD IS WHERE THEY DIFFER, AND ONLY IN THE ADDRESSES.  The route's
head logs `203,204,205`; the stale head logs `215,216,217`. -/
theorem receiptWitness_staleHead_addresses_differ :
    ((receiptWitnessSegment 200 (5 / 4)).map Prod.fst,
      (receiptWitnessSegment 200 5).map Prod.fst)
      = ([203, 204, 205], [215, 216, 217]) := rfl

/-- AND THE STORED WORDS AGREE.  The two head segments carry the SAME words
in the same order, so a check on the receipt's CONTENT alone -- as opposed
to its address/content PAIRS -- also accepts the impostor.  Together with
the value agreement above, this closes off every non-positional check. -/
theorem receiptWitness_staleHead_words_agree :
    (receiptWitnessSegment 200 (5 / 4)).map Prod.snd =
      (receiptWitnessSegment 200 5).map Prod.snd := rfl

end E1InteriorMinCandidate
end WordRAM
end RMQ
