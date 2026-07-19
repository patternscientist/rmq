import RMQ.Core.WordRAM.E1CloseCompose
import RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.Candidate

/-!
# E1 amended machine: the THREE-WAY CANDIDATE MERGE block (M3d-7)

The cross-block close object
`bpChunkedCrossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeTrace.lean:1144`)
sequences five sub-computations and fuses its epilogue onto the right
fringe arm as

    TraceResult.map
      (fun right? => bpCandidateClose? (bpCandidateMerge3? left? middle? right?))
      (<right fringe arm>)

This module builds the machine block for that epilogue.  It is the last
piece of the cross-block arm that is neither assembly nor blocked on the
interior leg: before it existed, `rg` over `RMQ/Core/WordRAM/` for
`bpCandidateMerge` / `candMerge` / `merge3` returned nothing, so the
cross-block arm could not be assembled even partially into a running
program.

## Why `E1SameBlockArm.sameBlockClose` does not generalise

That epilogue (`E1SameBlockArm.lean:238`, two instructions) handles
`bpCandidateClose?` on a SINGLE arm and needs no option dispatch, because
`bpFringeCandGlobal` is total into `some` (`ChargedFringeChunks.lean:1617`
— both match arms produce `some`).  Here `middle?` is GENUINELY optional:
the interior leg sits behind the guard `leftBlock + 1 < rightBlock`
(`ChargedFringeTrace.lean:1163`) whose else-branch is
`TraceResult.pure none`.  So the block needs a real three-way,
option-aware minimum, and all six control paths must be handled.

## Encoding and why the comparisons are direct

Candidates are `Nat × Nat` pairs with `.1` the VALUE being minimized and
`.2` the POSITION (`bpCandidateBetter` compares only `.1`;
`bpCandidateClose?` projects only `.2`; `bpFringeCandGlobal` rebases only
`.2`).  Optional candidates use the house `+1` BIAS already used by
`fringeMerge` (`E1FringeFoldBlock.lean:204`, `.add fBV fCV fOne`) and
decoded by `bestOfRegs`: `0` encodes `none`, `v + 1` encodes `some v`.

The bias is what makes the block read-free AND comparison-direct: for two
OCCUPIED candidates the biased test `v₁ + 1 < v₂ + 1` is literally the
route's `v₁ < v₂`, so no unbiasing arithmetic is needed before either
comparison.  Only occupancy needs a test, and only for `middle?`, which
is one `brNZ`.

`bpCandidateBetter` uses STRICT `<` (`Candidate.lean:15`), so ties keep
the LEFT candidate; since `bpCandidateMerge3?` associates to the left
(`Candidate.lean:24`), the left fringe wins ties over the interior and
both win ties over the right fringe.  The block reproduces this by using
`natLt` (never `natLe`) at both comparison sites.

## The occupancy hypotheses are route facts, not conveniences

The block takes the left and right candidate registers in occupied form
(`lv + 1`, `rv + 1`).  That is exactly what the route supplies: both
fringe arms end in `bpFringeCandGlobal`, which is total into `some`.
There is no reusable lemma for that in the tree — it is discharged
inline, per site — so `bpFringeCandGlobal_isSome` below states it once.

The block is read-free, matching the route: the epilogue rides a
`TraceResult.map`, which contributes no trace event.
-/

namespace RMQ
namespace WordRAM
namespace E1CandMerge3

open E1Machine
open E1FringeFoldBlock
open E1FringeArmBlock
open E1SameBlockArm
open RMQ.SuccinctClose

/-! ## The missing totality lemma

`bpFringeCandGlobal` is total into `some`, which is what makes the left
and right candidates occupied.  The tree discharges this inline at every
site; stating it once removes the per-site `cases`. -/

theorem bpFringeCandGlobal_isSome (base fallbackVal fallbackPos : Nat)
    (candidate? : Option (Nat × Nat)) :
    (bpFringeCandGlobal base fallbackVal fallbackPos candidate?).isSome = true := by
  cases candidate? <;> rfl

/-! ## Register bank extension (three-way merge, `75 .. 84`)

The bank below `75` is fully allocated: `40 .. 62` fold, `63 .. 68` arm,
`69 .. 71` same-block, `72 .. 74` dispatch.  The merge writes its
`bpCandidateClose?` payload into the SAME `fRes` (`69`) the same-block
leg uses, so the two dispatch arms converge on one output register. -/

/-- Left candidate, biased value (`0` = `none`, `v + 1` = `some v`). -/
abbrev mLV : Nat := 75
/-- Left candidate, position. -/
abbrev mLP : Nat := 76
/-- Middle (interior) candidate, biased value. -/
abbrev mMV : Nat := 77
/-- Middle (interior) candidate, position. -/
abbrev mMP : Nat := 78
/-- Right candidate, biased value. -/
abbrev mRV : Nat := 79
/-- Right candidate, position. -/
abbrev mRP : Nat := 80
/-- Running accumulator, biased value. -/
abbrev mAV : Nat := 81
/-- Running accumulator, position. -/
abbrev mAP : Nat := 82
/-- Scratch. -/
abbrev mT : Nat := 83
/-- Scratch. -/
abbrev mU : Nat := 84

/-! ## Route-side pure helpers

The accumulator after the middle step, named so the category log and the
block invariant can both refer to it without re-deriving the merge. -/

/-- The accumulator after folding `middle?` into an OCCUPIED left
candidate. -/
def candAfterMid (left : Nat × Nat) (middle : Option (Nat × Nat)) :
    Nat × Nat :=
  match middle with
  | none => left
  | some m => bpCandidateBetter left m

/-- Folding `middle?` into an occupied left candidate stays occupied, at
`candAfterMid`. -/
theorem bpCandidateMerge?_some_left (left : Nat × Nat)
    (middle : Option (Nat × Nat)) :
    bpCandidateMerge? (some left) middle = some (candAfterMid left middle) := by
  cases middle <;> rfl

/-- With both fringe arms occupied, the three-way merge is one
`bpCandidateBetter` applied to `candAfterMid`. -/
theorem bpCandidateMerge3?_some_left_right (left right : Nat × Nat)
    (middle : Option (Nat × Nat)) :
    bpCandidateMerge3? (some left) middle (some right) =
      some (bpCandidateBetter (candAfterMid left middle) right) := by
  unfold bpCandidateMerge3?
  rw [bpCandidateMerge?_some_left]
  rfl

/-! ## Block segments -/

/--
The middle phase (`E+0 .. E+8`, exit `E+9` on every arm): seed the
accumulator from the occupied left candidate, then fold `middle?` in if
it is present AND strictly better.

Three arms: middle absent (4 instructions), middle present and strictly
better (7), middle present and not better (6).
-/
def candMerge3Mid (E : Nat) : List Instr :=
  [ .move mAV mLV        -- E+0   acc := left
  , .move mAP mLP        -- E+1
  , .brNZ mMV (E + 4)    -- E+2   middle present? -> compare
  , .brNZ fOne (E + 9)   -- E+3   middle absent   -> skip
  , .natLt mT mMV mAV    -- E+4   biased test IS the route's `m.1 < acc.1`
  , .brNZ mT (E + 7)     -- E+5
  , .brNZ fOne (E + 9)   -- E+6   not better      -> skip
  , .move mAV mMV        -- E+7   acc := middle
  , .move mAP mMP ]      -- E+8

@[simp] theorem candMerge3Mid_length (E : Nat) :
    (candMerge3Mid E).length = 9 := rfl

/--
The right phase (`E+9 .. E+13`, exit `E+14` on both arms): fold the
OCCUPIED right candidate in if strictly better.  Two arms (4 / 3).
-/
def candMerge3Right (E : Nat) : List Instr :=
  [ .natLt mU mRV mAV    -- E+9
  , .brNZ mU (E + 12)    -- E+10
  , .brNZ fOne (E + 14)  -- E+11  not better -> skip
  , .move mAV mRV        -- E+12  acc := right
  , .move mAP mRP ]      -- E+13

@[simp] theorem candMerge3Right_length (E : Nat) :
    (candMerge3Right E).length = 5 := rfl

/--
The `bpCandidateClose?` epilogue (`E+14 .. E+15`): the merged candidate
is occupied (the left arm is), so the close is the single arithmetic
expression `position - 1` and needs no option dispatch.
-/
def candMerge3Close : List Instr :=
  [ .const mT 1          -- E+14
  , .sub fRes mAP mT ]   -- E+15

@[simp] theorem candMerge3Close_length : candMerge3Close.length = 2 := rfl

/-- The whole three-way merge block at base `E` (16 instructions, exit
`E + 16`), read-free. -/
def candMerge3 (E : Nat) : List Instr :=
  candMerge3Mid E ++ (candMerge3Right E ++ candMerge3Close)

@[simp] theorem candMerge3_length (E : Nat) :
    (candMerge3 E).length = 16 := rfl

/-- The block performs no memory read: the route's epilogue rides a
`TraceResult.map`, which contributes no trace event. -/
theorem candMerge3_readFree (E : Nat) :
    ∀ instr ∈ candMerge3 E, instr.category ≠ Category.memoryRead := by
  intro instr hinstr
  simp only [candMerge3, candMerge3Mid, candMerge3Right, candMerge3Close,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
    or_false] at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h | h | h | h | h | h |
      h | h <;> subst h <;> simp [Instr.category]

/-! ## Category logs

Every arm is a FUNCTION of the route-side branch conditions — middle
occupancy, and the two `bpCandidateBetter` comparisons — never a
numeral. -/

/-- Categories charged by the middle phase, on the arm the route selects. -/
def candMerge3MidCats (left : Nat × Nat) (middle : Option (Nat × Nat)) :
    List Category :=
  match middle with
  | none => [.registerWrite, .registerWrite, .branch, .branch]
  | some m =>
      if m.1 < left.1 then
        [ .registerWrite, .registerWrite, .branch, .comparison, .branch
        , .registerWrite, .registerWrite ]
      else
        [ .registerWrite, .registerWrite, .branch, .comparison, .branch
        , .branch ]

/-- Categories charged by the right phase, on the arm the route selects. -/
def candMerge3RightCats (acc right : Nat × Nat) : List Category :=
  if right.1 < acc.1 then
    [.comparison, .branch, .registerWrite, .registerWrite]
  else
    [.comparison, .branch, .branch]

/-- Categories charged by the close epilogue.  Unconditional: the close
has no route-side branch, because the merge of an occupied left candidate
is occupied. -/
def candMerge3CloseCats : List Category := [.registerWrite, .arithmetic]

/-- Category log of the whole block on the arm the route selects. -/
def candMerge3Cats (left : Nat × Nat) (middle : Option (Nat × Nat))
    (right : Nat × Nat) : List Category :=
  candMerge3MidCats left middle ++
    (candMerge3RightCats (candAfterMid left middle) right ++
      candMerge3CloseCats)

/-! ## Width certificates

Constructor-exhaustive, no wildcard arm.  The block carries no divisor,
so no positivity side condition arises. -/

/-- Constructor-exhaustive width certificate for the middle phase. -/
theorem candMerge3Mid_fits (w E : Nat) (hw : E + 9 < 2 ^ w)
    (hreg : 84 < 2 ^ w) :
    ∀ instr ∈ candMerge3Mid E, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h40 : (40 : Nat) < 2 ^ w := by omega
  have h75 : (75 : Nat) < 2 ^ w := by omega
  have h76 : (76 : Nat) < 2 ^ w := by omega
  have h77 : (77 : Nat) < 2 ^ w := by omega
  have h78 : (78 : Nat) < 2 ^ w := by omega
  have h81 : (81 : Nat) < 2 ^ w := by omega
  have h82 : (82 : Nat) < 2 ^ w := by omega
  have h83 : (83 : Nat) < 2 ^ w := by omega
  have hE4 : E + 4 < 2 ^ w := by omega
  have hE7 : E + 7 < 2 ^ w := by omega
  have hE9 : E + 9 < 2 ^ w := hw
  simp only [candMerge3Mid, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h | h | h | h | h <;> subst h
  · exact ⟨h81, h75⟩
  · exact ⟨h82, h76⟩
  · exact ⟨h77, hE4⟩
  · exact ⟨h40, hE9⟩
  · exact ⟨h83, h77, h81⟩
  · exact ⟨h83, hE7⟩
  · exact ⟨h40, hE9⟩
  · exact ⟨h81, h77⟩
  · exact ⟨h82, h78⟩

/-- Constructor-exhaustive width certificate for the right phase. -/
theorem candMerge3Right_fits (w E : Nat) (hw : E + 14 < 2 ^ w)
    (hreg : 84 < 2 ^ w) :
    ∀ instr ∈ candMerge3Right E, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h40 : (40 : Nat) < 2 ^ w := by omega
  have h79 : (79 : Nat) < 2 ^ w := by omega
  have h80 : (80 : Nat) < 2 ^ w := by omega
  have h81 : (81 : Nat) < 2 ^ w := by omega
  have h82 : (82 : Nat) < 2 ^ w := by omega
  have h84 : (84 : Nat) < 2 ^ w := hreg
  have hE12 : E + 12 < 2 ^ w := by omega
  have hE14 : E + 14 < 2 ^ w := hw
  simp only [candMerge3Right, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h | h | h | h <;> subst h
  · exact ⟨h84, h79, h81⟩
  · exact ⟨h84, hE12⟩
  · exact ⟨h40, hE14⟩
  · exact ⟨h81, h79⟩
  · exact ⟨h82, h80⟩

/-- Constructor-exhaustive width certificate for the close epilogue. -/
theorem candMerge3Close_fits (w : Nat) (hreg : 84 < 2 ^ w) :
    ∀ instr ∈ candMerge3Close, Instr.FieldsFit w instr := by
  intro instr hinstr
  have h1 : (1 : Nat) < 2 ^ w := by omega
  have h69 : (69 : Nat) < 2 ^ w := by omega
  have h82 : (82 : Nat) < 2 ^ w := by omega
  have h83 : (83 : Nat) < 2 ^ w := by omega
  simp only [candMerge3Close, List.mem_cons, List.not_mem_nil, or_false]
    at hinstr
  rcases hinstr with h | h <;> subst h
  · exact ⟨h83, h1⟩
  · exact ⟨h69, h82, h83⟩

/-- Constructor-exhaustive width certificate for the whole block. -/
theorem candMerge3_fits (w E : Nat) (hw : E + 14 < 2 ^ w)
    (hreg : 84 < 2 ^ w) :
    ∀ instr ∈ candMerge3 E, Instr.FieldsFit w instr := by
  intro instr hinstr
  simp only [candMerge3, List.mem_append] at hinstr
  rcases hinstr with h | h | h
  · exact candMerge3Mid_fits w E (by omega) hreg instr h
  · exact candMerge3Right_fits w E hw hreg instr h
  · exact candMerge3Close_fits w hreg instr h

/-! ## Hosting bundle -/

/-- Peel the block's hosting fact into its three segments. -/
theorem candMerge3_hosting {program : E1Machine.Program} {E : Nat}
    (hhost : HostedAt program E (candMerge3 E)) :
    HostedAt program E (candMerge3Mid E) ∧
    HostedAt program (E + 9) (candMerge3Right E) ∧
    HostedAt program (E + 14) candMerge3Close := by
  have hR1 := HostedAt.append_right hhost
  have hR2 := HostedAt.append_right hR1
  refine ⟨HostedAt.append_left hhost, ?_, ?_⟩
  · have := HostedAt.append_left hR1
    simpa using this
  · simpa using hR2

/-! ## Preservation predicate (NUMERALS, per the house pattern) -/

/-- Registers the block never writes.  Stated in numerals: with the
register abbrevs `omega` treats the names as unanalysed atoms and fails. -/
abbrev CandMerge3Untouched (r : Nat) : Prop :=
  r ≠ 69 ∧ r ≠ 81 ∧ r ≠ 82 ∧ r ≠ 83 ∧ r ≠ 84

/-! ## Simulation -/

/--
The middle phase runs to `E + 9` on all three arms, leaving the
accumulator holding `candAfterMid` in biased form.

The biased accumulator invariant `mAV = acc.1 + 1` is what lets the RIGHT
phase compare without unbiasing.
-/
theorem candMerge3Mid_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hMid : HostedAt program E (candMerge3Mid E))
    (regs : RegFile) (lv lp mv mp : Nat)
    (hOne : regs fOne = 1)
    (hLV : regs mLV = lv + 1) (hLP : regs mLP = lp)
    (hMV : regs mMV = mv) (hMP : regs mMP = mp) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E, false⟩ ⟨regs', E + 9, false⟩ []
        (candMerge3MidCats (lv, lp) (bestOfRegs mv mp)) ∧
      regs' mAV = (candAfterMid (lv, lp) (bestOfRegs mv mp)).1 + 1 ∧
      regs' mAP = (candAfterMid (lv, lp) (bestOfRegs mv mp)).2 ∧
      (∀ r, CandMerge3Untouched r → regs' r = regs r) := by
  -- fetch facts for the nine middle-phase positions
  have hf : ∀ (k m : Nat) (instr : Instr), k < 9 →
      (candMerge3Mid E)[k]? = some instr → E + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hMid k hk, hget]
  have h0 : program[E]? = some (.move mAV mLV) :=
    hf 0 E _ (by omega) rfl (by omega)
  have h1 : program[E + 1]? = some (.move mAP mLP) :=
    hf 1 _ _ (by omega) rfl (by omega)
  have h2 : program[E + 2]? = some (.brNZ mMV (E + 4)) :=
    hf 2 _ _ (by omega) rfl (by omega)
  have h3 : program[E + 3]? = some (.brNZ fOne (E + 9)) :=
    hf 3 _ _ (by omega) rfl (by omega)
  have h4 : program[E + 4]? = some (.natLt mT mMV mAV) :=
    hf 4 _ _ (by omega) rfl (by omega)
  have h5 : program[E + 5]? = some (.brNZ mT (E + 7)) :=
    hf 5 _ _ (by omega) rfl (by omega)
  have h6 : program[E + 6]? = some (.brNZ fOne (E + 9)) :=
    hf 6 _ _ (by omega) rfl (by omega)
  have h7 : program[E + 7]? = some (.move mAV mMV) :=
    hf 7 _ _ (by omega) rfl (by omega)
  have h8 : program[E + 8]? = some (.move mAP mMP) :=
    hf 8 _ _ (by omega) rfl (by omega)
  -- the two accumulator seeds, common to all three arms
  obtain ⟨r1, hr1⟩ : ∃ z : RegFile, z = regs.write mAV (lv + 1) := ⟨_, rfl⟩
  have hseed0 : RunsTo store program ⟨regs, E, false⟩
      ⟨r1, E + 1, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨regs, E, false⟩ : State)) rfl h0
    simpa [hr1, hLV] using h
  obtain ⟨r2, hr2⟩ : ∃ z : RegFile, z = r1.write mAP lp := ⟨_, rfl⟩
  have hseed1 : RunsTo store program ⟨r1, E + 1, false⟩
      ⟨r2, E + 2, false⟩ [] [Category.registerWrite] := by
    have h := RunsTo.move (store := store)
      (s := (⟨r1, E + 1, false⟩ : State)) rfl h1
    simpa [hr2, hr1, RegFile.write, mLV, mLP, mMV, mMP, mRV, mRP, mAV, mAP, mT, mU, fRes, fOne, hLP] using h
  have hr2AV : r2 mAV = lv + 1 := by simp [hr2, hr1, RegFile.write, mAV, mAP]
  have hr2AP : r2 mAP = lp := by simp [hr2, mAP]
  have hr2MV : r2 mMV = mv := by simp [hr2, hr1, RegFile.write, mMV, mAV, mAP, hMV]
  have hr2MP : r2 mMP = mp := by simp [hr2, hr1, RegFile.write, mMP, mAV, mAP, hMP]
  have hr2One : r2 fOne = 1 := by simp [hr2, hr1, RegFile.write, mAV, mAP, fOne, hOne]
  have hseed := hseed0.trans hseed1
  cases mv with
  | zero =>
      -- ARM (i): middle absent
      have hbr2 : RunsTo store program ⟨r2, E + 2, false⟩
          ⟨r2, E + 3, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_not_taken (store := store)
          (s := (⟨r2, E + 2, false⟩ : State)) rfl h2 (by simpa using hr2MV)
        simpa using h
      have hbr3 : RunsTo store program ⟨r2, E + 3, false⟩
          ⟨r2, E + 9, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_taken (store := store)
          (s := (⟨r2, E + 3, false⟩ : State)) rfl h3 (by simp [hr2One])
        simpa using h
      refine ⟨r2, ?_, ?_, ?_, ?_⟩
      · have hrun := (hseed.trans hbr2).trans hbr3
        simpa [candMerge3MidCats, bestOfRegs] using hrun
      · simpa [candAfterMid, bestOfRegs] using hr2AV
      · simpa [candAfterMid, bestOfRegs] using hr2AP
      · intro r hr
        obtain ⟨_, hAV, hAP, _, _⟩ := hr
        simp [hr2, hr1, RegFile.write, mAV, mAP, hAV, hAP]
  | succ m =>
      -- middle present: compare
      have hbr2 : RunsTo store program ⟨r2, E + 2, false⟩
          ⟨r2, E + 4, false⟩ [] [Category.branch] := by
        have h := RunsTo.brNZ_taken (store := store)
          (s := (⟨r2, E + 2, false⟩ : State)) rfl h2 (by simp [hr2MV])
        simpa using h
      obtain ⟨r3, hr3⟩ : ∃ z : RegFile, z = r2.write mT (if m + 1 < lv + 1 then 1 else 0) := ⟨_, rfl⟩
      have hlt : RunsTo store program ⟨r2, E + 4, false⟩
          ⟨r3, E + 5, false⟩ [] [Category.comparison] := by
        have h := RunsTo.natLt (store := store)
          (s := (⟨r2, E + 4, false⟩ : State)) rfl h4
        simpa [hr3, hr2MV, hr2AV] using h
      have hr3AV : r3 mAV = lv + 1 := by
        simp [hr3, RegFile.write, mAV, mT, hr2AV]
      have hr3AP : r3 mAP = lp := by simp [hr3, RegFile.write, mAP, mT, hr2AP]
      have hr3MV : r3 mMV = m + 1 := by simp [hr3, RegFile.write, mMV, mT, hr2MV]
      have hr3MP : r3 mMP = mp := by simp [hr3, RegFile.write, mMP, mT, hr2MP]
      have hr3One : r3 fOne = 1 := by simp [hr3, RegFile.write, mT, fOne, hr2One]
      have hmid := (hseed.trans hbr2).trans hlt
      by_cases hbetter : m < lv
      · -- ARM (ii): middle strictly better
        have hcond : r3 mT = 1 := by
          rw [hr3, RegFile.write_same]
          exact if_pos (by omega)
        have hbr5 : RunsTo store program ⟨r3, E + 5, false⟩
            ⟨r3, E + 7, false⟩ [] [Category.branch] := by
          have h := RunsTo.brNZ_taken (store := store)
            (s := (⟨r3, E + 5, false⟩ : State)) rfl h5 (by simp [hcond])
          simpa using h
        obtain ⟨r4, hr4⟩ : ∃ z : RegFile, z = r3.write mAV (m + 1) := ⟨_, rfl⟩
        have hmv7 : RunsTo store program ⟨r3, E + 7, false⟩
            ⟨r4, E + 8, false⟩ [] [Category.registerWrite] := by
          have h := RunsTo.move (store := store)
            (s := (⟨r3, E + 7, false⟩ : State)) rfl h7
          simpa [hr4, hr3MV] using h
        obtain ⟨r5, hr5⟩ : ∃ z : RegFile, z = r4.write mAP mp := ⟨_, rfl⟩
        have hmv8 : RunsTo store program ⟨r4, E + 8, false⟩
            ⟨r5, E + 9, false⟩ [] [Category.registerWrite] := by
          have h := RunsTo.move (store := store)
            (s := (⟨r4, E + 8, false⟩ : State)) rfl h8
          simpa [hr5, hr4, RegFile.write, mLV, mLP, mMV, mMP, mRV, mRP, mAV, mAP, mT, mU, fRes, fOne, hr3MP] using h
        refine ⟨r5, ?_, ?_, ?_, ?_⟩
        · have hrun := ((hmid.trans hbr5).trans hmv7).trans hmv8
          have harm :
              candMerge3MidCats (lv, lp) (bestOfRegs (m + 1) mp) =
                [ Category.registerWrite, Category.registerWrite
                , Category.branch, Category.comparison, Category.branch
                , Category.registerWrite, Category.registerWrite ] := by
            simp [candMerge3MidCats, bestOfRegs, hbetter]
          rw [harm]
          simpa using hrun
        · have hval : candAfterMid (lv, lp) (bestOfRegs (m + 1) mp)
              = (m, mp) := by
            simp [candAfterMid, bestOfRegs, bpCandidateBetter, hbetter]
          rw [hval]
          simp [hr5, hr4, RegFile.write, mAV, mAP]
        · have hval : candAfterMid (lv, lp) (bestOfRegs (m + 1) mp)
              = (m, mp) := by
            simp [candAfterMid, bestOfRegs, bpCandidateBetter, hbetter]
          rw [hval]
          simp [hr5, mAP]
        · intro r hr
          obtain ⟨_, hAV, hAP, hT, _⟩ := hr
          simp [hr5, hr4, hr3, hr2, hr1, RegFile.write, mAV, mAP, mT, hAV, hAP, hT]
      · -- ARM (iii): middle present, not better
        have hcond : r3 mT = 0 := by
          rw [hr3, RegFile.write_same]
          exact if_neg (by omega)
        have hbr5 : RunsTo store program ⟨r3, E + 5, false⟩
            ⟨r3, E + 6, false⟩ [] [Category.branch] := by
          have h := RunsTo.brNZ_not_taken (store := store)
            (s := (⟨r3, E + 5, false⟩ : State)) rfl h5 (by simp [hcond])
          simpa using h
        have hbr6 : RunsTo store program ⟨r3, E + 6, false⟩
            ⟨r3, E + 9, false⟩ [] [Category.branch] := by
          have h := RunsTo.brNZ_taken (store := store)
            (s := (⟨r3, E + 6, false⟩ : State)) rfl h6 (by simp [hr3One])
          simpa using h
        refine ⟨r3, ?_, ?_, ?_, ?_⟩
        · have hrun := (hmid.trans hbr5).trans hbr6
          have harm :
              candMerge3MidCats (lv, lp) (bestOfRegs (m + 1) mp) =
                [ Category.registerWrite, Category.registerWrite
                , Category.branch, Category.comparison, Category.branch
                , Category.branch ] := by
            simp [candMerge3MidCats, bestOfRegs, hbetter]
          rw [harm]
          simpa using hrun
        · have hval : candAfterMid (lv, lp) (bestOfRegs (m + 1) mp)
              = (lv, lp) := by
            simp [candAfterMid, bestOfRegs, bpCandidateBetter, hbetter]
          rw [hval]
          exact hr3AV
        · have hval : candAfterMid (lv, lp) (bestOfRegs (m + 1) mp)
              = (lv, lp) := by
            simp [candAfterMid, bestOfRegs, bpCandidateBetter, hbetter]
          rw [hval]
          exact hr3AP
        · intro r hr
          obtain ⟨_, hAV, hAP, hT, _⟩ := hr
          simp [hr3, hr2, hr1, RegFile.write, mAV, mAP, mT, hAV, hAP, hT]

/--
The right phase and the close epilogue: fold the OCCUPIED right candidate
in if strictly better, then emit `bpCandidateClose?` into `fRes`.
-/
theorem candMerge3RightClose_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hRight : HostedAt program (E + 9) (candMerge3Right E))
    (hClose : HostedAt program (E + 14) candMerge3Close)
    (regs : RegFile) (acc : Nat × Nat) (rv rp : Nat)
    (hOne : regs fOne = 1)
    (hAV : regs mAV = acc.1 + 1) (hAP : regs mAP = acc.2)
    (hRV : regs mRV = rv + 1) (hRP : regs mRP = rp) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E + 9, false⟩ ⟨regs', E + 16, false⟩ []
        (candMerge3RightCats acc (rv, rp) ++ candMerge3CloseCats) ∧
      regs' mAV = (bpCandidateBetter acc (rv, rp)).1 + 1 ∧
      regs' mAP = (bpCandidateBetter acc (rv, rp)).2 ∧
      regs' fRes = (bpCandidateBetter acc (rv, rp)).2 - 1 ∧
      (∀ r, CandMerge3Untouched r → regs' r = regs r) := by
  have hfR : ∀ (k m : Nat) (instr : Instr), k < 5 →
      (candMerge3Right E)[k]? = some instr → E + 9 + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hRight k hk, hget]
  have h9 : program[E + 9]? = some (.natLt mU mRV mAV) :=
    hfR 0 (E + 9) _ (by omega) rfl (by omega)
  have h10 : program[E + 10]? = some (.brNZ mU (E + 12)) :=
    hfR 1 _ _ (by omega) rfl (by omega)
  have h11 : program[E + 11]? = some (.brNZ fOne (E + 14)) :=
    hfR 2 _ _ (by omega) rfl (by omega)
  have h12 : program[E + 12]? = some (.move mAV mRV) :=
    hfR 3 _ _ (by omega) rfl (by omega)
  have h13 : program[E + 13]? = some (.move mAP mRP) :=
    hfR 4 _ _ (by omega) rfl (by omega)
  have hfC : ∀ (k m : Nat) (instr : Instr), k < 2 →
      candMerge3Close[k]? = some instr → E + 14 + k = m →
      program[m]? = some instr := by
    intro k m instr hk hget hm
    rw [← hm, hClose k hk, hget]
  have h14 : program[E + 14]? = some (.const mT 1) :=
    hfC 0 (E + 14) _ (by omega) rfl (by omega)
  have h15 : program[E + 15]? = some (.sub fRes mAP mT) :=
    hfC 1 _ _ (by omega) rfl (by omega)
  -- the comparison, common to both arms
  obtain ⟨q1, hq1⟩ : ∃ z : RegFile, z = regs.write mU (if rv + 1 < acc.1 + 1 then 1 else 0) := ⟨_, rfl⟩
  have hcmp : RunsTo store program ⟨regs, E + 9, false⟩
      ⟨q1, E + 10, false⟩ [] [Category.comparison] := by
    have h := RunsTo.natLt (store := store)
      (s := (⟨regs, E + 9, false⟩ : State)) rfl h9
    simpa [hq1, hRV, hAV] using h
  have hq1AV : q1 mAV = acc.1 + 1 := by simp [hq1, RegFile.write, mAV, mU, hAV]
  have hq1AP : q1 mAP = acc.2 := by simp [hq1, RegFile.write, mAP, mU, hAP]
  have hq1RV : q1 mRV = rv + 1 := by simp [hq1, RegFile.write, mRV, mU, hRV]
  have hq1RP : q1 mRP = rp := by simp [hq1, RegFile.write, mRP, mU, hRP]
  have hq1One : q1 fOne = 1 := by simp [hq1, RegFile.write, mU, fOne, hOne]
  -- the close epilogue, common to both arms, from any state holding `mAP`
  have hcloseRun : ∀ (q : RegFile) (pos : Nat), q mAP = pos →
      ∃ q' : RegFile,
        RunsTo store program ⟨q, E + 14, false⟩ ⟨q', E + 16, false⟩ []
          candMerge3CloseCats ∧
        q' mAV = q mAV ∧ q' mAP = pos ∧ q' fRes = pos - 1 ∧
        (∀ r, CandMerge3Untouched r → q' r = q r) := by
    intro q pos hpos
    obtain ⟨q2, hq2⟩ : ∃ z : RegFile, z = q.write mT 1 := ⟨_, rfl⟩
    have hc1 : RunsTo store program ⟨q, E + 14, false⟩
        ⟨q2, E + 15, false⟩ [] [Category.registerWrite] := by
      have h := RunsTo.const (store := store)
        (s := (⟨q, E + 14, false⟩ : State)) rfl h14
      simpa [hq2] using h
    obtain ⟨q3, hq3⟩ : ∃ z : RegFile, z = q2.write fRes (pos - 1) := ⟨_, rfl⟩
    have hc2 : RunsTo store program ⟨q2, E + 15, false⟩
        ⟨q3, E + 16, false⟩ [] [Category.arithmetic] := by
      have h := RunsTo.sub (store := store)
        (s := (⟨q2, E + 15, false⟩ : State)) rfl h15
      simpa [hq3, hq2, RegFile.write, mLV, mLP, mMV, mMP, mRV, mRP, mAV, mAP, mT, mU, fRes, fOne, hpos] using h
    refine ⟨q3, ?_, ?_, ?_, ?_, ?_⟩
    · simpa [candMerge3CloseCats] using hc1.trans hc2
    · simp [hq3, hq2, RegFile.write, mAV, mT, fRes]
    · simp [hq3, hq2, RegFile.write, mAP, mT, fRes, hpos]
    · simp [hq3, fRes]
    · intro r hr
      obtain ⟨hRes, _, _, hT, _⟩ := id hr
      simp [hq3, hq2, RegFile.write, mT, fRes, hRes, hT]
  by_cases hbetter : rv < acc.1
  · -- ARM (i): right strictly better
    have hcond : q1 mU = 1 := by
      rw [hq1, RegFile.write_same]
      exact if_pos (by omega)
    have hbr10 : RunsTo store program ⟨q1, E + 10, false⟩
        ⟨q1, E + 12, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨q1, E + 10, false⟩ : State)) rfl h10 (by simp [hcond])
      simpa using h
    obtain ⟨q2, hq2⟩ : ∃ z : RegFile, z = q1.write mAV (rv + 1) := ⟨_, rfl⟩
    have hmv12 : RunsTo store program ⟨q1, E + 12, false⟩
        ⟨q2, E + 13, false⟩ [] [Category.registerWrite] := by
      have h := RunsTo.move (store := store)
        (s := (⟨q1, E + 12, false⟩ : State)) rfl h12
      simpa [hq2, hq1RV] using h
    obtain ⟨q3, hq3⟩ : ∃ z : RegFile, z = q2.write mAP rp := ⟨_, rfl⟩
    have hmv13 : RunsTo store program ⟨q2, E + 13, false⟩
        ⟨q3, E + 14, false⟩ [] [Category.registerWrite] := by
      have h := RunsTo.move (store := store)
        (s := (⟨q2, E + 13, false⟩ : State)) rfl h13
      simpa [hq3, hq2, RegFile.write, mLV, mLP, mMV, mMP, mRV, mRP, mAV, mAP, mT, mU, fRes, fOne, hq1RP] using h
    have hq3AP : q3 mAP = rp := by simp [hq3, mAP]
    obtain ⟨q4, hq4run, hq4AV, hq4AP, hq4Res, hq4pres⟩ :=
      hcloseRun q3 rp hq3AP
    have hval : bpCandidateBetter acc (rv, rp) = (rv, rp) := by
      simp [bpCandidateBetter, hbetter]
    refine ⟨q4, ?_, ?_, ?_, ?_, ?_⟩
    · have hrun := (((hcmp.trans hbr10).trans hmv12).trans hmv13).trans
        hq4run
      have harm : candMerge3RightCats acc (rv, rp) =
          [ Category.comparison, Category.branch, Category.registerWrite
          , Category.registerWrite ] := by
        simp [candMerge3RightCats, hbetter]
      rw [harm]
      simpa using hrun
    · rw [hval, hq4AV]
      simp [hq3, hq2, RegFile.write, mAV, mAP]
    · rw [hval]; exact hq4AP
    · rw [hval]; exact hq4Res
    · intro r hr
      obtain ⟨hRes, hAVr, hAPr, hT, hU⟩ := id hr
      rw [hq4pres r hr]
      simp [hq3, hq2, hq1, RegFile.write, mAV, mAP, mU, hAVr, hAPr, hU]
  · -- ARM (ii): right not better
    have hcond : q1 mU = 0 := by
      rw [hq1, RegFile.write_same]
      exact if_neg (by omega)
    have hbr10 : RunsTo store program ⟨q1, E + 10, false⟩
        ⟨q1, E + 11, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_not_taken (store := store)
        (s := (⟨q1, E + 10, false⟩ : State)) rfl h10 (by simp [hcond])
      simpa using h
    have hbr11 : RunsTo store program ⟨q1, E + 11, false⟩
        ⟨q1, E + 14, false⟩ [] [Category.branch] := by
      have h := RunsTo.brNZ_taken (store := store)
        (s := (⟨q1, E + 11, false⟩ : State)) rfl h11 (by simp [hq1One])
      simpa using h
    obtain ⟨q4, hq4run, hq4AV, hq4AP, hq4Res, hq4pres⟩ :=
      hcloseRun q1 acc.2 hq1AP
    have hval : bpCandidateBetter acc (rv, rp) = acc := by
      simp [bpCandidateBetter, hbetter]
    refine ⟨q4, ?_, ?_, ?_, ?_, ?_⟩
    · have hrun := ((hcmp.trans hbr10).trans hbr11).trans hq4run
      have harm : candMerge3RightCats acc (rv, rp) =
          [Category.comparison, Category.branch, Category.branch] := by
        simp [candMerge3RightCats, hbetter]
      rw [harm]
      simpa using hrun
    · rw [hval, hq4AV]; exact hq1AV
    · rw [hval]; exact hq4AP
    · rw [hval]; exact hq4Res
    · intro r hr
      obtain ⟨hRes, hAVr, hAPr, hT, hU⟩ := id hr
      rw [hq4pres r hr]
      simp [hq1, RegFile.write, mU, hU]

/--
EXACT SIMULATION OF THE THREE-WAY MERGE.

The block runs from `E` to `E + 16` on all six control paths, emits NO
read event, charges the route-selected category log, and leaves

* the accumulator pair holding `bpCandidateMerge3?` in biased form, and
* `fRes` holding the `bpCandidateClose?` payload

for the route's own merge function applied to the DECODED register
contents.  The left and right candidates are taken occupied, which is
what the route supplies (`bpFringeCandGlobal_isSome`).
-/
theorem candMerge3_runsTo
    (store : ReadStore) {program : E1Machine.Program} {E : Nat}
    (hHost : HostedAt program E (candMerge3 E))
    (regs : RegFile) (lv lp mv mp rv rp : Nat)
    (hOne : regs fOne = 1)
    (hLV : regs mLV = lv + 1) (hLP : regs mLP = lp)
    (hMV : regs mMV = mv) (hMP : regs mMP = mp)
    (hRV : regs mRV = rv + 1) (hRP : regs mRP = rp) :
    ∃ regs' : RegFile,
      RunsTo store program ⟨regs, E, false⟩ ⟨regs', E + 16, false⟩ []
        (candMerge3Cats (lv, lp) (bestOfRegs mv mp) (rv, rp)) ∧
      bestOfRegs (regs' mAV) (regs' mAP) =
        bpCandidateMerge3? (some (lv, lp)) (bestOfRegs mv mp)
          (some (rv, rp)) ∧
      some (regs' fRes) =
        bpCandidateClose?
          (bpCandidateMerge3? (some (lv, lp)) (bestOfRegs mv mp)
            (some (rv, rp))) ∧
      (∀ r, CandMerge3Untouched r → regs' r = regs r) := by
  obtain ⟨hMid, hRight, hClose⟩ := candMerge3_hosting hHost
  obtain ⟨regs1, hrun1, hAV1, hAP1, hpres1⟩ :=
    candMerge3Mid_runsTo store hMid regs lv lp mv mp hOne hLV hLP hMV hMP
  have hOne1 : regs1 fOne = 1 := by
    rw [hpres1 fOne (by decide)]; exact hOne
  have hRV1 : regs1 mRV = rv + 1 := by
    rw [hpres1 mRV (by decide)]; exact hRV
  have hRP1 : regs1 mRP = rp := by
    rw [hpres1 mRP (by decide)]; exact hRP
  obtain ⟨regs2, hrun2, hAV2, hAP2, hRes2, hpres2⟩ :=
    candMerge3RightClose_runsTo store hRight hClose regs1
      (candAfterMid (lv, lp) (bestOfRegs mv mp)) rv rp
      hOne1 hAV1 hAP1 hRV1 hRP1
  refine ⟨regs2, ?_, ?_, ?_, ?_⟩
  · have hrun := hrun1.trans hrun2
    simpa [candMerge3Cats, List.append_assoc] using hrun
  · rw [bpCandidateMerge3?_some_left_right, hAV2, hAP2, bestOfRegs_succ]
  · rw [bpCandidateMerge3?_some_left_right, hRes2]
    simp [bpCandidateClose?]
  · intro r hr
    rw [hpres2 r hr, hpres1 r hr]

/-! ## ANTI-VACUITY: the six paths EXECUTE onto distinguishable halts

`candMerge3_runsTo` is a simulation theorem, and a reader is entitled to
ask whether its six arms are ever actually taken -- a block that
collapsed two arms would still support a simulation theorem, just one whose
case split was decorative.

This section RUNS the block rather than merely hosting it: `run` is
applied to six concrete register files, one per control path, and the
outcomes are observed as numerals.  The paths are separated by BOTH
observables the machine offers:

* the MODELED STEP COUNT (`10, 11, 13, 14, 12, 13`), which alone
  separates five of the six; and
* the CLOSE PAYLOAD in `fRes` (`99, 200, 201, 302, 103, 304`), pairwise
  distinct, which separates the two 13-step paths.

Concrete failures these numerals reject: testing `natLe` instead of
`natLt` at either comparison site collapses the tie behaviour and changes
`fRes`; dropping the `middle?` occupancy test at `E+2` makes paths 1/2
read an unoccupied middle register and changes both observables; a merge
that returned the accumulator VALUE rather than its POSITION would report
`4`/`2` rather than the position-derived payloads.

Every run also halts with an EMPTY read log, which is the executed form
of `candMerge3_readFree` and matches the route, whose epilogue rides a
`TraceResult.map` and contributes no trace event.
-/

/-- Witness store.  A read-free block cannot consult it; the empty store
makes that testable rather than assumed. -/
def witnessStore : ReadStore := ⟨fun _ _ => none⟩

/-- Witness program: the block at base `0`, then `halt`. -/
def candMerge3Witness : E1Machine.Program := candMerge3 0 ++ [.halt]

/-- The witness program hosts the block at base `0`. -/
theorem candMerge3Witness_hosts :
    HostedAt candMerge3Witness 0 (candMerge3 0) :=
  HostedAt.append_left (hostedAt_self candMerge3Witness)

/-- Register file for one path: the house constant `1` in `fOne`, the two
fringe candidates occupied (`+1` bias), the middle candidate as given. -/
def witnessRegs (lv lp mv mp rv rp : Nat) : RegFile :=
  RegFile.write (RegFile.write (RegFile.write (RegFile.write
    (RegFile.write (RegFile.write (RegFile.write
      (fun _ => 0) fOne 1) mLV (lv + 1)) mLP lp) mMV mv) mMP mp)
        mRV (rv + 1)) mRP rp

/-- The observable outcome of running the witness on one path: exit pc,
halted flag, modeled steps, close payload, read log. -/
def witnessOutcome (lv lp mv mp rv rp : Nat) :
    Nat × Bool × Nat × Nat × List TraceEvent :=
  let r := run witnessStore candMerge3Witness 32
    ⟨witnessRegs lv lp mv mp rv rp, 0, false⟩
  (r.final.pc, r.final.halted, r.steps, r.final.regs fRes, r.readLog)

/-- PATH 1: middle absent, right not better. -/
theorem candMerge3Witness_path1 :
    witnessOutcome 5 100 0 0 9 200 = (16, true, 10, 99, []) := rfl

/-- PATH 2: middle absent, right strictly better. -/
theorem candMerge3Witness_path2 :
    witnessOutcome 5 101 0 0 2 201 = (16, true, 11, 200, []) := rfl

/-- PATH 3: middle present and strictly better, right not better. -/
theorem candMerge3Witness_path3 :
    witnessOutcome 5 102 4 202 9 302 = (16, true, 13, 201, []) := rfl

/-- PATH 4: middle present and strictly better, right strictly better. -/
theorem candMerge3Witness_path4 :
    witnessOutcome 5 103 4 203 1 303 = (16, true, 14, 302, []) := rfl

/-- PATH 5: middle present and NOT better, right not better. -/
theorem candMerge3Witness_path5 :
    witnessOutcome 5 104 8 204 9 304 = (16, true, 12, 103, []) := rfl

/-- PATH 6: middle present and NOT better, right strictly better. -/
theorem candMerge3Witness_path6 :
    witnessOutcome 5 105 8 205 1 305 = (16, true, 13, 304, []) := rfl

/-- The six executed paths are PAIRWISE DISTINGUISHABLE on the
`(modeled steps, close payload)` pair.  This is the statement that would
fail if any two control paths collapsed. -/
theorem candMerge3Witness_paths_distinguishable :
    let obs := fun (o : Nat × Bool × Nat × Nat × List TraceEvent) =>
      (o.2.2.1, o.2.2.2.1)
    [ obs (witnessOutcome 5 100 0 0 9 200)
    , obs (witnessOutcome 5 101 0 0 2 201)
    , obs (witnessOutcome 5 102 4 202 9 302)
    , obs (witnessOutcome 5 103 4 203 1 303)
    , obs (witnessOutcome 5 104 8 204 9 304)
    , obs (witnessOutcome 5 105 8 205 1 305) ].Nodup := by decide

/-- Executed form of `candMerge3_readFree`: every path halts having read
nothing. -/
theorem candMerge3Witness_readLogs_empty :
    [ (witnessOutcome 5 100 0 0 9 200).2.2.2.2
    , (witnessOutcome 5 101 0 0 2 201).2.2.2.2
    , (witnessOutcome 5 102 4 202 9 302).2.2.2.2
    , (witnessOutcome 5 103 4 203 1 303).2.2.2.2
    , (witnessOutcome 5 104 8 204 9 304).2.2.2.2
    , (witnessOutcome 5 105 8 205 1 305).2.2.2.2 ]
      = [[], [], [], [], [], []] := rfl

end E1CandMerge3
end WordRAM
end RMQ
