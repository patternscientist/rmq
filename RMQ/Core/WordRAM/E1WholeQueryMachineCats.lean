import RMQ.Core.WordRAM.E1WholeQueryRankPositive
import RMQ.Core.WordRAM.E1WholeQueryCats

/-!
# THE MACHINE'S WHOLE-QUERY STAGE RECORD, AND THE CATEGORY ACCOUNTING

`E1WholeQueryCats.lean` predicts the machine's whole-query category log from
the ROUTE, as a function of the route's branch classification, with the
per-stage charges left as parameters.  This module supplies the instantiation
the real machine actually charges and PROVES the prediction, branch by branch,
against the executed run theorems.

**WHY THIS IS NOT FITTING THE CATEGORY FUNCTION TO THE MACHINE.**  The order
matters and it is the right way round: `wholeQueryBranchCats` was written
first, from the route, and it is NOT edited here.  What is written here is an
`S`, and an `S` cannot make a false control structure true — the record has
one field per stage and `wholeQueryBranchCats` fixes which fields appear, in
which order, on which branch.  When the two disagreed, the disagreement was
reported and the RECORD was changed under a coordinator ruling
(DD-20260719-206, DD-20260719-208), not papered over by an `S`.

**THE LCA-RUN CATS ARE A PARAMETER, FOLLOWING `crossBlockArmCats`.**  The
close/LCA leg's charge differs between the same-block and the cross-block arm,
and the cross arm's whole-query execution is not written
(`E1_LIVE_STATE.md` §10f).  Rather than assert a cross-arm charge that nothing
executes, `wholeQueryMachineStageCats` takes `lcaRunCats` as a PARAMETER —
exactly the precedent `crossBlockArmCats` (`E1CrossBlockArm.lean:1088`) sets by
taking `interiorCats` as a parameter for the same reason.  The same-block
instantiation is supplied and proved; the cross one is left open rather than
guessed.

**WHAT IS PROVED HERE.**  Three of the four route branches, which is exactly
the set that runs from `initialState` to halted today:

* `.leftSelectNone` and `.rightSelectNone` — for EVERY `lcaRunCats`, since
  neither branch's log mentions the LCA leg;
* `.full` on the same-block arm, at `sameBlockLcaRunCats`.

The `.lcaNone` branch is not here: it is unreachable on the same-block arm by
proof (`E1WholeQueryLcaNone.lean:145`) and its cross-arm status is open.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open E1SelectDispatch
open E1SelectBridge
open E1RankBlock
open E1SameBlockArm
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-! ## The machine's per-stage charges -/

/--
The stage charges the whole-query machine actually incurs, read off the three
executed run theorems in `E1WholeQueryProgram.lean`.

`lcaRunCats` is a parameter for the reason given in the module note: the
close/LCA leg's charge is arm-dependent and only the same-block arm is
executed.  Every other field is a fixed list or a function of the position the
stage is indexed by — no numeral is asserted, and nothing here is a count.
-/
def wholeQueryMachineStageCats (shape : Cartesian.CartesianShape)
    (lcaRunCats : Nat → Nat → List Category) : WholeQueryStageCats where
  prologue := guardAcceptCats ++ [Category.registerWrite]
  select := fun idx =>
    selectCloseCats (wholeQuerySelData shape)
      concreteBPNativeSelectCloseTraceSegmentLayout
      concreteBPNativeRankCloseTraceSegmentBase
      concreteBPNativeSelectChunkTraceSegment
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (bpFringeChunkBits shape.bpCode.length) idx
  selectJoin := [Category.registerWrite, Category.arithmetic]
  lcaRun := lcaRunCats
  lcaSkippedLeftMiss := [Category.comparison, Category.branch]
  lcaSkippedRightMiss :=
    [Category.comparison, Category.branch, Category.comparison, Category.branch]
  rankJoin := [Category.registerWrite, Category.arithmetic]
  rankRun := fun pos =>
    rankCloseHitCats
      (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
        ((builtRelativeSplitBPCloseRankData shape).wordOffset pos))
  rankSkipped := []
  outputSome := [Category.registerWrite, Category.control]
  outputNone := [Category.registerWrite, Category.control]

/--
The close/LCA leg's charge on the SAME-BLOCK arm: the two select tests, the
two address arithmetic ticks, the dispatch, and the same-block leg itself.
-/
def sameBlockLcaRunCats (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : List Category :=
  [Category.comparison, Category.branch, Category.comparison, Category.branch,
      Category.arithmetic, Category.arithmetic] ++
    (E1CloseDispatch.closeDispatchCats ++
      E1SameBlockLeg.sameBlockLegCats shape
        concreteBPNativeFringeChunkTraceSegment
        (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose rightClose)

/-! ## The accounting, branch by branch -/

/--
THE LEFT-SELECT-MISS BRANCH'S CHARGE IS THE ROUTE-INDEXED PREDICTION.

Holds for EVERY `lcaRunCats`, which is the independence the route's control
structure asserts on this branch: the log does not mention the LCA leg, so it
cannot depend on it.
-/
theorem wholeQueryProgram_runsTo_leftSelectNone_cats
    (shape : Cartesian.CartesianShape) {n left right : Nat}
    (lcaRunCats : Nat → Nat → List Category)
    (hlt : left < right) (hbound : right ≤ n)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        none) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n) (initialState left right)
          ⟨regsF, 5645, true⟩
        (wholeQueryBranchTrace shape left right .leftSelectNone)
        (wholeQueryBranchCats (wholeQueryMachineStageCats shape lcaRunCats)
          left right .leftSelectNone) ∧
      decodePacket (regsF regOut) =
        wholeQueryBranchValue shape .leftSelectNone := by
  obtain ⟨regsF, hrun, hout⟩ :=
    wholeQueryProgram_runsTo_leftSelectNone shape hlt hbound hleftVal
  refine ⟨regsF, ?_, hout⟩
  simpa [wholeQueryBranchCats, wholeQueryMachineStageCats,
    List.append_assoc] using hrun

/--
THE RIGHT-SELECT-MISS BRANCH'S CHARGE IS THE ROUTE-INDEXED PREDICTION, AND IT
IS A DIFFERENT LIST FROM THE LEFT-MISS ONE.

This is the branch DD-20260719-208 split the skip arm for.  Under the previous
record the two select-miss cases of `wholeQueryBranchCats` were the same term,
so this theorem and its left-miss sibling could not both have been true.
-/
theorem wholeQueryProgram_runsTo_rightSelectNone_cats
    (shape : Cartesian.CartesianShape) {n left right cl : Nat}
    (lcaRunCats : Nat → Nat → List Category)
    (hlt : left < right) (hbound : right ≤ n)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = none) :
    ∃ regsF : RegFile,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n) (initialState left right)
          ⟨regsF, 5645, true⟩
        (wholeQueryBranchTrace shape left right (.rightSelectNone cl))
        (wholeQueryBranchCats (wholeQueryMachineStageCats shape lcaRunCats)
          left right (.rightSelectNone cl)) ∧
      decodePacket (regsF regOut) =
        wholeQueryBranchValue shape (.rightSelectNone cl) := by
  obtain ⟨regsF, hrun, hout⟩ :=
    wholeQueryProgram_runsTo_rightSelectNone shape hlt hbound hleftVal hrightVal
  refine ⟨regsF, ?_, hout⟩
  simpa [wholeQueryBranchCats, wholeQueryMachineStageCats,
    List.append_assoc] using hrun

/--
THE FULL BRANCH ON THE SAME-BLOCK ARM: RECEIPT, CHARGE AND VALUE, ALL THREE
IN THE ROUTE'S OWN VOCABULARY.

This is `wholeQueryProgram_runsTo_sameBlock_routeReceipt`
(`E1WholeQuerySameBlockRoute.lean:103`) with its two remaining machine-side
spellings removed:

* the CHARGE, which that theorem states as the machine's explicit
  concatenation, becomes `wholeQueryBranchCats` at the machine's own `S`;
* the VALUE, which that theorem deliberately left as
  `regsF regOut = rank.value` because `decodePacket … = wholeQueryBranchValue …`
  did not follow without `rank.value ≠ 0`, becomes the route's form — the
  side condition is now PROVED (DD-20260719-207), not assumed.

The extra hypothesis over that theorem is `right ≤ shape.size`, which is
`ValidRange`'s own second conjunct transported through the shape.  Nothing is
assumed that the public surface does not already assume, and neither
`decodePacket` nor `wholeQueryBranchValue` is weakened.
-/
theorem wholeQueryProgram_runsTo_sameBlock_routeCats
    (shape : Cartesian.CartesianShape) {n left right cl cr : Nat}
    (hlt : left < right) (hbound : right ≤ n)
    (hshape : right ≤ shape.size)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    ∃ (regsF : RegFile) (answerClose : Nat),
      wholeQueryBranch shape left right = .full cl cr answerClose ∧
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n) (initialState left right)
          ⟨regsF, 5643, true⟩
        (wholeQueryBranchTrace shape left right (.full cl cr answerClose))
        (wholeQueryBranchCats
          (wholeQueryMachineStageCats shape (sameBlockLcaRunCats shape))
          left right (.full cl cr answerClose)) ∧
      decodePacket (regsF regOut) =
        wholeQueryBranchValue shape (.full cl cr answerClose) := by
  obtain ⟨regsF, answerClose, hbranch, hrun, hout⟩ :=
    wholeQueryProgram_runsTo_sameBlock_routeReceipt shape hlt hbound hleftVal
      hrightVal hsame
  refine ⟨regsF, answerClose, hbranch, ?_, ?_⟩
  · simpa [wholeQueryBranchCats, wholeQueryMachineStageCats,
      sameBlockLcaRunCats, List.append_assoc] using hrun
  · rw [hout, ← concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]
    exact decodePacket_eq_wholeQueryBranchValue_of_branch hlt hshape hbranch

end E1Query
end WordRAM
end RMQ
