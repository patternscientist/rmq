import RMQ.Core.WordRAM.E1WholeQueryLcaNone

/-!
# THE SAME-BLOCK RECEIPT BRIDGE

**THE GAP THIS CLOSES.**  `wholeQueryProgram_runsTo_sameBlock`
(`E1WholeQueryProgram.lean:1034`) executes the `.full` branch on the
same-block arm from `initialState` to a halted state, but its receipt is in
the ARM's vocabulary -- it names
`bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore`
directly -- while the route names
`concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`.  The two
bridging rewrites both existed; the bridge itself did not.

**THE BRIDGE IS THREE REWRITES AND CARRIES ONE HYPOTHESIS, `hsame`, WHICH
IS THE ARM SELECTOR ITSELF.**

* `wholeQueryBranchTrace_full_machineObjects` (`E1WholeQueryObjects.lean:126`)
  puts the route's `.full` receipt in store-parametric form at the global
  store and swaps the rank leg;
* `lcaLeg_of_sameBlock` (`E1WholeQueryLcaLeg.lean:64`) selects the
  same-block arm under `hsame`;
* `lcaLeg_sameBlock_rankSeed_eq` (`E1WholeQueryLcaLeg.lean:132`) identifies
  the rank seed the two sides spell differently.

Nothing is reconciled here that was not already reconciled -- this supplies
the composition the scope note named as unwritten.

**WHAT IS AND IS NOT CLAIMED ABOUT THE VALUE.**  The run theorem below
carries its value clause in the MACHINE's form, `regsF regOut = rank.value`,
and does NOT claim `decodePacket (regsF regOut) = wholeQueryBranchValue …`.
That is deliberate and is the finding recorded in
`E1_LIVE_STATE.md` §10f: the two disagree when the rank value is `0`,
because `decodePacket 0 = none` (`E1QueryProgram.lean:96`) while the
route's `.full` value is `some (rank.value - 1)` UNCONDITIONALLY, and
`0 - 1 = 0` in `Nat`.  The obligation `rank.value ≠ 0` is real, is not
discharged anywhere in the tree, and is NOT assumed here.  Stating the
value clause in the machine's form is the honest option; weakening the
route's value or asserting the side condition would not be.
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

/-- **THE RECEIPT BRIDGE.**  The route's `.full` receipt, on the same-block
arm, written entirely in the objects `wholeQueryProgram_runsTo_sameBlock`
produces.

Positional: both sides are the same four-segment concatenation in the same
associativity, so this constrains every event in every position rather than
any aggregate. -/
theorem wholeQueryBranchTrace_full_sameBlock_machineObjects
    (shape : Cartesian.CartesianShape)
    (left right cl cr answerClose : Nat)
    (hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    wholeQueryBranchTrace shape left right (.full cl cr answerClose) =
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
        (concreteBPNativeSelectCloseGlobalWordTraceResult shape
          (right - 1)).trace ++
        (ConcreteCompactBPCloseLCADirectory.bpChunkedSameBlockCloseDecodedTraceResultWithRankSeedAtSegmentWithStore
          shape (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
          concreteBPNativeFringeChunkTraceSegment
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (canonicalBPRelativeSummaryBlockSizeRaw shape) cl cr).trace ++
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).trace := by
  rw [wholeQueryBranchTrace_full_machineObjects,
    lcaLeg_of_sameBlock shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      cl cr hsame,
    lcaLeg_sameBlock_rankSeed_eq]

/-- **THE SAME-BLOCK `.full` BRANCH, EXECUTED AGAINST THE ROUTE'S OWN
RECEIPT.**

This is `wholeQueryProgram_runsTo_sameBlock` with its receipt replaced by
`wholeQueryBranchTrace shape left right (wholeQueryBranch shape left right)`
-- the route's own object, computed by the route's own classifier, not a
machine-side paraphrase.  It is the same shape the two select-miss branches
already have.

**THE BRANCH IS NOT ASSUMED TO BE `.full`; IT IS DERIVED.**  The first
conjunct is `wholeQueryBranch shape left right = .full cl cr answerClose`,
supplied by `wholeQueryBranch_eq_full_of_sameBlock`
(`E1WholeQueryLcaNone.lean`), which in turn rests on the proof that
`.lcaNone` cannot fire on this arm.  So the receipt is stated at the branch
the route actually takes.

**THE VALUE CLAUSE IS IN THE MACHINE'S FORM, DELIBERATELY.**  See the
module header: `decodePacket (regsF regOut) = wholeQueryBranchValue …`
does NOT follow without `rank.value ≠ 0`, which is not proved anywhere in
the tree.  The clause below is what is actually established. -/
theorem wholeQueryProgram_runsTo_sameBlock_routeReceipt
    (shape : Cartesian.CartesianShape) {n left right cl cr : Nat}
    (hlt : left < right) (hbound : right ≤ n)
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
        (wholeQueryBranchTrace shape left right
          (.full cl cr answerClose))
        (guardAcceptCats ++
          ([Category.registerWrite] ++
            (selectCloseCats (wholeQuerySelData shape)
              concreteBPNativeSelectCloseTraceSegmentLayout
              concreteBPNativeRankCloseTraceSegmentBase
              concreteBPNativeSelectChunkTraceSegment
              (concreteBPNativeSuccinctRMQGlobalReadStore shape)
              (bpFringeChunkBits shape.bpCode.length) left ++
              ([Category.registerWrite, Category.arithmetic] ++
                selectCloseCats (wholeQuerySelData shape)
                  concreteBPNativeSelectCloseTraceSegmentLayout
                  concreteBPNativeRankCloseTraceSegmentBase
                  concreteBPNativeSelectChunkTraceSegment
                  (concreteBPNativeSuccinctRMQGlobalReadStore shape)
                  (bpFringeChunkBits shape.bpCode.length) (right - 1)))) ++
          ([Category.comparison, Category.branch, Category.comparison,
              Category.branch, Category.arithmetic, Category.arithmetic] ++
            ((E1CloseDispatch.closeDispatchCats ++
                E1SameBlockLeg.sameBlockLegCats shape
                  concreteBPNativeFringeChunkTraceSegment
                  (canonicalBPRelativeSummaryBlockSizeRaw shape) cl cr) ++
              ([Category.registerWrite, Category.arithmetic] ++
                (rankCloseHitCats
                    (bpWordChunkCount (bpFringeChunkBits shape.bpCode.length)
                      ((builtRelativeSplitBPCloseRankData shape).wordOffset
                        (answerClose + 1))) ++
                  [Category.registerWrite, Category.control]))))) ∧
      regsF regOut =
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).value := by
  obtain ⟨regsF, answerClose, hrun, hval, hout⟩ :=
    wholeQueryProgram_runsTo_sameBlock shape hlt hbound hleftVal hrightVal hsame
  refine ⟨regsF, answerClose, ?_, ?_, hout⟩
  · obtain ⟨a', ha'⟩ :=
      wholeQueryBranch_eq_full_of_sameBlock shape hlt hleftVal hrightVal hsame
    have hlca :
        (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
          shape cl cr).value = some answerClose := by
      rw [lcaLeg_eq_withStore_at_globalReadStore,
        lcaLeg_of_sameBlock shape
          (concreteBPNativeSuccinctRMQGlobalReadStore shape) cl cr hsame,
        lcaLeg_sameBlock_rankSeed_eq]
      exact hval.symm
    exact wholeQueryBranch_eq_full shape left right hleftVal hrightVal hlca
  · rw [wholeQueryBranchTrace_full_sameBlock_machineObjects shape left right
      cl cr answerClose hsame]
    exact hrun

end E1Query
end WordRAM
end RMQ
