import RMQ.Core.WordRAM.E1WholeQueryMachineCats
import RMQ.Core.WordRAM.E1InteriorTraceLadder

/-!
# THE FOURTH BRANCH: THE `.full` PATH ON THE CROSS-BLOCK ARM

Three of the four route branches ran from `initialState` to halted before this
module; the fourth — `.full` on the cross-block arm — did not.  This supplies
it, and then identifies its value with the route's, which is what
`E1_LIVE_STATE.md` §10f named as unwritten.

**THE MIRROR WAS MECHANICAL AND THAT IS A FINDING, NOT A SAVING.**
`closeLcaProgramAt_runsTo_cross` (`E1WholeQueryCloseLca.lean:258`) already
existed as the exact twin of `closeLcaProgramAt_runsTo_same`, and the
same-block whole-query proof consumes its twin in one `obtain`.  So the
whole-query cross run is that proof with one lemma swapped.  Recorded because
two briefs budgeted the cross arm as a lane of work; the arm-level machinery
was in place and only the composition was missing.

**WHAT IS ACTUALLY OWED HERE, AS OPPOSED TO ASSUMED.**  The machine's cross
arm carries its interior UNGUARDED — `closeLcaProgramAt_runsTo_cross` names
`⟨dispatchRouteValue …, dispatchEvents …⟩` directly — while the route's cross
object guards it, `if leftBlock + 1 < rightBlock then … else pure none`
(`ChargedFringeTrace.lean:940`).  The two agree only because the guard
COLLAPSES: when `¬(lb + 1 < rb)` the count `rb - lb - 1` is `0` in `Nat`, and
the dispatch's `count = 0` arm IS `pure none` with an empty read log.  That
collapse is proved below rather than assumed, and it is the one place this
composition could have hidden a defect.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open E1SelectDispatch
open E1SelectBridge
open E1RankBlock
open E1SameBlockArm
open E1InteriorDispatchCompose
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-- The close/LCA leg's charge on the CROSS-BLOCK arm, read off
`closeLcaProgramAt_runsTo_cross`. -/
def crossBlockLcaRunCats (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : List Category :=
  [Category.comparison, Category.branch, Category.comparison, Category.branch,
      Category.arithmetic, Category.arithmetic] ++
    (E1CloseDispatch.closeDispatchCats ++
      (E1CrossBlockArm.crossBlockArmCats shape
        concreteBPNativeFringeChunkTraceSegment
        (canonicalBPRelativeSummaryBlockSizeRaw shape)
        (dispatchCats shape
          (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
          (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
            leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
        (dispatchRouteValue shape
          (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
          (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
            leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1))
        leftClose rightClose ++
        [Category.registerWrite, Category.branch]))

/--
The machine's cross-block arm object at the canonical instantiation: the arm
spec with the canonical rank seed, the global read store, and the interior the
trace ladder identified (rung 7).  Named once so the run theorem below states
its receipt and value against ONE object rather than three copies of a
sixteen-line expression.
-/
def crossArmObject (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : WordRAM.TraceResult (Option Nat) :=
  E1CrossBlockArm.crossBlockArmSpec shape
    (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape)
    concreteBPNativeFringeChunkTraceSegment
    (concreteBPNativeSuccinctRMQGlobalReadStore shape)
    ⟨dispatchRouteValue shape
        (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
        (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
          leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1),
      dispatchEvents shape
        (leftClose / (RelativeRmm.canonicalLayout shape).blockSize + 1)
        (rightClose / (RelativeRmm.canonicalLayout shape).blockSize -
          leftClose / (RelativeRmm.canonicalLayout shape).blockSize - 1)⟩
    leftClose rightClose

/--
THE FOURTH BRANCH, EXECUTED: the `.full` path on the cross-block arm runs from
`initialState` to a halted state, with its charge already in the route's
`wholeQueryBranchCats` form.

The receipt and value are still in the MACHINE's vocabulary here — they name
`crossArmObject`.  Putting them in the route's vocabulary is the separate
identification below, and keeping the two steps apart is deliberate: it is
what makes the identification a theorem rather than a definition.
-/
theorem wholeQueryProgram_runsTo_crossBlock
    (shape : Cartesian.CartesianShape) {n left right cl cr : Nat}
    (hlt : left < right) (hbound : right ≤ n)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    ∃ (regsF : RegFile) (answerClose : Nat),
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n) (initialState left right)
          ⟨regsF, 5643, true⟩
        ((concreteBPNativeSelectCloseGlobalWordTraceResult shape left).trace ++
          (concreteBPNativeSelectCloseGlobalWordTraceResult shape
            (right - 1)).trace ++
          (crossArmObject shape cl cr).trace ++
          (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
            (answerClose + 1)).trace)
        (wholeQueryBranchCats
          (wholeQueryMachineStageCats shape (crossBlockLcaRunCats shape))
          left right (.full cl cr answerClose)) ∧
      some answerClose = (crossArmObject shape cl cr).value ∧
      regsF regOut =
        (concreteBPNativeChunkedRankCloseGlobalWordTraceResult shape
          (answerClose + 1)).value := by
  have hguard : HostedAt (wholeQueryProgram shape n) 0
      (guardBlock n (8 + (wholeQueryValidPath shape wholeQueryNoneExit).length)) :=
    programSkeleton_hosts_guardBlock n _
  have hvp : HostedAt (wholeQueryProgram shape n) 8
      (wholeQueryValidPath shape wholeQueryNoneExit) :=
    programSkeleton_hosts_validPath n _
  obtain ⟨hthrough, hout⟩ := wholeQueryValidPath_hosts_outputStage shape hvp
  obtain ⟨hprefix, hjoin, hcloseLca⟩ :=
    wholeQueryValidPathThroughLca_hosts_closeLca shape hthrough
  obtain ⟨regs2, hrunP, hT1, hV, hZ, hOne⟩ :=
    wholeQuerySelectPrefix_runsTo shape hguard hprefix hlt hbound
  rw [hleftVal] at hT1
  rw [hrightVal] at hV
  obtain ⟨regs3, hrunJ, hClose, hRight⟩ :=
    selectJoin_runsTo_hit shape hjoin regs2
      (packet_of_decodePacket_eq_some hT1)
      (packet_of_decodePacket_eq_some hV) hZ hOne
  obtain ⟨regs4, hrunC, hval, _hpres⟩ :=
    E1WholeQueryCloseLca.closeLcaProgramAt_runsTo_cross shape hcloseLca regs3
      hClose hRight hcross
  obtain ⟨regs5, hrunO, hout'⟩ :=
    wholeQueryOutputStage_runsTo shape hout regs4
  refine ⟨regs5, regs4 fRes, ?_, hval, hout'⟩
  have hpc : E1WholeQueryCloseLca.closeLcaExit 827 + 63 = 5643 := by
    simp [E1WholeQueryCloseLca.closeLcaExit]
  rw [hpc] at hrunO
  have htrans := ((hrunP.trans hrunJ).trans hrunC).trans hrunO
  simpa [wholeQueryBranchCats, wholeQueryMachineStageCats,
    crossBlockLcaRunCats, crossArmObject, List.append_assoc] using htrans

/-! ## The guard collapse -/

/--
THE ONE PLACE THIS COMPOSITION COULD HAVE HIDDEN A DEFECT.

The route's cross object guards its interior — `if leftBlock + 1 < rightBlock`
— while the machine's arm carries it unguarded.  They agree only because the
guard COLLAPSES on the else branch: `¬(bl + 1 < br)` forces `br - bl - 1 = 0`
in `Nat`, and the dispatch's `count = 0` arm is `pure none` with an EMPTY read
log.  So the machine emits nothing exactly where the route's guard emits
nothing.

Proved, not assumed.  Had the `count = 0` arm read anything — for instance had
it fallen through into `twoSpanBlock`'s unconditional head-level read — the
two sides would differ in their receipts and this equation would fail here,
which is the check that makes the unguarded machine object safe to use.
-/
theorem dispatchTraceResult_of_not_lt (shape : Cartesian.CartesianShape)
    {bl br : Nat} (h : ¬ (bl + 1 < br)) :
    (⟨dispatchRouteValue shape (bl + 1) (br - bl - 1),
      dispatchEvents shape (bl + 1) (br - bl - 1)⟩ :
        WordRAM.TraceResult (Option (Nat × Nat))) =
      WordRAM.TraceResult.pure none := by
  have hz : br - bl - 1 = 0 := by omega
  rw [hz]
  simp [dispatchRouteValue, dispatchEvents,
    E1InteriorDispatch.interiorRangeMin_of_count_zero,
    FlatStoreComputation.pure, WordRAM.TraceResult.pure]

/-! ## The arm-level identification -/

/--
**THE FOURTH BRANCH'S OBJECT IS THE ROUTE'S OBJECT.**  The machine's cross-arm
object and the route's `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
are ONE TERM on the cross arm — value and receipt together, not just the value.

This is the identification `E1_LIVE_STATE.md` §10f named as unwritten, and it
is the cross-arm counterpart of `lcaLeg_of_sameBlock`'s role in the same-block
bridge.  Every hop already existed; what was missing was the composition and
the guard collapse above.

The block-index spellings on the two sides differ — the route says
`blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) x`, the machine
says `x / (RelativeRmm.canonicalLayout shape).blockSize` — and they are the
SAME TERM: `blockOfClose bs c` is `c / bs` (`BlockLocal.lean:864`) and
`(canonicalLayout shape).blockSize` is `canonicalBPRelativeSummaryBlockSizeRaw shape`
by projection (`RelativeSummary.lean:1278`).  Checked rather than assumed,
because a mismatch here would have been invisible until the composed term was
elaborated.
-/
theorem crossArmObject_eq_routeLcaLeg (shape : Cartesian.CartesianShape)
    {cl cr : Nat}
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural shape cl cr =
      crossArmObject shape cl cr := by
  rw [lcaLeg_eq_withStore_at_globalReadStore,
    lcaLeg_of_crossBlock shape
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) cl cr hcross,
    lcaLeg_sameBlock_rankSeed_eq,
    E1CrossBlockArm.crossBlockArmSpec_eq]
  unfold crossArmObject
  congr 1
  by_cases hlt :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl + 1 <
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr
  · rw [if_pos hlt]
    exact
      E1InteriorTraceLadder.canonicalInterior_traceResult_eq_dispatch shape _ _
  · rw [if_neg hlt]
    exact (dispatchTraceResult_of_not_lt shape hlt).symm

/--
THE FOURTH BRANCH, ENTIRELY IN THE ROUTE'S VOCABULARY: receipt, charge and
value, with the branch itself derived rather than assumed.

This is the cross-arm counterpart of
`wholeQueryProgram_runsTo_sameBlock_routeCats`, and with it all four route
branches run from `initialState` to a halted state with all three clauses
stated against the route's own objects.
-/
theorem wholeQueryProgram_runsTo_crossBlock_routeCats
    (shape : Cartesian.CartesianShape) {n left right cl cr : Nat}
    (hlt : left < right) (hbound : right ≤ n)
    (hshape : right ≤ shape.size)
    (hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some cl)
    (hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some cr)
    (hcross :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cl ≠
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) cr) :
    ∃ (regsF : RegFile) (answerClose : Nat),
      wholeQueryBranch shape left right = .full cl cr answerClose ∧
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore shape)
          (wholeQueryProgram shape n) (initialState left right)
          ⟨regsF, 5643, true⟩
        (wholeQueryBranchTrace shape left right (.full cl cr answerClose))
        (wholeQueryBranchCats
          (wholeQueryMachineStageCats shape (crossBlockLcaRunCats shape))
          left right (.full cl cr answerClose)) ∧
      decodePacket (regsF regOut) =
        wholeQueryBranchValue shape (.full cl cr answerClose) := by
  obtain ⟨regsF, answerClose, hrun, hval, hout⟩ :=
    wholeQueryProgram_runsTo_crossBlock shape hlt hbound hleftVal hrightVal
      hcross
  have hlca :
      (concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
        shape cl cr).value = some answerClose := by
    rw [crossArmObject_eq_routeLcaLeg shape hcross]
    exact hval.symm
  have hbranch :=
    wholeQueryBranch_eq_full shape left right hleftVal hrightVal hlca
  refine ⟨regsF, answerClose, hbranch, ?_, ?_⟩
  · simpa [wholeQueryBranchTrace,
      crossArmObject_eq_routeLcaLeg shape hcross,
      concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq,
      List.append_assoc] using hrun
  · rw [hout, ← concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq]
    exact decodePacket_eq_wholeQueryBranchValue_of_branch hlt hshape hbranch

end E1Query
end WordRAM
end RMQ
