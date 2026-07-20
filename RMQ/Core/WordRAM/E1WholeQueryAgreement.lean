import RMQ.Core.WordRAM.E1WholeQueryCrossRoute
import RMQ.Core.WordRAM.E1WholeQueryPublic

/-!
# `WholeQueryMachineAgrees`, DISCHARGED

Every piece the whole-query agreement needed is now in place, and this module
composes them.

**THE SELECT-MISS BRANCHES ARE NOT PROVED HERE BECAUSE THEY CANNOT HAPPEN.**
`wholeQueryBranch_ne_selectNone_of_bounds` (`E1WholeQueryRankPositive.lean:311`)
shows that on `left < right` and `right ≤ shape.size` — the public surface's
own hypothesis — the route ALWAYS takes `.full`.  The selects cannot miss on a
valid range because `bpCloseOfInorder?` is total below the shape's size
(`BPShape.lean:57`).  So the whole-query obligation on a valid range is the
`.full` branch's two arms, and both are executed.

**THE STAGE RECORD DISPATCHES ON THE ROUTE'S OWN CONDITION.**
`WholeQueryMachineAgrees` fixes ONE `S`, but the close/LCA leg charges
differently on the two arms.  `wholeQueryLcaRunCats` therefore branches on
`blockOfClose … leftClose = blockOfClose … rightClose` — which is the route's
own arm selector, the same condition
`lcaCloseTraceResultWithRankSeedAllSizeStructural` (`ChargedFringeWiring.lean:50`)
dispatches on.  It is a function of the route's branch conditions, not a
numeral, and not fitted to the machine.
-/

namespace RMQ
namespace WordRAM
namespace E1Query

open E1Machine
open RMQ.SuccinctSpace
open RMQ.SuccinctClose
open RMQ.SuccinctFinal

/-- The close/LCA leg's charge, on whichever arm the route's own block
condition selects. -/
def wholeQueryLcaRunCats (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : List Category :=
  if blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose then
    sameBlockLcaRunCats shape leftClose rightClose
  else
    crossBlockLcaRunCats shape leftClose rightClose

/-- The whole-query machine's stage record: the charges of `E1WholeQueryMachineCats`
with the arm-dispatching close/LCA leg. -/
def wholeQueryMachineS (shape : Cartesian.CartesianShape) : WholeQueryStageCats :=
  wholeQueryMachineStageCats shape (wholeQueryLcaRunCats shape)

/--
**THE WHOLE-QUERY AGREEMENT, DISCHARGED ON EVERY NONEMPTY IN-RANGE QUERY.**

All three clauses at once: the skeleton runs from `initialState` with exact
fuel to a halted state, its receipt is POSITIONALLY the route's whole-query
receipt, its charge is POSITIONALLY the route-indexed category log, and its
output packet decodes to the route's whole-query value.

Nothing is weakened to make this close.  In particular the value clause is the
real one — `decodePacket … = wholeQueryRouteValue …` — which was the
obstruction DD-20260719-205 reported and DD-20260719-207 discharged.
-/
theorem wholeQueryMachineAgrees_of_bounds (shape : Cartesian.CartesianShape)
    {n left right : Nat}
    (hlt : left < right) (hbound : right ≤ n) (hshape : right ≤ shape.size) :
    WholeQueryMachineAgrees (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      n (wholeQueryValidPath shape wholeQueryNoneExit)
      (wholeQueryMachineS shape) shape left right := by
  obtain ⟨leftClose, hlc⟩ :=
    bpCloseOfInorder?_some_of_lt shape (show left < shape.size by omega)
  obtain ⟨rightClose, hrc⟩ :=
    bpCloseOfInorder?_some_of_lt shape (show right - 1 < shape.size by omega)
  have hleftVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape left).value =
        some leftClose := by
    rw [selectCloseTrace_value_eq_bpCloseOfInorder]; exact hlc
  have hrightVal :
      (concreteBPNativeSelectCloseGlobalWordTraceResult shape
        (right - 1)).value = some rightClose := by
    rw [selectCloseTrace_value_eq_bpCloseOfInorder]; exact hrc
  by_cases hsame :
      blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) leftClose =
        blockOfClose (canonicalBPRelativeSummaryBlockSizeRaw shape) rightClose
  · obtain ⟨regsF, answerClose, hbranch, hrun, hout⟩ :=
      wholeQueryProgram_runsTo_sameBlock_routeCats shape hlt hbound hshape
        hleftVal hrightVal hsame
    refine ⟨⟨regsF, 5643, true⟩, ?_, rfl, ?_⟩
    · rw [wholeQueryRouteTrace, wholeQueryCats, hbranch]
      simpa [wholeQueryMachineS, wholeQueryMachineStageCats,
        wholeQueryBranchCats, wholeQueryLcaRunCats, hsame] using hrun
    · rw [wholeQueryRouteValue, hbranch]; exact hout
  · obtain ⟨regsF, answerClose, hbranch, hrun, hout⟩ :=
      wholeQueryProgram_runsTo_crossBlock_routeCats shape hlt hbound hshape
        hleftVal hrightVal hsame
    refine ⟨⟨regsF, 5643, true⟩, ?_, rfl, ?_⟩
    · rw [wholeQueryRouteTrace, wholeQueryCats, hbranch]
      simpa [wholeQueryMachineS, wholeQueryMachineStageCats,
        wholeQueryBranchCats, wholeQueryLcaRunCats, hsame] using hrun
    · rw [wholeQueryRouteValue, hbranch]; exact hout

/--
**THE PUBLIC `List Int` COROLLARY LANDS.**

`programSkeleton_valid_matches_public` (`E1WholeQueryPublic.lean:140`) was
written against the hypothesised agreement and could not be discharged.  It
now is, on `ValidRange` and nothing more: same value packet, receipt
positionally the public trace, and memory-read charge equal to the public
cost.
-/
theorem programSkeleton_valid_matches_public_at_machineS
    (xs : List Int) {left right : Nat}
    (hvalid : ValidRange xs left right) :
    ∃ final : State,
      RunsTo (concreteBPNativeSuccinctRMQGlobalReadStore
            (SuccinctClassic.cartesianShape xs))
          (programSkeleton xs.length
            (wholeQueryValidPath (SuccinctClassic.cartesianShape xs)
              wholeQueryNoneExit))
          (initialState left right) final
          (SuccinctClassic.queryTraceResult xs left right).trace
          (wholeQueryCats (wholeQueryMachineS
              (SuccinctClassic.cartesianShape xs))
            (SuccinctClassic.cartesianShape xs) left right) ∧
        final.halted = true ∧
        decodePacket (final.regs regOut) =
          (SuccinctClassic.queryCosted xs left right).value ∧
        catCount
            (wholeQueryCats (wholeQueryMachineS
                (SuccinctClassic.cartesianShape xs))
              (SuccinctClassic.cartesianShape xs) left right)
            .memoryRead =
          (SuccinctClassic.queryCosted xs left right).cost := by
  have hsize : (SuccinctClassic.cartesianShape xs).size = xs.length :=
    Cartesian.shape_size xs
  exact programSkeleton_valid_matches_public
    (concreteBPNativeSuccinctRMQGlobalReadStore
      (SuccinctClassic.cartesianShape xs))
    xs _ _ hvalid
    (wholeQueryMachineAgrees_of_bounds (SuccinctClassic.cartesianShape xs)
      hvalid.1 hvalid.2 (by rw [hsize]; exact hvalid.2))

end E1Query
end WordRAM
end RMQ
