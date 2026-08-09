/-
Existence check for every declaration named by an `ACCEPTED_BASE` row of
`paper/THEOREM_LEDGER.md`.

That status is defined in the ledger header as "kernel-checked declaration
present on the base commit". When the substrate is repinned, all 29 such rows
move to the new commit, and each move **restates** that claim about a new tree.
This script is what makes the restatement checkable instead of assumed: if a
named declaration has been renamed, moved behind a `private`, or deleted, the
repin would silently assert something false.

It checks existence only. Whether each declaration still *says* what its row
claims is the job of the row's proposition text and the audit, not of this
script -- and that limit is the point of stating it here rather than letting
a green run imply more.

Note the import list. `RMQ.Headlines` (the file `RMQ/Headlines.lean`) is
imported **only** by the library root `RMQ.lean`; it is not in the closure of
`RMQPaper`, `RMQHub`, or the spoke roots, even though it defines headline
aliases that ledger rows cite. Omitting it makes two names look absent that are
merely unreachable -- which happened on the first run of this check. An import
list that is too narrow turns this script into a false-positive generator, so
it deliberately imports the library root as well as every artifact root.

Run: `lake env lean scripts/ledger_decl_check.lean`
-/
import Lean
import RMQ
import RMQ.Headlines
import RMQPaper
import RMQHub
import RMQArchive
import RMQRankSelect
import RMQBPNavigation
import RMQUnionFind

namespace RMQLedgerDeclCheck

/-- Declarations cited by `ACCEPTED_BASE` rows, transcribed from the ledger. -/
def ledgerNames : List Lean.Name :=
[
  `RMQ.BPNavigation.concreteBPCloseNavigationFamily_profile,
  `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound,
  `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack,
  `RMQ.Headlines.concreteBPCloseNavigationProfile,
  `RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack,
  `RMQ.Headlines.listIntSuccinctRMQFinalFullModelCostLeOfFootprintGlobal,
  `RMQ.Headlines.listIntSuccinctRMQFinalFullModelSoundnessExactOfFootprintGlobal,
  `RMQ.Headlines.listIntSuccinctRMQFlatPayloadStoreNoSyntheticExecutionStory,
  `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem,
  `RMQ.Headlines.listIntSuccinctRMQReviewerNativeMachineAdequacy,
  `RMQ.Headlines.rankSelectNPlusOConstantQuery,
  `RMQ.Headlines.succinctRMQListIntTwoNPlusOConstantQuery,
  `RMQ.Headlines.succinctRMQReviewerEveryReadOccurrenceProvenance,
  `RMQ.Headlines.succinctRMQReviewerMachineWellFormed,
  `RMQ.Headlines.succinctRMQReviewerManifestSemanticAdequacy,
  `RMQ.Headlines.succinctRMQReviewerPhysicalExecutionRefinesLogical,
  `RMQ.Headlines.succinctRMQReviewerPhysicalStoreAdapter,
  `RMQ.Headlines.succinctRMQReviewerPhysicalWordsErasePublicPayload,
  `RMQ.Headlines.succinctRMQReviewerWordBitsLogarithmic,
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly,
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultWithStoreSuccessfulReadsBackedByCanonicalReviewerPayloadOfFootprintGlobal,
  `RMQ.RankSelect.compressedFIDFixedWeightFamilyProfile,
  `RMQ.RankSelect.compressedFIDFixedWeightInterpretedFamilyProfile,
  `RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery,
  `RMQ.SuccinctClassic.ReviewerNativeMachineAdequacy,
  `RMQ.SuccinctClassic.buildPayload_length,
  `RMQ.SuccinctClassic.chargedTraceCostAlgebra,
  `RMQ.SuccinctClassic.listIntFinalFullModelCostLeOfFootprintGlobal,
  `RMQ.SuccinctClassic.listIntFinalFullModelSoundnessExactOfFootprintGlobal,
  `RMQ.SuccinctClassic.overhead_littleO,
  `RMQ.SuccinctClassic.queryCosted_cost_le,
  `RMQ.SuccinctClassic.queryCosted_invalid,
  `RMQ.SuccinctClassic.queryTraceResultWithStore_eq_of_orderedReadFootprint,
  `RMQ.SuccinctClassic.scanWindow_cartesianShape_representative_eq,
  `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerMachineWellFormed,
  `RMQ.SuccinctFinal.ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy,
  `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone,
  `RMQ.SuccinctFinal.PackedCellProbe.packedReviewerArchitectureCapstone_holds,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_successful_reads_backed_by_counted_flat_payload_of_footprint_global,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_210,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only,
  `RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story,
  `RMQ.SuccinctSpace.LittleOLinear,
  `RMQ.WordRAM.TraceEvent.sum_nonSyntheticWeight_ne_length_of_synthetic_mem,
  `RMQ.leftmostArgMin_unique
]

/-- Floor on the transcribed list, so silently emptying it cannot pass. -/
def expectedCount : Nat := 53

/-- A name that must NOT resolve. Guards against an `env.find?` that always
succeeds -- a check that finds everything is as useless as one that finds
nothing, and only a negative control distinguishes them. -/
def absentControl : Lean.Name := `RMQ.ThisDeclarationDoesNotExist_LedgerCheckControl

end RMQLedgerDeclCheck

#eval show Lean.Elab.Command.CommandElabM Unit from do
  let env <- Lean.getEnv
  let names := RMQLedgerDeclCheck.ledgerNames
  if names.length != RMQLedgerDeclCheck.expectedCount then
    throwError "LEDGER-DECLS: FAIL (list holds {names.length} names, expected {RMQLedgerDeclCheck.expectedCount}). Update expectedCount deliberately when the ledger gains or loses an ACCEPTED_BASE citation; do not let it drift."
  if (env.find? RMQLedgerDeclCheck.absentControl).isSome then
    throwError "LEDGER-DECLS: FAIL (negative control resolved). Name resolution is not discriminating, so a PASS below would mean nothing."
  let missing := names.filter (fun n => (env.find? n).isNone)
  unless missing.isEmpty do
    throwError "LEDGER-DECLS: FAIL ({missing.length} of {names.length} absent): {missing}. Either a declaration was renamed or removed while paper/THEOREM_LEDGER.md still cites it, or an import is missing from this script -- check that second possibility before editing the ledger."
  Lean.logInfo m!"LEDGER-DECLS: RESULT: PASS ({names.length} names present, negative control absent)"
