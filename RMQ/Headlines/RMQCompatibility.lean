import RMQ.Headlines.RMQ

/-!
# RMQ compatibility and history headlines

This module preserves checked pre-canonical query profiles and cost envelopes
for compatibility users of the broad `RMQ.Headlines` barrel.  It is
deliberately not imported by `RMQPaper`.  Every public name here is marked
`Compatibility` or `Legacy`, because these theorems describe older payloads,
older executions, conservative envelopes, or size-premised routes rather than
the canonical reviewer payload/global trace certified by the paper surface.
-/

namespace RMQ.Headlines

/-- Legacy direct-query two-sided profile with the old aggregate budget. -/
abbrev succinctRMQLegacy196727DirectTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile

/-- Legacy whole-query-interpreted profile with the old aggregate budget. -/
abbrev succinctRMQLegacy196727InterpretedTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile

/-- Legacy domain-leaf-trace profile with the old aggregate budget. -/
abbrev succinctRMQLegacy196727LeafTraceTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_leaf_trace_profile

/-- Legacy locally segmented word-trace profile with the old aggregate budget. -/
abbrev succinctRMQLegacy196727WordTraceTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_profile

/-- Legacy size-premised locally segmented word-trace profile. -/
abbrev succinctRMQLegacy196727LargeRegimeWordTraceTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_word_trace_large_regime_profile

/-- Legacy size-premised globally segmented word-trace profile. -/
abbrev succinctRMQLegacy196727LargeRegimeGlobalWordTraceTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_global_word_trace_large_regime_profile

/-- Compatibility transfer of the checked transitional bound to List Int stores. -/
theorem listIntSuccinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctClassic.storesAgreeOnFootprint xs store
        (RMQ.SuccinctClassic.globalReadStore xs))
    (left right : Nat) :
    (RMQ.SuccinctClassic.queryCostedWithStore
      xs store left right).cost <=
        RMQ.SuccinctClassic.canonicalTransitionalQueryCost :=
  RMQ.SuccinctClassic.listIntCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
    xs hfoot left right

/-- Legacy conservative aggregate bound for the canonical global trace. -/
abbrev succinctRMQLegacy196727WholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le

/-- Compatibility alias for the checked transitional global-trace bound. -/
abbrev succinctRMQCompatibility328WholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional

/-- The compatibility transitional constant computes to `328`. -/
abbrev succinctRMQCompatibility328QueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq

/-- Compatibility-only route-split all-size bound `4144`. -/
abbrev succinctRMQCompatibility4144WholeQueryGlobalWordTraceCostedCostLe :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize

/-- Compatibility-only supplied-store transfer of the `4144` bound. -/
abbrev succinctRMQCompatibility4144WholeQueryGlobalWordTraceCostedWithStoreCostLeOfFootprintGlobal :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_cleanAllSize

/-- Legacy all-size modeled query-cost constant. -/
abbrev succinctRMQLegacy196727QueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost
    RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost

/-- The legacy modeled query-cost constant computes to `196727`. -/
abbrev succinctRMQLegacy196727QueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost_eq

/-- Compatibility-only route-split cost constant `4144`. -/
abbrev succinctRMQCompatibility4144QueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost

abbrev succinctRMQCompatibility4144QueryCostEq :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost_eq

/-- Compatibility full-model transfer of the checked transitional bound. -/
theorem succinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal
    {shape : RMQ.Cartesian.CartesianShape}
    {store : RMQ.WordRAM.ReadStore}
    (hfoot :
      RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
        shape store
          (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
            shape))
    (left right : Nat) :
    (RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
      shape store left right).cost <=
        3 * RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost +
          RMQ.SuccinctClose.ConcreteCompactBPCloseLCADirectory.canonicalCompactBPCloseQueryCostWithRankSeed
            RMQ.SuccinctSelect.sparseDenseFalseSelectQueryCost :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_canonicalTransitional
    hfoot left right

/-- Compatibility size-premised global execution story. -/
abbrev succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_execution_story

/-- Compatibility bounded size-premised global execution story. -/
abbrev succinctRMQCompatibilityLargeRegimeGlobalPayloadStoreBoundedExecutionStory :=
  RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceOfSizeGe_bounded_execution_story

end RMQ.Headlines
