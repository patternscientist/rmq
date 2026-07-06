import RMQ.Core.SuccinctFinalRAM
import RMQ.Core.SuccinctFinalStoreParam

/-!
# Model-adequacy bundle for the final succinct RMQ trace

This module packages existing final-query theorem surfaces into compact
reviewer-facing records. It does not introduce a new algorithm, cost model, or
execution path.
-/

namespace RMQ

namespace SuccinctFinal

/--
Reviewer-facing adequacy packet for the final BP-native succinct RMQ query
trace.  The fields collect the existing theorem surfaces that explain what the
modeled constant-query claim means: the `Costed` result is exactly the
projection of a `WordRAM.TraceResult`, the trace refines the interpreted
whole-query program, its events are reads or word primitives, successful reads
are backed by counted flat payload words, event data are bounded, and no event
is the synthetic cost-only marker.
-/
structure ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop where
  toCosted_eq :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).toCosted
  refines_interpreted :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
        shape left right =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
        shape left right
  cost_le :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left right).cost <=
        concreteBPNativeSuccinctRMQQueryCost
          SuccinctSelect.sparseDenseFalseSelectQueryCost
  event_read_or_primitive :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.isReadWord \/ event.isWordPrimitive
  matches_global_read_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.matchesReadStore
          (concreteBPNativeSuccinctRMQGlobalReadStore shape)
  event_bounds :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeTraceEventReadAddressFitsInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event /\
          concreteBPNativeTraceEventPrimitiveOperandsFitInBits
            (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
              shape left right) event
  no_synthetic :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  successful_reads_backed_by_counted_flat_payload :
    forall {segment index : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord segment index (some word) ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
            shape segment /\
          concreteBPNativeSuccinctRMQFlatPayloadReadBacked
            shape segment index word

/-- Existing theorem packets collected into the final trace model-adequacy record. -/
theorem concreteBPNativeSuccinctRMQFinalTraceModelAdequacy
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
      shape left right := by
  rcases
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTrace_noSynthetic_execution_story
      shape left right with
    ⟨hcost, hrefine, hclass, hstore, hnoSynthetic,
      hreadBits, hprimitiveBits⟩
  exact
    { toCosted_eq := hcost
      refines_interpreted := hrefine
      cost_le :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le
          shape left right
      event_read_or_primitive := hclass
      matches_global_read_store := hstore
      event_bounds := fun event hmem =>
        ⟨hreadBits event hmem, hprimitiveBits event hmem⟩
      no_synthetic := hnoSynthetic
      successful_reads_backed_by_counted_flat_payload := by
        intro segment index word hmem
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_successful_read_events_backed_by_counted_flat_payload
            shape left right hmem }

/-- Paper-facing exactness alias paired with the model-adequacy bundle. -/
theorem concreteBPNativeSuccinctRMQFinalTraceModelAdequacy_exact
    {n : Nat} {shape : Cartesian.CartesianShape}
    (hshape : List.Mem shape (Cartesian.shapesOfSize n))
    {left len : Nat} (hlen : 0 < len) (hbound : left + len <= n) :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
      shape left (left + len)).erase =
        some (scanWindow shape.representative left len) := by
  exact
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
      hshape hlen hbound

/--
Small supplied-store adequacy packet for the final whole-query replay.  This is
separate from the canonical global trace packet because it talks about a caller
provided `WordRAM.ReadStore`.
-/
structure ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) : Prop where
  matches_supplied_store :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        event.matchesReadStore store
  global_store_eval :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape (concreteBPNativeSuccinctRMQGlobalReadStore shape) left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right
  refines_interpreted :
    (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      left right).toCosted =
      concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
        shape left right
  no_synthetic :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right).trace ->
        ¬ event.isSyntheticCostOnlyPrimitive
  store_parametric_from_footprint :
    forall {storeB : WordRAM.ReadStore},
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
          shape store storeB ->
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape store left right =
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            shape storeB left right

/-- Existing supplied-store theorems collected into one small adequacy packet. -/
theorem concreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
    (shape : Cartesian.CartesianShape) (store : WordRAM.ReadStore)
    (left right : Nat) :
    ConcreteBPNativeSuccinctRMQFinalSuppliedStoreAdequacy
      shape store left right := by
  exact
    { matches_supplied_store :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_matchesReadStore
          shape store left right
      global_store_eval :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_globalReadStore
          shape left right
      refines_interpreted :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_refines_wholeQueryInterpretedCosted
          shape left right
      no_synthetic :=
        concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_no_syntheticCostOnlyPrimitive
          shape store left right
      store_parametric_from_footprint := by
        intro storeB hfoot
        exact
          concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_footprint
            shape hfoot left right }

end SuccinctFinal

end RMQ
