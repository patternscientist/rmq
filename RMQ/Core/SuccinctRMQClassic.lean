import RMQ.Core.Microtable
import RMQ.Core.SuccinctFinalModelAdequacy

/-!
# Classic list-facing succinct RMQ theorem

The construction-heavy succinct RMQ capstone is naturally stated over
Cartesian-shape representatives, because that is the finite universe used by
the lower-bound and BP encoding layers.  This module gives the same result the
front door that readers expect for RMQ: an ordinary `List Int` input, half-open
queries, and leftmost ties.
-/

namespace RMQ

namespace SuccinctClassic

/-- The concrete shape stored by the succinct RMQ construction for `xs`. -/
def cartesianShape (xs : List Int) : Cartesian.CartesianShape :=
  Cartesian.shape xs

/--
Prepared executable input for the list-facing succinct RMQ path.

The `values` array is an executable cache of the original list, while
`shape` is the one Cartesian shape reused by the prepared payload and query
wrappers below.  The agreement fields are proof-only bridges back to the
canonical `List Int` reference path.
-/
structure PreparedInput where
  xs : List Int
  values : Array Int
  shape : Cartesian.CartesianShape
  values_toList_eq : values.toList = xs
  shape_eq : shape = cartesianShape xs

/--
Build the prepared executable input with the theorem-backed stack/right-spine
Cartesian-shape builder.
-/
def prepareInput (xs : List Int) : PreparedInput where
  xs := xs
  values := xs.toArray
  shape := Cartesian.stackCartesianShape xs
  values_toList_eq := by
    simp
  shape_eq := by
    unfold cartesianShape
    exact Cartesian.stackCartesianShape_eq_shape xs

/-- The prepared array cache erases back to the original list. -/
theorem preparedInput_values_toList_eq (prepared : PreparedInput) :
    prepared.values.toList = prepared.xs :=
  prepared.values_toList_eq

/-- The prepared Cartesian shape is exactly the canonical list-facing shape. -/
theorem preparedInput_shape_eq_cartesianShape (prepared : PreparedInput) :
    prepared.shape = cartesianShape prepared.xs :=
  prepared.shape_eq

/-- The canonical prepared builder stores an array copy of the input list. -/
theorem prepareInput_values_toList_eq (xs : List Int) :
    (prepareInput xs).values.toList = xs := by
  simp [prepareInput]

/-- The prepared builder stores a theorem-backed canonical Cartesian shape. -/
theorem prepareInput_shape_eq_cartesianShape (xs : List Int) :
    (prepareInput xs).shape = cartesianShape xs := by
  simp [prepareInput, cartesianShape, Cartesian.stackCartesianShape_eq_shape]

/--
The executable stack/right-spine shape builder agrees with the canonical
list-facing Cartesian shape used by `SuccinctClassic`.
-/
theorem stackCartesianShape_eq_cartesianShape (xs : List Int) :
    Cartesian.stackCartesianShape xs = cartesianShape xs := by
  unfold cartesianShape
  exact Cartesian.stackCartesianShape_eq_shape xs

/-- The auxiliary `o(n)` term used by the public BP-native construction. -/
abbrev overhead : Nat -> Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerOverhead

/-- Constant modeled query budget of the public BP-native construction. -/
abbrev legacyQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost
    SuccinctSelect.sparseDenseFalseSelectQueryCost

/-- Compatibility bound for the retired route-split/zero-block explanation. -/
abbrev compatibilityCleanAllSizeQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost

/-- Shape-sensitive route-split modeled query budget for `xs`. -/
abbrev routeSplitQueryCost (xs : List Int) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQRouteSplitQueryCost
    (cartesianShape xs)
/-- Principled U3 charged-trace cost for the accepted canonical reviewer route. -/
abbrev queryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost

/-- Checked historical U2 cost, retained without changing the current route. -/
abbrev canonicalTransitionalQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost

/-- Distinct live compatibility cap computed from the current raw expression. -/
abbrev liveCompatibilityQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQLiveCompatibilityQueryCost

/-- Public operation-aligned cost algebra reusable by the E1 simulation. -/
abbrev chargedTraceCostAlgebra :=
  SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra

theorem queryCost_eq : queryCost = 210 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq

/-- Checked historical U3 cost of the retired event-silent fringe route. -/
abbrev canonicalSilentFringeQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost

theorem canonicalSilentFringeQueryCost_eq :
    canonicalSilentFringeQueryCost = 76 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQSilentFringeChargedTraceCost_eq

/-- Checked historical U3 cost of the retired route whose in-word
rank/select leaves were event-silent register word primitives (the B3
recharge replaced them with charged chunk/select-table reads). -/
abbrev canonicalSilentWordRankSelectQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost

theorem canonicalSilentWordRankSelectQueryCost_eq :
    canonicalSilentWordRankSelectQueryCost = 142 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost_eq

/-- Checked historical U3 cost of the retired pre-sparse-level chunked
route: the value `queryCost` held before the charged sparse-level interior
recharge moved the interior component `30 -> 33`.  Retained, not deleted,
so the migration `207 -> 210` stays auditable from the public surface. -/
abbrev canonicalSilentSparseLevelQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost

theorem canonicalSilentSparseLevelQueryCost_eq :
    canonicalSilentSparseLevelQueryCost = 207 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq

theorem canonicalTransitionalQueryCost_eq :
    canonicalTransitionalQueryCost = 328 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq

theorem liveCompatibilityQueryCost_eq :
    liveCompatibilityQueryCost = 352 := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQLiveCompatibilityQueryCost_eq


/-- Shape-sensitive route-split budget over an already prepared shape. -/
abbrev preparedRouteSplitQueryCost (prepared : PreparedInput) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQRouteSplitQueryCost
    prepared.shape

/--
The counted payload built from an ordinary input list: the `2*n` BP shape code
plus the compact auxiliary payload used by the final BP-native construction.
-/
def buildPayload (xs : List Int) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    (cartesianShape xs)

/--
Prepared payload construction.  This reuses the stored Cartesian shape and is
proved below to agree with the canonical `buildPayload` path.
-/
def preparedBuildPayload (prepared : PreparedInput) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    prepared.shape

/-- One principled validity boundary for every public `List Int` execution
surface.  The controller thunk is not evaluated for empty, reversed, or
out-of-bounds ranges. -/
def withValidRange {α : Type}
    (xs : List Int) (left right : Nat)
    (run : Unit -> α) (invalid : α) : α :=
  if ValidRange xs left right then run () else invalid

/-- Canonical guarded trace result. -/
def queryTraceResult (xs : List Int) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  withValidRange xs left right
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (cartesianShape xs) left right)
    (WordRAM.TraceResult.pure none)

/-- Guarded supplied-store trace result. -/
def queryTraceResultWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  withValidRange xs left right
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs) store left right)
    (WordRAM.TraceResult.pure none)

/--
The all-size, global-word-trace query of the public BP-native construction,
specialized to the Cartesian shape of an ordinary input list.
-/
def queryCosted (xs : List Int) (left right : Nat) :
    Costed (Option Nat) :=
  (queryTraceResult xs left right).toCosted

/-- Guarded list-facing form of the canonical interpreted cost target. -/
def canonicalInterpretedQueryCosted
    (xs : List Int) (left right : Nat) : Costed (Option Nat) :=
  withValidRange xs left right
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
        (cartesianShape xs) left right)
    (Costed.pure none)

/--
Prepared all-size query.  This reuses the stored Cartesian shape and is proved
below to agree with the canonical `queryCosted` path, including model cost.
-/
def preparedQueryCosted
    (prepared : PreparedInput) (left right : Nat) :
    Costed (Option Nat) :=
  (withValidRange prepared.xs left right
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        prepared.shape left right)
    (WordRAM.TraceResult.pure none)).toCosted

/--
The supplied-store final query specialized to the Cartesian shape of an
ordinary input list.
-/
def queryCostedWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) :
    Costed (Option Nat) :=
  (queryTraceResultWithStore xs store left right).toCosted

/-- The guarded canonical trace rejects every invalid range before execution. -/
theorem queryTraceResult_invalid
    (xs : List Int) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    queryTraceResult xs left right = WordRAM.TraceResult.pure none := by
  simp [queryTraceResult, withValidRange, hbad]

/-- The guarded canonical costed query rejects every invalid range. -/
theorem queryCosted_invalid
    (xs : List Int) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    queryCosted xs left right = Costed.pure none := by
  simp [queryCosted, queryTraceResult_invalid xs left right hbad,
    WordRAM.TraceResult.pure_toCosted]

/-- Supplied logical stores cannot bypass invalid-range rejection. -/
theorem queryTraceResultWithStore_invalid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    queryTraceResultWithStore xs store left right =
      WordRAM.TraceResult.pure none := by
  simp [queryTraceResultWithStore, withValidRange, hbad]

/-- Costed supplied-store queries reject every invalid range. -/
theorem queryCostedWithStore_invalid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    queryCostedWithStore xs store left right = Costed.pure none := by
  simp [queryCostedWithStore,
    queryTraceResultWithStore_invalid xs store left right hbad,
    WordRAM.TraceResult.pure_toCosted]

/-- On a valid range the public trace is exactly the canonical evaluator. -/
theorem queryTraceResult_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    queryTraceResult xs left right =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        (cartesianShape xs) left right := by
  simp [queryTraceResult, withValidRange, hvalid]

/-- On a valid range the supplied-store trace is exactly the supplied-store
evaluator. -/
theorem queryTraceResultWithStore_valid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    queryTraceResultWithStore xs store left right =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs) store left right := by
  simp [queryTraceResultWithStore, withValidRange, hvalid]

/-- Prepared queries use the same validity boundary. -/
theorem preparedQueryCosted_invalid
    (prepared : PreparedInput) (left right : Nat)
    (hbad : Not (ValidRange prepared.xs left right)) :
    preparedQueryCosted prepared left right = Costed.pure none := by
  simp [preparedQueryCosted, withValidRange, hbad,
    WordRAM.TraceResult.pure_toCosted]

/-- Empty half-open ranges are rejected. -/
theorem queryCosted_empty_range (xs : List Int) (left : Nat) :
    (queryCosted xs left left).erase = none := by
  rw [queryCosted_invalid]
  · rfl
  · simp [ValidRange]

/-- Reversed half-open ranges are rejected. -/
theorem queryCosted_reversed_range
    (xs : List Int) {left right : Nat} (hreverse : right <= left) :
    (queryCosted xs left right).erase = none := by
  rw [queryCosted_invalid]
  · rfl
  · simp [ValidRange]
    omega

/-- Ranges ending beyond the input are rejected. -/
theorem queryCosted_out_of_bounds
    (xs : List Int) {left right : Nat} (hout : xs.length < right) :
    (queryCosted xs left right).erase = none := by
  rw [queryCosted_invalid]
  · rfl
  · simp [ValidRange]
    omega

/-- The prepared route-split budget agrees with the canonical list-facing one. -/
theorem preparedRouteSplitQueryCost_eq_routeSplitQueryCost
    (prepared : PreparedInput) :
    preparedRouteSplitQueryCost prepared =
      routeSplitQueryCost prepared.xs := by
  cases prepared with
  | mk xs values shape hvalues hshape =>
      simp [preparedRouteSplitQueryCost, routeSplitQueryCost, hshape]

/-- Prepared payload construction agrees with canonical `buildPayload`. -/
theorem preparedBuildPayload_eq_buildPayload
    (prepared : PreparedInput) :
    preparedBuildPayload prepared = buildPayload prepared.xs := by
  cases prepared with
  | mk xs values shape hvalues hshape =>
      simp [preparedBuildPayload, buildPayload, hshape]

/-- Prepared query execution agrees exactly with canonical `queryCosted`. -/
theorem preparedQueryCosted_eq_queryCosted
    (prepared : PreparedInput) (left right : Nat) :
    preparedQueryCosted prepared left right =
      queryCosted prepared.xs left right := by
  cases prepared with
  | mk xs values shape hvalues hshape =>
      simp [preparedQueryCosted, queryCosted, queryTraceResult,
        withValidRange, hshape]

/-- Prepared query results agree with canonical `queryCosted` results. -/
theorem preparedQueryCosted_erase_eq
    (prepared : PreparedInput) (left right : Nat) :
    (preparedQueryCosted prepared left right).erase =
      (queryCosted prepared.xs left right).erase := by
  rw [preparedQueryCosted_eq_queryCosted]

/-- Prepared query model costs agree with canonical `queryCosted` costs. -/
theorem preparedQueryCosted_cost_eq
    (prepared : PreparedInput) (left right : Nat) :
    (preparedQueryCosted prepared left right).cost =
      (queryCosted prepared.xs left right).cost := by
  rw [preparedQueryCosted_eq_queryCosted]

/-- Query-independent flat payload layout used by the final query for `xs`. -/
abbrev flatPayloadLayout (xs : List Int) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
      (cartesianShape xs) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayloadLayout
    (cartesianShape xs)

/-- Read-store view induced by the query-independent flat payload layout. -/
abbrev flatPayloadReadStore (xs : List Int) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerReadStore
    (cartesianShape xs)

/-- Canonical globally segmented read store for the final query on `xs`. -/
abbrev globalReadStore (xs : List Int) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
    (cartesianShape xs)

/-- Ordered logical footprint recorded by one supplied-store execution. -/
def orderedReadFootprintWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) :=
  (queryTraceResultWithStore xs store left right).trace.filterMap fun event =>
    match event with
    | WordRAM.TraceEvent.readWord segment index _ => some (segment, index)
    | _ => none

/-- Agreement on exactly the addresses emitted by `storeA`'s execution. -/
def storesAgreeOnOrderedReadFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat) : Prop :=
  forall segment index,
    (segment, index) ∈
        orderedReadFootprintWithStore xs storeA left right ->
      storeA.readWord? segment index = storeB.readWord? segment index

/-- One flat pre-execution machine-word list whose erasure is `buildPayload`. -/
abbrev reviewerPhysicalWords (xs : List Int) : List (List Bool) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords
    (cartesianShape xs)

/-- Canonical flat physical store for an ordinary input list. -/
abbrev reviewerPhysicalReadStore (xs : List Int) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalReadStore
    (cartesianShape xs)

/-- Guarded genuine execution against a caller-supplied flat physical store. -/
def reviewerPhysicalTraceResultWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  withValidRange xs left right
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        (cartesianShape xs) store left right)
    (WordRAM.TraceResult.pure none)

/-- Guarded canonical genuine flat physical execution. -/
def reviewerPhysicalTraceResult
    (xs : List Int) (left right : Nat) : WordRAM.TraceResult (Option Nat) :=
  reviewerPhysicalTraceResultWithStore xs
    (reviewerPhysicalReadStore xs) left right

/-- Ordered physical addresses consumed by the reviewer execution. -/
def reviewerPhysicalFootprintWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) : List Nat :=
  (reviewerPhysicalTraceResultWithStore xs store left right).trace.filterMap
    fun event =>
      match event with
      | WordRAM.TraceEvent.readWord 0 address _ => some address
      | WordRAM.TraceEvent.readWord _ _ _ => none
      | _ => none

/-- Ordered physical addresses consumed by the canonical reviewer execution. -/
def reviewerPhysicalFootprint
    (xs : List Int) (left right : Nat) : List Nat :=
  reviewerPhysicalFootprintWithStore xs (reviewerPhysicalReadStore xs)
    left right

/-- Agreement on every physical address emitted by the first guarded
execution. -/
def physicalStoresAgreeOnOrderedReadFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat) : Prop :=
  forall address,
    address ∈ reviewerPhysicalFootprintWithStore xs storeA left right ->
      storeA.readWord? 0 address = storeB.readWord? 0 address

/-- Supplied flat physical stores cannot bypass invalid-range rejection. -/
theorem reviewerPhysicalTraceResultWithStore_invalid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    reviewerPhysicalTraceResultWithStore xs store left right =
      WordRAM.TraceResult.pure none := by
  simp [reviewerPhysicalTraceResultWithStore, withValidRange, hbad]

/-- The canonical genuine flat physical execution rejects invalid ranges. -/
theorem reviewerPhysicalTraceResult_invalid
    (xs : List Int) (left right : Nat)
    (hbad : Not (ValidRange xs left right)) :
    reviewerPhysicalTraceResult xs left right =
      WordRAM.TraceResult.pure none := by
  simp [reviewerPhysicalTraceResult,
    reviewerPhysicalTraceResultWithStore_invalid xs
      (reviewerPhysicalReadStore xs) left right hbad]

/-- On a valid range the list-facing physical evaluator is exactly the raw
flat-store-parametric evaluator. -/
theorem reviewerPhysicalTraceResultWithStore_valid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    reviewerPhysicalTraceResultWithStore xs store left right =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
        (cartesianShape xs) store left right := by
  simp [reviewerPhysicalTraceResultWithStore, withValidRange, hvalid]

/-- On a valid public range, the answer projection is literally the answer
computed by the existing supplied-store evaluator after physical-address
translation. -/
theorem reviewerPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator_of_valid
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    (reviewerPhysicalTraceResultWithStore xs store left right).value =
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs)
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (cartesianShape xs) store)
        left right).value := by
  rw [reviewerPhysicalTraceResultWithStore_valid xs store left right hvalid]
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator
      (cartesianShape xs) store left right

/-- Projection-specific dependency transfer.  It is deliberately quantified
only over pairs of valid supplied-store executions whose translated evaluator
answers differ; it does not claim that every consumed word is decisive. -/
theorem reviewerPhysicalTraceResultWithStore_value_ne_of_suppliedStoreEvaluator_value_ne_of_valid
    (xs : List Int) (storeA storeB : WordRAM.ReadStore) (left right : Nat)
    (hvalid : ValidRange xs left right)
    (hneq :
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs)
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (cartesianShape xs) storeA)
        left right).value ≠
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs)
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (cartesianShape xs) storeB)
        left right).value) :
    (reviewerPhysicalTraceResultWithStore xs storeA left right).value ≠
      (reviewerPhysicalTraceResultWithStore xs storeB left right).value := by
  rw [reviewerPhysicalTraceResultWithStore_valid xs storeA left right hvalid,
    reviewerPhysicalTraceResultWithStore_valid xs storeB left right hvalid]
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne
      (cartesianShape xs) storeA storeB left right hneq

/-- Public corruption fixture: make one translated physical address
unreadable while leaving every other canonical physical word unchanged. -/
abbrev reviewerPhysicalDropAddressStore
    (xs : List Int) (address : Nat) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalDropAddressStore
    (cartesianShape xs) address

/-- On a valid range the canonical list-facing physical evaluator is the
canonical raw flat physical execution. -/
theorem reviewerPhysicalTraceResult_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    reviewerPhysicalTraceResult xs left right =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
        (cartesianShape xs) left right := by
  rw [reviewerPhysicalTraceResult,
    reviewerPhysicalTraceResultWithStore_valid xs
      (reviewerPhysicalReadStore xs) left right hvalid]
  rfl

/-- The guarded canonical physical execution refines the guarded canonical
logical execution, preserving the decoded result, ordered translated trace,
and modeled cost. -/
theorem reviewerPhysicalTraceResult_refines_queryTraceResult
    (xs : List Int) (left right : Nat) :
    (reviewerPhysicalTraceResult xs left right).value =
        (queryTraceResult xs left right).value /\
      (reviewerPhysicalTraceResult xs left right).trace =
        (queryTraceResult xs left right).trace.map
          (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent
            (cartesianShape xs)) /\
      (reviewerPhysicalTraceResult xs left right).toCosted =
        queryCosted xs left right := by
  by_cases hvalid : ValidRange xs left right
  · simpa only [reviewerPhysicalTraceResult_valid xs left right hvalid,
      queryTraceResult_valid xs left right hvalid, queryCosted] using
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
        (cartesianShape xs) left right
  · simp [reviewerPhysicalTraceResult,
      reviewerPhysicalTraceResultWithStore, queryTraceResult, queryCosted,
      withValidRange, hvalid, WordRAM.TraceResult.pure_toCosted]

/-- Agreement on the first guarded execution's physical footprint determines
the complete guarded physical execution. -/
theorem reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat)
    (hagree : physicalStoresAgreeOnOrderedReadFootprint
      xs storeA storeB left right) :
    reviewerPhysicalTraceResultWithStore xs storeA left right =
      reviewerPhysicalTraceResultWithStore xs storeB left right := by
  by_cases hvalid : ValidRange xs left right
  · rw [reviewerPhysicalTraceResultWithStore_valid xs storeA left right hvalid,
      reviewerPhysicalTraceResultWithStore_valid xs storeB left right hvalid]
    apply
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint
    intro address hmem
    apply hagree address
    simpa [reviewerPhysicalFootprintWithStore,
      reviewerPhysicalTraceResultWithStore_valid xs storeA left right hvalid,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprintWithStore]
      using hmem
  · simp [reviewerPhysicalTraceResultWithStore, withValidRange, hvalid]

/-- A disagreement at a consumed physical address is observable at the public
list-facing evaluator. -/
theorem reviewerPhysicalTraceResultWithStore_ne_of_consumed_read_disagreement
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right address : Nat) (wordA? : Option WordRAM.Word)
    (hmem : WordRAM.TraceEvent.readWord 0 address wordA? ∈
      (reviewerPhysicalTraceResultWithStore
        xs storeA left right).trace)
    (hneq : storeA.readWord? 0 address ≠ storeB.readWord? 0 address) :
    reviewerPhysicalTraceResultWithStore xs storeA left right ≠
      reviewerPhysicalTraceResultWithStore xs storeB left right := by
  by_cases hvalid : ValidRange xs left right
  · rw [reviewerPhysicalTraceResultWithStore_valid xs storeA left right hvalid,
      reviewerPhysicalTraceResultWithStore_valid xs storeB left right hvalid]
    apply
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_ne_of_consumed_read_disagreement
        (cartesianShape xs) storeA storeB left right address wordA?
    · simpa [reviewerPhysicalTraceResultWithStore_valid xs storeA left right hvalid]
        using hmem
    · exact hneq
  · simp [reviewerPhysicalTraceResultWithStore, withValidRange, hvalid]
      at hmem

/-- Query-independent all-size physical capacity. -/
abbrev reviewerCapacity (n : Nat) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerCapacity n

/-- Query-independent all-size machine word width. -/
abbrev reviewerWordBits (n : Nat) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerWordBits n

/-- List-facing final footprint agreement for two supplied read stores. -/
abbrev storesAgreeOnFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore) : Prop :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
    (cartesianShape xs) storeA storeB

/-- Final globally segmented WordRAM trace result for the query on `xs`. -/
abbrev flatPayloadTraceResult
    (xs : List Int) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  queryTraceResult xs left right

/-- Trace-local bit width bounding read addresses and word-primitive data. -/
abbrev flatPayloadTraceEventBits
    (xs : List Int) (left right : Nat) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceEventBits
    (cartesianShape xs) left right

/--
List-facing form of the final flat-payload/no-synthetic execution story.

For fixed `xs,left,right`, this names the concrete flat layout and read store,
states how the flat payload splits into its component payloads, proves every
successful store read has source-manifest evidence, proves counted successful
store reads have positional flat-payload backing, and packages the interpreted
trace, store agreement, bounded event data, and absence of synthetic cost-only
events.
-/
def FlatPayloadStoreNoSyntheticExecutionStory
    (xs : List Int) (left right : Nat) : Prop :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
      (cartesianShape xs) =
      buildPayload xs /\
    (ValidRange xs left right ->
      SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
        (cartesianShape xs) left right) /\
    SuccinctSpace.flattenPayloadWords
        (reviewerPhysicalWords xs) = buildPayload xs /\
    ((reviewerPhysicalTraceResult xs left right).value =
        (queryTraceResult xs left right).value /\
      (reviewerPhysicalTraceResult xs left right).trace =
        (queryTraceResult xs left right).trace.map
          (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent
            (cartesianShape xs)) /\
      (reviewerPhysicalTraceResult xs left right).toCosted =
        queryCosted xs left right) /\
    reviewerPhysicalFootprint xs left right =
      ((reviewerPhysicalTraceResult xs left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | WordRAM.TraceEvent.readWord _ _ _ => none
        | _ => none) /\
    (forall storeB : WordRAM.ReadStore,
      physicalStoresAgreeOnOrderedReadFootprint xs
          (reviewerPhysicalReadStore xs) storeB left right ->
        reviewerPhysicalTraceResult xs left right =
          reviewerPhysicalTraceResultWithStore xs storeB left right) /\
    (forall store : WordRAM.ReadStore,
      ValidRange xs left right ->
        (reviewerPhysicalTraceResultWithStore xs store left right).value =
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
            (cartesianShape xs)
            (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
              (cartesianShape xs) store)
            left right).value) /\
    (forall storeA storeB : WordRAM.ReadStore,
      ValidRange xs left right ->
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs)
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (cartesianShape xs) storeA)
        left right).value ≠
      (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        (cartesianShape xs)
        (SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          (cartesianShape xs) storeB)
        left right).value ->
        (reviewerPhysicalTraceResultWithStore xs storeA left right).value ≠
          (reviewerPhysicalTraceResultWithStore xs storeB left right).value) /\
    (Not (ValidRange xs left right) ->
      queryTraceResult xs left right = WordRAM.TraceResult.pure none /\
      reviewerPhysicalTraceResult xs left right =
        WordRAM.TraceResult.pure none /\
      queryCosted xs left right = Costed.pure none /\
      reviewerPhysicalFootprint xs left right = [] /\
      forall store : WordRAM.ReadStore,
        reviewerPhysicalTraceResultWithStore xs store left right =
          WordRAM.TraceResult.pure none) /\
    (forall event,
      List.Mem event (reviewerPhysicalTraceResult xs left right).trace ->
        event.matchesReadStore
          (reviewerPhysicalReadStore xs)) /\
    (forall {address : Nat} {word : List Bool},
      WordRAM.TraceEvent.readWord 0 address (some word) ∈
          (reviewerPhysicalTraceResult xs left right).trace ->
        address < (reviewerPhysicalWords xs).length /\
          (reviewerPhysicalWords xs)[address]? = some word) /\
    queryCosted xs left right =
      canonicalInterpretedQueryCosted xs left right /\
    (forall event,
      List.Mem event (reviewerPhysicalTraceResult xs left right).trace ->
        Not event.isSyntheticCostOnlyPrimitive)

/--
The final query trace for an ordinary list is backed by the concrete flat
payload layout and contains no synthetic cost-only trace events.
-/
theorem flatPayloadStoreNoSyntheticExecutionStory
    (xs : List Int) (left right : Nat) :
    FlatPayloadStoreNoSyntheticExecutionStory xs left right := by
  unfold FlatPayloadStoreNoSyntheticExecutionStory
  refine ⟨rfl,
    (fun _ =>
      SuccinctFinal.concreteBPNativeSuccinctRMQFinalTraceModelAdequacy
        (cartesianShape xs) left right), ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [reviewerPhysicalWords, buildPayload] using
      SuccinctFinal.concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
        (cartesianShape xs)
  · by_cases hvalid : ValidRange xs left right
    · simpa only [reviewerPhysicalTraceResult_valid xs left right hvalid,
        queryTraceResult_valid xs left right hvalid, queryCosted] using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
          (cartesianShape xs) left right
    · simp [reviewerPhysicalTraceResult,
        reviewerPhysicalTraceResultWithStore,
        queryTraceResult, queryCosted, withValidRange, hvalid,
        WordRAM.TraceResult.pure_toCosted]
  · intro storeB hagree
    exact
      reviewerPhysicalTraceResultWithStore_eq_of_orderedReadFootprint
        xs (reviewerPhysicalReadStore xs) storeB left right hagree
  · intro store hvalid
    exact
      reviewerPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator_of_valid
        xs store left right hvalid
  · intro storeA storeB hvalid hneq
    exact
      reviewerPhysicalTraceResultWithStore_value_ne_of_suppliedStoreEvaluator_value_ne_of_valid
        xs storeA storeB left right hvalid hneq
  · intro hbad
    refine ⟨queryTraceResult_invalid xs left right hbad,
      reviewerPhysicalTraceResult_invalid xs left right hbad,
      queryCosted_invalid xs left right hbad, ?_, ?_⟩
    · unfold reviewerPhysicalFootprint reviewerPhysicalFootprintWithStore
      rw [reviewerPhysicalTraceResultWithStore_invalid xs
        (reviewerPhysicalReadStore xs) left right hbad]
      rfl
    · intro store
      exact reviewerPhysicalTraceResultWithStore_invalid
        xs store left right hbad
  · intro event hmem
    by_cases hvalid : ValidRange xs left right
    · have hraw : event ∈
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            (cartesianShape xs) left right).trace := by
        simpa only [reviewerPhysicalTraceResult_valid xs left right hvalid]
          using hmem
      exact
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_matchesReadStore
          (cartesianShape xs) (reviewerPhysicalReadStore xs)
          left right event hraw
    · exfalso
      have hnil : List.Mem event [] := by
        simpa [reviewerPhysicalTraceResult_invalid xs left right hvalid,
          WordRAM.TraceResult.pure] using hmem
      exact List.not_mem_nil hnil
  · intro address word hmem
    by_cases hvalid : ValidRange xs left right
    · have hraw : WordRAM.TraceEvent.readWord 0 address (some word) ∈
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            (cartesianShape xs) left right).trace := by
        simpa only [reviewerPhysicalTraceResult_valid xs left right hvalid]
          using hmem
      simpa only [reviewerPhysicalWords] using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_successful_read_backed
          (cartesianShape xs) left right hraw
    · exfalso
      simp [reviewerPhysicalTraceResult_invalid xs left right hvalid,
        WordRAM.TraceResult.pure] at hmem
  · by_cases hvalid : ValidRange xs left right
    · rw [show queryCosted xs left right =
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            (cartesianShape xs) left right).toCosted by
          simp [queryCosted, queryTraceResult_valid xs left right hvalid]]
      rw [show canonicalInterpretedQueryCosted xs left right =
          SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryCanonicalInterpretedCosted
            (cartesianShape xs) left right by
          simp [canonicalInterpretedQueryCosted, withValidRange, hvalid]]
      exact
          SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_refines_canonicalInterpretedCosted
            (cartesianShape xs) left right
    · simp [queryCosted, queryTraceResult,
        canonicalInterpretedQueryCosted, withValidRange, hvalid,
        WordRAM.TraceResult.pure_toCosted]
  · intro event hmem
    by_cases hvalid : ValidRange xs left right
    · have hraw : event ∈
          (SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
            (cartesianShape xs) left right).trace := by
        simpa only [reviewerPhysicalTraceResult_valid xs left right hvalid]
          using hmem
      exact
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult_no_syntheticCostOnlyPrimitive
          (cartesianShape xs) left right event hraw
    · exfalso
      have hnil : List.Mem event [] := by
        simpa [reviewerPhysicalTraceResult_invalid xs left right hvalid,
          WordRAM.TraceResult.pure] using hmem
      exact List.not_mem_nil hnil

/-- The raw shape-level adequacy packet is consumed by the public story only
on the validity domain of the guarded list execution. -/
theorem flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
      (cartesianShape xs) left right :=
  (flatPayloadStoreNoSyntheticExecutionStory xs left right).2.1 hvalid

/-- List-facing projection of occurrence-level producer provenance: every
indexed logical read of a valid query retains its program/instruction/local
positions, prefix state, exact invocation parameters, physical source, and
component-local occurrence. -/
theorem flatPayloadStoreNoSyntheticExecutionStory_occurrenceProvenance_of_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance
      (cartesianShape xs) left right :=
  (flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid
    xs left right hvalid).every_emitted_read_has_occurrence_provenance

/-- Compatibility W18 event-value projection.  This does not retain global or
local occurrence positions; use the occurrence theorem above. -/
theorem flatPayloadStoreNoSyntheticExecutionStory_eventValueProducerProvenance_of_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
      (cartesianShape xs) left right :=
  (flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid
    xs left right hvalid).every_emitted_read_has_eventValue_producer_provenance

/-- Compatibility W18 component may-read fact.  It is not top-level
valid-query reachability. -/
theorem reviewerCountedSource_producerMayPath
    (xs : List Int) (source : SuccinctFinal.ReviewerSource)
    (hcounted : source.Counted) :
    source.HasProducerMayPath (cartesianShape xs) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path
    (cartesianShape xs) source hcounted

/-- Compatibility W18 component-only shared-BP path fact. -/
theorem reviewerSharedBPConsumer_producerConnected
    (xs : List Int) (consumer : SuccinctFinal.ReviewerSharedBPConsumer) :
    consumer.ProducerConnected (cartesianShape xs) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected
    (cartesianShape xs) consumer

/-- On every invalid public range, result, trace, cost, footprint, and every
supplied-flat-store execution are the same guarded empty execution. -/
theorem flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics
    (xs : List Int) (left right : Nat)
    (hbad : ¬ ValidRange xs left right) :
    queryTraceResult xs left right = WordRAM.TraceResult.pure none ∧
      reviewerPhysicalTraceResult xs left right =
        WordRAM.TraceResult.pure none ∧
      queryCosted xs left right = Costed.pure none ∧
      reviewerPhysicalFootprint xs left right = [] ∧
      ∀ store : WordRAM.ReadStore,
        reviewerPhysicalTraceResultWithStore xs store left right =
          WordRAM.TraceResult.pure none := by
  exact
    (flatPayloadStoreNoSyntheticExecutionStory xs left right).2.2.2.2.2.2.2.2.1
      hbad

/--
Shape-only local queries over `Cartesian.shape xs` return the same leftmost
RMQ answer as scanning the original list.
-/
theorem shape_queryOffset?_eq_scanWindow
    (xs : List Int) {left len : Nat}
    (hlen : 0 < len) (hbound : left + len <= xs.length) :
    (cartesianShape xs).queryOffset? left (left + len) =
      some (scanWindow xs left len) := by
  have hvalid :
      Cartesian.LocalValid xs.length left (left + len) := by
    unfold Cartesian.LocalValid
    omega
  have hquery :=
    Cartesian.queryOffset?_blockSignature
      (xs := xs) (start := 0) (blockSize := xs.length)
      (left := left) (right := left + len) (by simp)
  rw [dif_pos hvalid] at hquery
  have hlocal :=
    Cartesian.localScanOffset_add_start
      (xs := xs) (start := 0) (blockSize := xs.length)
      (left := left) (right := left + len) hvalid
  have hlocalEq :
      Cartesian.localScanOffset xs 0 left (left + len) =
        scanWindow xs left len := by
    simpa using hlocal
  simpa [cartesianShape, Cartesian.blockSignature, Cartesian.shape, hlocalEq]
    using hquery

/--
The canonical representative of `Cartesian.shape xs` has the same RMQ answers
as `xs`; the proof compares the shared shape-only local query.
-/
theorem scanWindow_cartesianShape_representative_eq
    (xs : List Int) {left len : Nat}
    (hlen : 0 < len) (hbound : left + len <= xs.length) :
    scanWindow (cartesianShape xs).representative left len =
      scanWindow xs left len := by
  let shape := cartesianShape xs
  have hshapeOfSize : Cartesian.ShapeOfSize xs.length shape := by
    simpa [shape, cartesianShape] using Cartesian.shape_shapeOfSize xs
  have hrepLen : shape.representative.length = xs.length := by
    rw [Cartesian.CartesianShape.representative_length,
      Cartesian.ShapeOfSize.size_eq hshapeOfSize]
  have hrepBound : left + len <= shape.representative.length := by
    omega
  have hrepQuery :=
    shape_queryOffset?_eq_scanWindow shape.representative
      hlen hrepBound
  have hxsQuery :=
    shape_queryOffset?_eq_scanWindow xs hlen hbound
  have hrepShape : cartesianShape shape.representative = shape := by
    simpa [cartesianShape] using
      Cartesian.CartesianShape.shape_representative shape
  have hrepQuery' :
      shape.queryOffset? left (left + len) =
        some (scanWindow shape.representative left len) := by
    simpa [hrepShape] using hrepQuery
  have hxsQuery' :
      shape.queryOffset? left (left + len) =
        some (scanWindow xs left len) := by
    simpa [shape] using hxsQuery
  have hsome :
      some (scanWindow shape.representative left len) =
        some (scanWindow xs left len) := by
    rw [← hrepQuery', hxsQuery']
  exact Option.some.inj hsome

/-- The auxiliary payload overhead is `o(n)`. -/
theorem overhead_littleO :
    SuccinctSpace.LittleOLinear overhead := by
  exact
    SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerOverhead_littleO

/-- The live canonical payload has at most `2*n + overhead n` bits. -/
theorem buildPayload_length (xs : List Int) :
    (buildPayload xs).length <=
      2 * xs.length + overhead xs.length := by
  have hshape :
      List.Mem (cartesianShape xs)
        (Cartesian.shapesOfSize xs.length) := by
    exact
      Cartesian.shapeOfSize_mem_shapesOfSize
        (by simpa [cartesianShape] using Cartesian.shape_shapeOfSize xs)
  simpa [buildPayload, overhead] using
    SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload_length_le
      hshape

/-- Every query has the checked canonical transitional U2 cost. -/
theorem queryCosted_cost_le_canonicalTransitional
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost <= canonicalTransitionalQueryCost := by
  by_cases hvalid : ValidRange xs left right
  · rw [queryCosted, queryTraceResult_valid xs left right hvalid]
    simpa [canonicalTransitionalQueryCost,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
      using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional
          (cartesianShape xs) left right
  · simp [queryCosted, queryTraceResult, withValidRange, hvalid,
      canonicalTransitionalQueryCost]

/-- Every query also has the distinctly named live raw-expression cap. -/
theorem queryCosted_cost_le_liveCompatibility
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost <= liveCompatibilityQueryCost := by
  by_cases hvalid : ValidRange xs left right
  · rw [queryCosted, queryTraceResult_valid xs left right hvalid]
    simpa [liveCompatibilityQueryCost,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
      using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_liveCompatibility
          (cartesianShape xs) left right
  · simp [queryCosted, queryTraceResult, withValidRange, hvalid,
      liveCompatibilityQueryCost]

/-- Every query has the principled fixed all-size charged-trace cost bound. -/
theorem queryCosted_cost_le
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost <= queryCost := by
  by_cases hvalid : ValidRange xs left right
  · rw [queryCosted, queryTraceResult_valid xs left right hvalid]
    simpa [queryCost,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
      using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace
          (cartesianShape xs) left right
  · simp [queryCosted, queryTraceResult, withValidRange, hvalid,
      queryCost]

/--
If a supplied store agrees with the canonical global store on the final
footprint, the supplied-store query is exactly the canonical list-facing query.
-/
theorem queryCostedWithStore_eq_queryCosted_of_footprint
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (left right : Nat) :
    queryCostedWithStore xs store left right =
      queryCosted xs left right := by
  by_cases hvalid : ValidRange xs left right
  · rw [queryCostedWithStore, queryCosted,
      queryTraceResultWithStore_valid xs store left right hvalid,
      queryTraceResult_valid xs left right hvalid]
    simpa [
      storesAgreeOnFootprint, globalReadStore,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore,
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
      using
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
          (cartesianShape xs) store hfoot left right
  · simp [queryCostedWithStore, queryCosted,
      queryTraceResultWithStore, queryTraceResult, withValidRange, hvalid]

/-- Agreement on the actual ordered footprint determines the complete
supplied-store execution: decoded result, cost, ordered trace, repeated reads,
and failed reads are identical. -/
theorem queryTraceResultWithStore_eq_of_orderedReadFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat)
    (hagree : storesAgreeOnOrderedReadFootprint
      xs storeA storeB left right) :
    queryTraceResultWithStore xs storeA left right =
      queryTraceResultWithStore xs storeB left right := by
  by_cases hvalid : ValidRange xs left right
  · have hraw :
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
          (cartesianShape xs) storeA storeB left right := by
      intro segment index hmem
      apply hagree segment index
      simpa [orderedReadFootprintWithStore,
        queryTraceResultWithStore_valid xs storeA left right hvalid,
        SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore]
        using hmem
    rw [queryTraceResultWithStore_valid xs storeA left right hvalid,
      queryTraceResultWithStore_valid xs storeB left right hvalid]
    exact
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
        (cartesianShape xs) storeA storeB left right hraw
  · simp [queryTraceResultWithStore, withValidRange, hvalid]

/-- Dynamic-footprint agreement also determines the decoded result and modeled
cost after projection to `Costed`. -/
theorem queryCostedWithStore_eq_of_orderedReadFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat)
    (hagree : storesAgreeOnOrderedReadFootprint
      xs storeA storeB left right) :
    queryCostedWithStore xs storeA left right =
      queryCostedWithStore xs storeB left right := by
  exact congrArg WordRAM.TraceResult.toCosted
    (queryTraceResultWithStore_eq_of_orderedReadFootprint
      xs storeA storeB left right hagree)

/--
Under footprint agreement with the canonical global store, the supplied-store
list-facing query inherits the all-size final model cost bound.
-/
theorem listIntFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (left right : Nat) :
    (queryCostedWithStore xs store left right).cost <= queryCost := by
  rw [queryCostedWithStore_eq_queryCosted_of_footprint xs hfoot left right]
  exact queryCosted_cost_le xs left right

/-- Explicit U3 list-facing supplied-store cost theorem. -/
theorem listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (left right : Nat) :
    (queryCostedWithStore xs store left right).cost <= queryCost :=
  listIntFinalFullModelCostLeOfFootprintGlobal xs hfoot left right

/-- Footprint agreement transfers the canonical transitional U2 cost bound. -/
theorem listIntCanonicalTransitionalFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (left right : Nat) :
    (queryCostedWithStore xs store left right).cost <=
      canonicalTransitionalQueryCost := by
  rw [queryCostedWithStore_eq_queryCosted_of_footprint xs hfoot left right]
  exact queryCosted_cost_le_canonicalTransitional xs left right

/-- Footprint agreement transfers the distinct live `352` compatibility cap. -/
theorem listIntLiveCompatibilityFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (left right : Nat) :
    (queryCostedWithStore xs store left right).cost <=
      liveCompatibilityQueryCost := by
  rw [queryCostedWithStore_eq_queryCosted_of_footprint xs hfoot left right]
  exact queryCosted_cost_le_liveCompatibility xs left right

/-- Valid half-open queries return the exact leftmost-minimum index of `xs`. -/
theorem queryCosted_exact
    (xs : List Int) {left len : Nat}
    (hlen : 0 < len) (hbound : left + len <= xs.length) :
    (queryCosted xs left (left + len)).erase =
      some (scanWindow xs left len) := by
  have hshape :
      List.Mem (cartesianShape xs)
        (Cartesian.shapesOfSize xs.length) := by
    exact
      Cartesian.shapeOfSize_mem_shapesOfSize
        (by simpa [cartesianShape] using Cartesian.shape_shapeOfSize xs)
  calc
    (queryCosted xs left (left + len)).erase =
        some (scanWindow (cartesianShape xs).representative left len) := by
          have hvalid : ValidRange xs left (left + len) := by
            constructor <;> omega
          rw [queryCosted,
            queryTraceResult_valid xs left (left + len) hvalid]
          simpa [
            SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted]
            using
            SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_exact
              (n := xs.length) (shape := cartesianShape xs)
              hshape hlen hbound
    _ = some (scanWindow xs left len) := by
          rw [scanWindow_cartesianShape_representative_eq xs hlen hbound]

/--
List-facing final full-model exactness for a supplied store that agrees with
the canonical global store on the final footprint.
-/
theorem listIntFinalFullModelSoundnessExactOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    {left len : Nat} (hlen : 0 < len)
    (hbound : left + len <= xs.length) :
    (queryCostedWithStore xs store left (left + len)).erase =
      some (scanWindow xs left len) := by
  rw [queryCostedWithStore_eq_queryCosted_of_footprint
    xs hfoot left (left + len)]
  exact queryCosted_exact xs hlen hbound

/-- Valid half-open queries return an index satisfying the core leftmost-tie spec. -/
theorem queryCosted_leftmost
    (xs : List Int) {left len idx : Nat}
    (hlen : 0 < len) (hbound : left + len <= xs.length)
    (hquery : (queryCosted xs left (left + len)).erase = some idx) :
    LeftmostArgMin xs left (left + len) idx := by
  have hexact := queryCosted_exact xs hlen hbound
  have hidx : idx = scanWindow xs left len := by
    exact (Option.some.inj (by rw [← hquery, hexact])).symm
  simpa [hidx] using scanWindow_leftmost xs left len hlen hbound

/--
Classic public theorem over ordinary lists.

For every `xs : List Int`, `buildPayload xs` has length at most
`2 * xs.length + overhead xs.length` with `overhead = o(n)`, and
`queryCosted xs` answers valid half-open RMQ queries exactly with leftmost ties
within the constant modeled query budget `queryCost`.
-/
theorem listInt_two_n_plus_o_constant_query_profile :
    SuccinctSpace.LittleOLinear overhead /\
      forall xs : List Int,
        (buildPayload xs).length <=
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
        (forall left right,
          Not (ValidRange xs left right) ->
            (queryCosted xs left right).erase = none) /\
        (forall {left len : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase =
                some (scanWindow xs left len)) /\
        (forall {left len idx : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase = some idx ->
                LeftmostArgMin xs left (left + len) idx) := by
  refine ⟨overhead_littleO, ?_⟩
  intro xs
  exact
    ⟨buildPayload_length xs,
      queryCosted_cost_le xs,
      (fun left right hbad => by
        rw [queryCosted_invalid xs left right hbad]
        rfl),
      (fun hlen hbound => queryCosted_exact xs hlen hbound),
      (fun hlen hbound hquery =>
        queryCosted_leftmost xs hlen hbound hquery)⟩

/--
Classic public theorem over ordinary lists, strengthened with the final
flat-payload/no-synthetic WordRAM execution story.

For every `xs : List Int`, this keeps the existing `2*n + o(n)` counted
payload and constant modeled query-cost clauses, proves valid half-open queries
answer the classic leftmost RMQ contract, and additionally proves every final
query trace is backed by the query-independent flat payload layout/read store
with bounded reads, bounded word-primitive data, and no synthetic cost-only
events.
-/
theorem listInt_flatPayloadStore_noSynthetic_execution_story :
    SuccinctSpace.LittleOLinear overhead /\
      forall xs : List Int,
        (buildPayload xs).length <=
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
        (forall left right,
          Not (ValidRange xs left right) ->
            (queryCosted xs left right).erase = none) /\
        (forall {left len : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase =
                some (scanWindow xs left len)) /\
        (forall {left len idx : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase = some idx ->
                LeftmostArgMin xs left (left + len) idx) /\
        (forall left right,
          FlatPayloadStoreNoSyntheticExecutionStory xs left right) := by
  refine And.intro overhead_littleO ?_
  intro xs
  exact
    And.intro (buildPayload_length xs)
      (And.intro (queryCosted_cost_le xs)
        (And.intro
          (fun left right hbad => by
            rw [queryCosted_invalid xs left right hbad]
            rfl)
          (And.intro
            (fun hlen hbound => queryCosted_exact xs hlen hbound)
            (And.intro
              (fun hlen hbound hquery =>
                queryCosted_leftmost xs hlen hbound hquery)
              (fun left right =>
                flatPayloadStoreNoSyntheticExecutionStory xs left right)))))

/--
Named public capstone: the no-synthetic flat execution story uses the same
`2*n + o(n)` advertised payload `buildPayload xs`, with every actual
successful read backed by the counted flat layout.
-/
theorem listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story :
    SuccinctSpace.LittleOLinear overhead /\
      forall xs : List Int,
        (buildPayload xs).length <=
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
        (forall left right,
          Not (ValidRange xs left right) ->
            (queryCosted xs left right).erase = none) /\
        (forall {left len : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase =
                some (scanWindow xs left len)) /\
        (forall {left len idx : Nat},
          0 < len ->
            left + len <= xs.length ->
              (queryCosted xs left (left + len)).erase = some idx ->
                LeftmostArgMin xs left (left + len) idx) /\
        (forall left right,
          FlatPayloadStoreNoSyntheticExecutionStory xs left right) :=
  listInt_flatPayloadStore_noSynthetic_execution_story

end SuccinctClassic

end RMQ
