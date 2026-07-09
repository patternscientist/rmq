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

/-- Build the prepared executable input by computing the canonical shape once. -/
def prepareInput (xs : List Int) : PreparedInput where
  xs := xs
  values := xs.toArray
  shape := cartesianShape xs
  values_toList_eq := by
    simp
  shape_eq := rfl

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

/-- The canonical prepared builder stores the canonical Cartesian shape. -/
theorem prepareInput_shape_eq_cartesianShape (xs : List Int) :
    (prepareInput xs).shape = cartesianShape xs := by
  rfl

/-- The auxiliary `o(n)` term used by the public BP-native construction. -/
abbrev overhead : Nat -> Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQOverhead
    SuccinctFinal.genericSparseExceptionBPCloseAccessOverhead

/-- Constant modeled query budget of the public BP-native construction. -/
abbrev legacyQueryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQQueryCost
    SuccinctSelect.sparseDenseFalseSelectQueryCost

/-- Clean fixed all-size modeled query budget of the public construction. -/
abbrev queryCost : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCleanAllSizeQueryCost

/-- Shape-sensitive route-split modeled query budget for `xs`. -/
abbrev routeSplitQueryCost (xs : List Int) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQRouteSplitQueryCost
    (cartesianShape xs)

/-- Shape-sensitive route-split budget over an already prepared shape. -/
abbrev preparedRouteSplitQueryCost (prepared : PreparedInput) : Nat :=
  SuccinctFinal.concreteBPNativeSuccinctRMQRouteSplitQueryCost
    prepared.shape

/--
The counted payload built from an ordinary input list: the `2*n` BP shape code
plus the compact auxiliary payload used by the final BP-native construction.
-/
def buildPayload (xs : List Int) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQPayload
    SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily
    (cartesianShape xs)

/--
Prepared payload construction.  This reuses the stored Cartesian shape and is
proved below to agree with the canonical `buildPayload` path.
-/
def preparedBuildPayload (prepared : PreparedInput) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQPayload
    SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily
    prepared.shape

/--
The all-size, global-word-trace query of the public BP-native construction,
specialized to the Cartesian shape of an ordinary input list.
-/
def queryCosted (xs : List Int) (left right : Nat) :
    Costed (Option Nat) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    (cartesianShape xs) left right

/--
Prepared all-size query.  This reuses the stored Cartesian shape and is proved
below to agree with the canonical `queryCosted` path, including model cost.
-/
def preparedQueryCosted
    (prepared : PreparedInput) (left right : Nat) :
    Costed (Option Nat) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted
    prepared.shape left right

/--
The supplied-store final query specialized to the Cartesian shape of an
ordinary input list.
-/
def queryCostedWithStore
    (xs : List Int) (store : WordRAM.ReadStore) (left right : Nat) :
    Costed (Option Nat) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore
    (cartesianShape xs) store left right

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
      simp [preparedQueryCosted, queryCosted, hshape]

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
    SuccinctFinal.ConcreteBPNativeSuccinctRMQFlatPayloadLayout
      (cartesianShape xs) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadLayout
    (cartesianShape xs)

/-- Read-store view induced by the query-independent flat payload layout. -/
abbrev flatPayloadReadStore (xs : List Int) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadStore
    (cartesianShape xs)

/-- Canonical globally segmented read store for the final query on `xs`. -/
abbrev globalReadStore (xs : List Int) : WordRAM.ReadStore :=
  SuccinctFinal.concreteBPNativeSuccinctRMQGlobalReadStore
    (cartesianShape xs)

/-- List-facing final footprint agreement for two supplied read stores. -/
abbrev storesAgreeOnFootprint
    (xs : List Int) (storeA storeB : WordRAM.ReadStore) : Prop :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnFootprint
    (cartesianShape xs) storeA storeB

/-- Final globally segmented WordRAM trace result for the query on `xs`. -/
abbrev flatPayloadTraceResult
    (xs : List Int) (left right : Nat) :
    WordRAM.TraceResult (Option Nat) :=
  SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
    (cartesianShape xs) left right

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
  (flatPayloadLayout xs).payload = buildPayload xs /\
    (let layout := flatPayloadLayout xs
     layout.payload =
      layout.bpCodePayload ++ layout.accessRankPayload ++
        layout.selectPayload ++ layout.accessPadding ++
          layout.closePayload ++ layout.closePadding) /\
    SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentBackingsAll
      (cartesianShape xs) /\
    (forall {segment index : Nat} {word : List Bool},
      (flatPayloadReadStore xs).readWord? segment index = some word ->
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadSourceManifest
          (cartesianShape xs) segment index word) /\
    (forall {segment index : Nat} {word : List Bool},
      (flatPayloadReadStore xs).readWord? segment index = some word ->
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          (cartesianShape xs) segment ->
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          (cartesianShape xs) segment index word) /\
    (forall {segment index : Nat} {word : List Bool},
      List.Mem (WordRAM.TraceEvent.readWord segment index (some word))
        (flatPayloadTraceResult xs left right).trace ->
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
          (cartesianShape xs) segment /\
        SuccinctFinal.concreteBPNativeSuccinctRMQFlatPayloadReadBacked
          (cartesianShape xs) segment index word) /\
    queryCosted xs left right =
      (flatPayloadTraceResult xs left right).toCosted /\
    queryCosted xs left right =
      SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted
        (cartesianShape xs) left right /\
    (forall event,
      List.Mem event (flatPayloadTraceResult xs left right).trace ->
        event.isReadWord \/ event.isWordPrimitive) /\
    (forall event,
      List.Mem event (flatPayloadTraceResult xs left right).trace ->
        event.matchesReadStore (flatPayloadReadStore xs)) /\
    (forall event,
      List.Mem event (flatPayloadTraceResult xs left right).trace ->
        Not event.isSyntheticCostOnlyPrimitive) /\
    (forall event,
      List.Mem event (flatPayloadTraceResult xs left right).trace ->
        SuccinctFinal.concreteBPNativeTraceEventReadAddressFitsInBits
          (flatPayloadTraceEventBits xs left right) event) /\
    (forall event,
      List.Mem event (flatPayloadTraceResult xs left right).trace ->
        SuccinctFinal.concreteBPNativeTraceEventPrimitiveOperandsFitInBits
          (flatPayloadTraceEventBits xs left right) event)

/--
The final query trace for an ordinary list is backed by the concrete flat
payload layout and contains no synthetic cost-only trace events.
-/
theorem flatPayloadStoreNoSyntheticExecutionStory
    (xs : List Int) (left right : Nat) :
    FlatPayloadStoreNoSyntheticExecutionStory xs left right := by
  simpa [FlatPayloadStoreNoSyntheticExecutionStory, flatPayloadLayout,
    flatPayloadReadStore, flatPayloadTraceResult, flatPayloadTraceEventBits,
    buildPayload, queryCosted] using
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryFlatPayloadStore_noSynthetic_execution_story
      (cartesianShape xs) left right

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
    SuccinctFinal.concreteBPNativeSuccinctRMQOverhead_littleO
      SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily

/-- The built payload has exactly `2*n + overhead n` bits. -/
theorem buildPayload_length (xs : List Int) :
    (buildPayload xs).length =
      2 * xs.length + overhead xs.length := by
  have hshape :
      List.Mem (cartesianShape xs)
        (Cartesian.shapesOfSize xs.length) := by
    exact
      Cartesian.shapeOfSize_mem_shapesOfSize
        (by simpa [cartesianShape] using Cartesian.shape_shapeOfSize xs)
  simpa [buildPayload, overhead] using
    SuccinctFinal.concreteBPNativeSuccinctRMQPayload_length
      SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily
      hshape

/-- Every query has the constant modeled cost of the final construction. -/
theorem queryCosted_cost_le_routeSplit
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost <= routeSplitQueryCost xs := by
  simpa [queryCosted, routeSplitQueryCost] using
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_routeSplit
      (cartesianShape xs) left right

/-- Every query has the clean fixed all-size modeled cost bound. -/
theorem queryCosted_cost_le
    (xs : List Int) (left right : Nat) :
    (queryCosted xs left right).cost <= queryCost := by
  simpa [queryCosted, queryCost] using
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_cleanAllSize
      (cartesianShape xs) left right

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
  simpa [queryCostedWithStore, queryCosted, storesAgreeOnFootprint,
    globalReadStore] using
    SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_eq_global_of_footprint
      (cartesianShape xs) store hfoot left right

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

/--
Under the Ready-threshold size condition, footprint agreement transfers the
fast-regime final model cost bound to the supplied-store list-facing query.
-/
theorem listIntFastRegimeFinalFullModelCostLeOfFootprintGlobal
    (xs : List Int) {store : WordRAM.ReadStore}
    (hfoot : storesAgreeOnFootprint xs store (globalReadStore xs))
    (hsize :
      SuccinctClose.concreteBPRelativeRmmInteriorReadyThreshold <=
        (cartesianShape xs).size)
    (left right : Nat) :
    (queryCostedWithStore xs store left right).cost <=
      SuccinctFinal.concreteBPNativeSuccinctRMQFastRegimeQueryCost := by
  simpa [queryCostedWithStore, storesAgreeOnFootprint, globalReadStore] using
    SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_of_size_ge_readyThreshold
      (shape := cartesianShape xs) (store := store)
      hfoot hsize left right

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
          simpa [queryCosted] using
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
  have hshape :
      List.Mem (cartesianShape xs)
        (Cartesian.shapesOfSize xs.length) := by
    exact
      Cartesian.shapeOfSize_mem_shapesOfSize
        (by simpa [cartesianShape] using Cartesian.shape_shapeOfSize xs)
  calc
    (queryCostedWithStore xs store left (left + len)).erase =
        some (scanWindow (cartesianShape xs).representative left len) := by
          simpa [queryCostedWithStore, storesAgreeOnFootprint,
            globalReadStore] using
            SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_exact_of_footprint_global
              (n := xs.length) (shape := cartesianShape xs)
              hshape hfoot hlen hbound
    _ = some (scanWindow xs left len) := by
          rw [scanWindow_cartesianShape_representative_eq xs hlen hbound]

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

For every `xs : List Int`, `buildPayload xs` has length
`2 * xs.length + overhead xs.length` with `overhead = o(n)`, and
`queryCosted xs` answers valid half-open RMQ queries exactly with leftmost ties
within the constant modeled query budget `queryCost`.
-/
theorem listInt_two_n_plus_o_constant_query_profile :
    SuccinctSpace.LittleOLinear overhead /\
      forall xs : List Int,
        (buildPayload xs).length =
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
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
        (buildPayload xs).length =
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
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
          (fun hlen hbound => queryCosted_exact xs hlen hbound)
          (And.intro
            (fun hlen hbound hquery =>
              queryCosted_leftmost xs hlen hbound hquery)
            (fun left right =>
              flatPayloadStoreNoSyntheticExecutionStory xs left right))))

/--
Named public capstone: the no-synthetic flat execution story uses the same
`2*n + o(n)` advertised payload `buildPayload xs`, with every actual
successful read backed by the counted flat layout.
-/
theorem listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story :
    SuccinctSpace.LittleOLinear overhead /\
      forall xs : List Int,
        (buildPayload xs).length =
          2 * xs.length + overhead xs.length /\
        (forall left right,
          (queryCosted xs left right).cost <= queryCost) /\
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
