# RMQ Family Summary

Snapshot: 2026-06-20, after the first table/access, payload, indexed LCA
query-cost, Fischer-Heun-backed LCA model, traced sparse-query substrate,
fixed-length exact-RMQ space sandwich, payload-lower-bound hub adapter,
packed plus-minus-one RMQ/LCA model layer, uniform charged-budget lower-bound
theorems, reusable hub import surface layers, and the first certified
broadword/succinct-space profile interface, now including a BP-native shape
payload and close-navigation RMQ adapter.

This document is the family-level map for the current Lean development. It
records the module dependency DAG, correctness and cost status by structure,
modeling scope notes, and declaration inventories. The theorem inventory lists
public theorem declarations by module; private helper theorems are listed in a
separate appendix.

## Status At A Glance

- Core contract: half-open RMQ ranges `[left, right)` over `List Int`, returning
  the leftmost minimum index when `left < right` and `right <= xs.length`.
- Exact public RMQ backends: linear scan, plus-minus-one linear instance,
  sparse table, memoized sparse table, hybrid block, recursive hybrid, raw
  whole-list microtable, and value-level Fischer-Heun.
- Exact LCA bridge: generated Euler traces plus exact RMQ backends induce exact
  LCA backends, and certified LCA encodings induce exact RMQ backends.
- Reverse RMQ-to-LCA witness: the built Cartesian tree supplies a concrete
  `RMQToLCAReduction`.
- Cost/model layer: Mathlib-free `Costed` monad, generic indexed-access and
  payload-accounting views, sparse-table build/query costs,
  recursive-hybrid build recurrence solved linear, raw microtable lookup/count
  profile, assembled Fischer-Heun linear-build/constant-supplied-query
  profile, and costed LCA-via-RMQ bridge wrappers, including an explicit
  indexed-access query path that charges first-occurrence reads, a supplied
  RMQ query, and the returned-node read. The canonical Fischer-Heun-backed LCA
  wrapper now instantiates that path with a concrete large-regime query bound.
  The cost-headline LCA path is the dense-label direct-address built query
  state backed by a counted first-occurrence-table builder. The dense LCA
  profile now also has counted Euler node/depth Array views, an assembled
  preprocessing-plus-query theorem, and a normalized demo-facing
  linear-build/constant-query theorem,
  `denseLCA_linearBuild_constantQuery_profile`.
- Derived-cost substrate: `Core.RAM` defines a tiny traced primitive-operation
  model and `Impl.SparseTableInstrumented` proves Array-backed sparse-table
  cell, row, and query refinements with derived trace bounds.
- Reusable hub surface: `RMQ.Core.ModelHub` and the standalone `RMQHub` Lake
  target collect the RMQ-free
  `Cost`/`RAM`/`Refine`/`TableModel`/`LowerBound`/`PayloadLowerBound` layer;
  `scripts/hub_axiom_check.lean` checks that surface without importing the RMQ
  spoke. The payload layer now includes both pointwise and uniform charged
  payload-budget lower bounds.
- Lower-bound layer: fixed-length lossless Cartesian-shape capacity theorem,
  exact-RMQ-decoder bridge, Mathlib-free Remy-style proof of
  `2^(2*n) <= (2*n+1)^2 * shapeCount n`, and the resulting no-premise
  logarithmic-slack bit lower bound. A canonical representative state encoding
  now instantiates the abstract state-encoding adapter, and
  `Impl.FischerHeun` adds a Fischer-Heun-shaped state encoder that separates
  counted payload bits from proof-only built-state fields. The
  `ExactRMQSpaceBounds` wrapper and its canonical/Fischer-Heun-shaped
  instantiations now give a non-vacuous fixed-length `2*n` upper witness paired
  with the universal logarithmic-slack lower bound.
- Shape sample layer: recursive canonical representative arrays are proved for
  every Cartesian shape, with exact length and computed-shape theorems. These
  witnesses now feed the concrete baseline state-encoding instance.
- Succinct layer: normalized plus-minus-one delta signatures, exact
  rank/select primitives, balanced-parentheses predicates, model-level packed
  rank/select with unit-cost query theorems, generated Euler-tour parentheses
  proved balanced and depth-exact, and a packed-payload plus-minus-one RMQ
  model over a fixed exact signature table. A reduction-facing succinct adapter
  now turns both generic plus-minus-one backends and the concrete packed
  Euler-parentheses backend into tree LCA backends; `Impl.LCACost` specializes
  the indexed LCA query path to that packed backend with a `<= 4` modeled-read
  capstone. `Core.SuccinctSpace` now names the final broadword theorem shape:
  counted auxiliary payload, constant costed payload-only queries, exact RMQ
  refinement, an explicit Mathlib-free `o(n)` overhead predicate, closure
  lemmas for combining component overheads, exact-to-budget padding, and a
  componentized BP-directory profile. It also exposes the concrete packed
  rank/select component boundary and a balanced-parentheses access layer for
  generated Euler-tour parentheses, including transported prefix balance,
  final balance, and two-rank excess cost bounds. The Cartesian-shape BP code
  is now proved balanced with exact length `2*n`, and `bpCloseOfInorder?`
  proves that closing-parenthesis rank recovers inorder/RMQ indices.

## Dependency DAG

```mermaid
flowchart TD
  Std["Lean/Std + omega"]

  Std --> Spec["Core.Spec"]
  Std --> Cost["Core.Cost"]
  Cost --> RAM["Core.RAM"]
  Cost --> TableModel["Core.TableModel"]
  Std --> LowerBoundHub["Core.LowerBound"]
  TableModel --> PayloadLowerBound["Core.PayloadLowerBound"]
  LowerBoundHub["Core.LowerBound"] --> PayloadLowerBound

  Spec --> Window["Core.Window"]
  Window --> Backend["Core.Backend"]
  Spec --> Schedule["Core.Schedule"]

  Backend --> LinearScan["Impl.LinearScan"]
  Backend --> SparseTable["Impl.SparseTable"]
  Backend --> LCA["Core.LCA"]
  LCA --> PlusMinusOneCore["Core.PlusMinusOne"]
  PlusMinusOneCore --> Succinct["Core.Succinct"]
  Succinct --> SuccinctSpace["Core.SuccinctSpace"]
  SuccinctSpace --> SuccinctRankProposal["Core.SuccinctRankProposal"]
  SuccinctSpace --> SuccinctSelectProposal["Core.SuccinctSelectProposal"]
  EncodingLowerBound --> SuccinctSpace
  LCA --> Reduction["Core.Reduction"]
  Succinct --> SuccinctReduction["Core.SuccinctReduction"]
  Reduction --> SuccinctReduction
  Reduction --> Cartesian["Core.Cartesian"]
  Cartesian --> Shape["Core.Shape"]
  Shape --> EncodingLowerBound["Core.EncodingLowerBound"]
  TableModel --> EncodingLowerBound
  PayloadLowerBound --> EncodingLowerBound
  Shape --> Microtable["Core.Microtable"]

  Cost --> CostKernels["Core.CostKernels"]
  Microtable --> CostKernels
  TableModel --> Succinct

  Schedule --> Recursion["Core.Recursion"]
  Backend --> Recursion
  Window --> Recursion

  RAM --> SparseTableInstrumented["Impl.SparseTableInstrumented"]
  SparseTable --> SparseTableInstrumented
  SparseTable --> SparseTableMemoCost["Impl.SparseTableMemoCost"]
  Cost --> SparseTableMemoCost

  Window --> HybridBlock["Impl.HybridBlock"]
  LinearScan --> HybridBlock
  SparseTable --> HybridBlock

  PlusMinusOneCore --> PlusMinusOneImpl["Impl.PlusMinusOne"]
  LinearScan --> PlusMinusOneImpl

  Schedule --> RecursiveHybrid["Impl.RecursiveHybrid"]
  Recursion --> RecursiveHybrid
  LinearScan --> RecursiveHybrid

  CostKernels --> RecursiveHybridCost["Impl.RecursiveHybridCost"]
  RecursiveHybrid --> RecursiveHybridCost

  RecursiveHybridCost --> FischerHeunCost["Impl.FischerHeunCost"]
  SparseTableMemoCost --> FischerHeunCost
  Reduction --> LCACost["Impl.LCACost"]
  SuccinctReduction --> LCACost
  Cost --> LCACost
  LCACost --> LCAFischerHeun["Impl.LCAFischerHeun"]

  Microtable --> FischerHeun["Impl.FischerHeun"]
  RecursiveHybrid --> FischerHeun
  SparseTableMemoCost --> FischerHeun
  FischerHeunCost --> FischerHeun
  FischerHeun --> LCAFischerHeun

  Microtable --> Equivalence["Impl.Equivalence"]
  LinearScan --> Equivalence
  SparseTable --> Equivalence
  SparseTableMemoCost --> Equivalence
  HybridBlock --> Equivalence
  RecursiveHybrid --> Equivalence
  FischerHeun --> Equivalence
```

`RMQ.lean` imports the full family root.

## Correctness And Cost Status

| Structure | Correctness status | Cost status | Notes |
| --- | --- | --- | --- |
| Core RMQ spec and backend contract | `LeftmostArgMin`, `CandidateExact`, `RMQBackend`, and contract-level backend equality are proved. | No cost model here. | All public RMQ backends target the same half-open leftmost-argmin contract. |
| Traced RAM substrate | `Core.RAM` defines primitive operation traces, derived `steps`, and a `toCosted` bridge whose cost is definitionally the trace length. The raw primitive constructor is internal; clients build programs through typed primitives such as branches, reads, writes, comparisons, allocations, and array pushes. | Primitive branches, Array reads/writes, integer comparisons, Array allocations, and Array pushes each contribute one trace operation. | This is a hardened shallow trace substrate, not yet a full first-order interpreter. It is currently used by the sparse-table query and memoized-build bridge, and now by the dense LCA first-occurrence builder. |
| Reusable model hub | `RMQ.Core.ModelHub` imports exactly the RMQ-free model layer: `Cost`, `RAM`, `Refine`, `TableModel`, `LowerBound`, and `PayloadLowerBound`. The standalone `RMQHub` Lake target imports the same barrel. | No algorithmic cost claim by itself; the hub exposes the cost, trace, refinement, table, payload, capacity, payload-accounted finite-encoding APIs, and uniform charged-budget lower-bound theorems used by the spoke. | This is the first extraction test: the hub builds and has a hub-only axiom gate without importing RMQ specs, Cartesian shapes, LCA, or implementations. |
| Refinement and table/access model | `Core.Refine` now owns `StoredSeq` and `StoredMatrix`, reusable Array/List erasure certificates for one-dimensional direct-address tables and list-of-lists tables. `Core.TableModel` keeps generic indexed access, finite indexed sequences, list-backed reference adapters, compatibility aliases for both stored views, unit-cost modeled reads, and payload views with uncharged auxiliary-state extension. | Indexed reads cost `indexedReadCost = 1`; payload views track serialized payload bits and a charged bit budget. | This keeps List tables as reference semantics while letting executable Array-backed representations prove erasure/refinement once at the boundary. Sparse-table stored queries and Fischer-Heun summary tables use `Refine.StoredMatrix`; dense LCA first-occurrence reads now use `Refine.StoredSeq`. |
| Linear scan | Exact query, soundness, completeness, invalid-range rejection, backend. | Costed scan kernel exists in `Core.CostKernels`; no separate backend-level cost wrapper. | Direct reference backend. |
| Plus-minus-one RMQ | `Core.PlusMinusOne` packages `AdjacentDepthsDifferByOne` as a first-class RMQ input, adds delta-signature replay, and proves a certified normalized signature-table contract. Euler traces, generated rose-tree Euler depths, and generated Euler-tour parenthesis bits instantiate the invariant directly. | The old raw constant-cost packed PM1 wrapper has been retired; remaining packed PM1 facts are exact value/reference scaffolding, not the final broadword query-cost model. | `Impl.PlusMinusOne` provides both the conservative linear instance and a normalized delta-signature backend, with contract-level equivalence between them. The packed PM1 model uses the fixed exact signature table as a universal decoder; it is not yet a broadword/block-decomposition implementation. |
| Succinct bit layer | `Core.Succinct` defines exact rank/select over `List Bool`, balanced-parentheses predicates, model-level `PackedBitVector`, `PackedBalancedParens`, `PackedPlusMinusOneRMQ`, and generated Euler-tour parentheses with proofs of balance and depth-trace agreement. `Core.SuccinctReduction` turns a plus-minus-one backend over generated Euler parentheses, including the concrete packed Euler-parentheses backend, into the ordinary RMQ/LCA reduction interface. `Core.SuccinctSpace` adds the certified broadword directory interface and family-level `2*n + o(n)` theorem shape over exact RMQ shape representatives, plus componentized BP-directory overhead accounting, a reusable rank/select directory boundary, payload-live stored-word rank/select components, balanced-parentheses access adapters, and a BP-native Cartesian-shape payload layer. The BP bridge proves `bpCode_balanced`, exact `2*n` BP payload length, inorder close-position existence/bounds, full close-rank count, `bpCloseOfInorder?_rankFalse_succ`, and `select_false_bpCode_eq_bpCloseOfInorder?`. `Core.SuccinctRankProposal` and `Core.SuccinctSelectProposal` isolate the sampled rank/select builder targets. | The packed/reference rank/select and packed PM1 wrappers erase to exact List-level semantics and are useful correctness scaffolding, but their old raw constant-cost profiles are retired: they wrapped aggregate reference computations instead of reading from a real o(n)-bit directory. The faithful rebuild now has both word primitives: `RAM.rankBoolWordPrefix` and `RAM.selectBoolWord`. `Succinct.select_min_length_eq` adds the select-side clamping fact needed for finite locator tables. `SuccinctSpace.StoredWordRankData.rankCostedClamped_exact` gives total rank via a valid stored-read path plus clamping; `SuccinctSpace.FixedWidthNatTable.profile`, `SuccinctSpace.FixedWidthRankSampleTables.profile`, and `SuccinctSpace.PayloadLiveStoredWordRankData.profile` add a payload-live fixed-width sample layer for rank, with `ofEncodedWords_profile` and `ofEntries_profile` constructors tying bounded entries or explicit encoded word lists to the charged payload. `SuccinctSpace.StoredWordSelectData.selectCosted_profile` gives select via a locator read, payload-word read, and word-select primitive; `SuccinctSpace.FixedWidthSelectSampleTable.profile`, `SuccinctSpace.FixedWidthSelectSampleTables.profile`, and `SuccinctSpace.PayloadLiveStoredWordSelectData.profile` add the analogous payload-live fixed-width locator layer for select, again with encoded-word and bounded-entry constructors. `SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankSelectData_profile` combines the payload-live rank/select components; `SuccinctSpace.BalancedParensAccess.ofPayloadLiveStoredWordRankSelectData_profile` and `SuccinctSpace.BalancedParensAccess.ofShapePayloadLiveStoredWordRankSelectData_close_profile` lift them to BP rank/select/excess access and the Cartesian close-select/rank-close legs with cost `<= 3`; `SuccinctSpace.FixedWidthOptionNatTable.profile`, `SuccinctSpace.PayloadLiveBPCloseLCADirectory.profile`, and `SuccinctSpace.PayloadLiveBPCloseLCADirectory.ofEntries_profile` add the payload-live fixed-width optional-close table for BP LCA-close navigation. The older payload-backed stored-word layer remains as compatibility scaffolding for intermediate migration theorems, but the current BP-native path uses payload-live rank/select plus payload-live LCA-close. `SuccinctSpace.BPBroadwordRMQDirectory` is the BP-native `shape.bpCode ++ aux` payload counterpart to the older canonical full-code-tail directory. `BPCloseRMQNavigationDirectory.queryEncodedCosted_exact` proves the abstract select-close, LCA-close, rank-close composition exact; `PayloadLiveBPCloseRMQNavigationDirectory.profile` proves the stateful built-query version exact with cost `<= 10`, `WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_bounded_built_query_profile` adds bounded stored-word discipline, and `WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_word_bounded_encoded_query_profile` gives the sampled payload-only theorem target with bounded rank/select payload words. `SuccinctSpace.logLogSampledDirectoryOverhead_littleO` now supplies the Mathlib-free `n/log n * log log n = o(n)` arithmetic needed for local two-level delta tables. `SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt` proves strict-position chunk presence. `SuccinctRankProposal` now has canonical super/block rank sample entries, fixed-width sample-table constructors, presence/bound lemmas, chunk-local rank exactness for ordinary chunks, `ofChunks_word_present_of_lt`, `CanonicalRankWordBridge`, and `canonicalTwoLevelRankDataOfBridge`/`canonicalTwoLevelRankDataOfChunksPresent`, plus canonical two-level rank overhead lemmas, reducing the remaining rank construction gap to the endpoint word-presence convention. `SuccinctSelectProposal` now has canonical coarse/local select locator entries, fixed-width locator-table constructors, bounded finite-table query clamping, `CanonicalSelectWordBridge`, `canonicalTwoLevelSelectData`, canonical two-level select/rank-select overhead lemmas, and the `SelectSampleWordExact` handoff for the remaining concrete sample-word proof. `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile` combines the two-level rank/select components into the generic `RankSelectDirectory` and `BalancedParensAccessFamily` contracts; `word_bounded_constant_query_profile` additionally exposes the machine-word payload-store bounds. `SuccinctSelectProposal.TwoLevelEncodedBPCloseRMQNavigationFamily.two_n_plus_o_encoded_query_profile` gives the two-level BP close-navigation payload-encoded profile with explicit encoded-function agreement on built payloads. | The BP-native query theorem now has payload-live rank/select and close-navigation migration boundaries, including two-level stateful and encoded close-navigation profiles, but the final concrete broadword sampled-directory builders are still unfinished. The single-level sampled-rank wrapper is a migration scaffold; the final word-RAM rank/select construction should instantiate the two-level interfaces so one-step `wordRank`/`wordSelect` is only used on machine-sized words. The next hard obligations are the rank endpoint/sentinel convention, the concrete select word bridge for the chosen payload store, a real succinct BP close/LCA entry scheme rather than a dense pair table, and the final two-level encoded BP close-navigation family instance. |
| Sparse table | Exact materialized sparse table query and backend. `SparseTableInstrumented` replays cell construction, counted array row pushes, memoized log-row building, supplied-table querying, and build-then-query execution through Array-facing primitive traces and refines the verified List definitions. | The obsolete `SparseTableCost` build/fresh-query module has been retired. `SparseTableInstrumented` gives derived trace bounds for cells, rows, the memoized log-row build, stored supplied-table queries, and a build-then-query execution, with headline theorems `memoBuild_refine_with_steps`, `memoBuild_and_query_refine_with_steps`, and `memoQueryWithTracedBuild_refine_with_steps`. | The traced query guard uses `Array.size`, not `List.length`, so the constant-step query statement no longer hides list materialization in the validity check. Generic Array-table/List-table refinement is factored through `Refine.StoredMatrix` row/cell erasure, `queryFromArrayTable_value_of_refines`, and `queryFromStoredTable`. |
| Memoized sparse table | Memoized build is extensionally equivalent to the verified sparse table, with backend and build-cost theorems for Fischer-Heun summaries. `SparseTableInstrumented.memoBuild_refine_with_steps` and `memoBuild_and_query_refine_with_steps` give the same log-row build a derived primitive-trace implementation over Arrays. | Exact log-row build cost formula, memo row count, a traced Array build bound, and a true build-then-query trace bound of `memoBuildSparseTableArraySteps xs.length + 7`. | This is the cost-faithful sparse-table builder used by Fischer-Heun summaries. The old fresh sparse-table query `Costed` wrapper was retired; Fischer-Heun's summary query now consumes a `Refine.StoredMatrix`/`StoredTable` Array representation. |
| Hybrid block | Exact public hybrid backend with boundary scans and sparse middle summaries. | No first-class cost profile yet. | Useful proof predecessor for the recursive and Fischer-Heun schedules. |
| Recursive hybrid | Exact public recursive backend via `recurseOnSummary`. | Build recurrence solved: `buildCost xs <= 2 * xs.length`; query-step costed erasure and cost formula with supplied summary query. | End-to-end recursive query bound is still not the flagship result; Fischer-Heun now carries the constant-query story. |
| Shape and microtable core | Shape/RMQ behavior equivalence, exact fixed-size shape signatures, recursive canonical representative arrays, shape universe count, certified raw local microtable, exact in-block backend. | Raw shape lookup cost bounded by `blockSize + 1`; shape count bounded by Catalan envelope `shapeCount b <= 4^b`. | The local theorem is now consumed by `Impl.FischerHeun`; representative arrays now provide concrete shape witnesses for lower-bound interfaces. |
| Encoding lower-bound scaffold | `Core.LowerBound` factors the generic finite bitstring universe, finite-domain lossless encoding interface, injection/capacity theorem, and logarithmic-slack arithmetic bridge. `Core.PayloadLowerBound` adds the reusable adapter from payload-accounted built states to fixed-length lossless encodings, plus `PayloadSpaceBounds` for two-sided finite-domain payload-space packages. `Core.EncodingLowerBound` instantiates that hub layer for Cartesian shapes: fixed-length lossless shape encodings must have at least `shapeCount n` available bitstrings; exact RMQ query decoders over representative arrays induce such encodings; and a Remy-style insertion/counting proof establishes `2^(2*n) <= (2*n+1)^2 * shapeCount n`, yielding the concrete no-premise `2*n - (2*log2(2*n+1)+2)` bit lower bound. Concrete state encodings adapt through `ExactRMQStateEncoding`, the baseline canonical representative payload instantiates it, and `Impl.FischerHeun.stateEncoding` gives a one-block Fischer-Heun-shaped instance. `ExactRMQSpaceBounds`, `canonicalRepresentativeSpaceBounds`, and `exactRMQ_two_sided_log_slack_space_bound` package the coarse fixed-length lower/upper sandwich; `exactRMQ_tight_fixed_length_payload_space_bound` is the sharper capstone, combining the state-encoding lower bound, uniform charged-payload budget lower bound, and an exact `2*n`-bit canonical upper witness. | No runtime cost model; this is information-theoretic capacity. `PayloadLosslessEncoding.payloadBitCount_ge_bits_of_mem` relates charged payload counts to fixed payload length without identifying them by default, while `lower_le_budget_of_payload_lossless_encoding` and `PayloadSpaceBounds.lower_le_budget` lift count lower bounds to any uniform charged payload budget. | The current concrete instances store the explicit preorder shape payload of length `2*n`; they are exact, non-vacuous fixed-length upper witnesses. Packed constant-time succinct RMQ remains a stronger future refinement. |
| Fischer-Heun value backend | `State` carries block size, raw microtable, block-minimum summary, a List reference summary sparse table, and a `Refine.StoredMatrix` Array representation refining it. `SummaryTableRefines` records when a supplied state carries the canonical memoized sparse table for an input, and `liftedSummaryStoredQuery_refines_recursiveMiddle_with_steps` proves the stored middle leg refines the recursive middle candidate with at most seven traced steps. `StoredMicrotableView` reads a stored block signature and then a shape/query slot; exact-input and padded-input stored views are proved extensionally equal to the supplied state's certified local microtable when the block index is in range. `queryWithState` composes padded local microtable lookups for same-block/boundary windows with the recursive-middle summary query. Exactness, soundness, completeness, invalid rejection, backend wrappers, and an all-input wrapper are proved. | `buildWithBlockSizeCosted` erases to `buildWithBlockSize` and costs exactly `buildCost`; the raw microtable build folds over shape rows and local-query slots; `queryWithStateCosted` now charges stored signature/slot microtable reads, the stored Array-backed summary sparse-table query, and combines; fresh-query and all-input cost/run theorems compose both costs. Positive-block supplied query cost is bounded by `13`; `fischerHeun_refines_with_steps` bundles supplied-query value refinement with the large-regime constant query bound, and `fischerHeun_fresh_refines_with_build_query_steps_of_large` bundles fresh-query value refinement with `buildCost <= 15 * xs.length` and total fresh cost `<= 15 * xs.length + 13`. | The supplied-query budget is an upper bound because the traced sparse-table query may do fewer than seven steps when a candidate is absent. The all-input wrapper is exact and costed, with linear scan outside the large canonical regime. |
| Fischer-Heun cost profile | Correctness-independent counting/cost assumptions are packaged as theorem premises and canonical corollaries. | `buildCost <= 15 * xs.length`; supplied query budget `<= 13`; canonical theorem discharges budgets when `16 <= canonicalBlockSize xs`. | Cost claims are scoped to the RAM/unit-cost indexed-access model. |
| LCA from RMQ | Generated Euler trace plus `TracePathAgreement` turns an exact RMQ backend over depths into an exact `LCABackend`; unique labels discharge trace/path agreement structurally. `LabelsBoundedBySize` and `DenseNatLabels` now name the dense/preindexed node-ID regime used by cost headlines without removing arbitrary-label correctness. The generated Euler-parentheses plus-minus-one input has a dedicated LCA adapter, including the concrete packed PM1 backend. `Impl.LCAFischerHeun` instantiates the bridge with canonical and all-input Fischer-Heun RMQ backends. | `Impl.LCACost` gives costed Euler-trace construction, the original abstract supplied-backend query wrapper, an explicit indexed-access LCA-via-RMQ query path, and an Euler-parentheses plus-minus-one wrapper over that path. `queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_labelsUnique` specializes this route to the packed PM1 backend with path-LCA soundness and cost `<= 4`. The detailed path uniformly costs at most two first-occurrence reads, one supplied RMQ query, and one returned-node read; successful first-occurrence lookups give an exact cost equation. The earlier association-list first-occurrence path has been retired; the cost headline uses the direct-address dense first-occurrence table. The dense table has a counted RAM builder with value erasure to the direct rows and step bound `labelsPreorder.length + 1 + 3 * eulerTrace.nodes.length`; Euler node/depth Array views now share the generic `RAM.arrayOfList` builder. `Impl.LCAFischerHeun` proves trace-read, dense built-state, first-occurrence-build-plus-dense-query, full dense component-preprocessing-plus-query path-LCA capstones, and the normalized `denseLCA_linearBuild_constantQuery_profile` with preprocessing cost bounded by `22 * eulerTrace.nodes.length + 3`, large-regime query cost `<= 16`, and combined cost bounded by that linear budget plus `16`. | The association-list cost wrapper and LCA capstones were retired because lookup is linear. The dense preprocessing theorem is an assembled component-budget theorem rather than one monolithic `RAM.Exec` program. The packed PM1 LCA route is still supplied-query/table-model level, not yet a BP-native LCA structure. |
| RMQ from LCA | `RMQToLCAReduction` plus an exact LCA backend gives an exact RMQ backend. | No cost profile yet. | `Core.Cartesian` supplies a concrete certified reduction for RMQ intervals. |
| Equivalence layer | Contract-level equality proved among linear scan, sparse table, memo sparse table, hybrid block, recursive hybrid, raw whole-list microtable, canonical Fischer-Heun, and all-input Fischer-Heun. | No cost layer. | Uses the generic backend contract rather than implementation-specific reasoning. |

## Consolidated Scope Notes

Succinct E1 update: the concrete two-level rank/select chunk-backed path has
advanced beyond the older table-row wording above. Rank now has the
sentinel-backed `canonicalTwoLevelRankDataOfChunksExact_profile` and the
local-span variant
`canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile`, whose block-table
field width is justified by `blocksPerSuper * wordSize` instead of
`bits.length`; select has slice-local word exactness and
`canonicalTwoLevelSelectDataOfChunksExact_selectCosted_profile`; the combined
`canonicalTwoLevelRankSelectDirectoryOfChunksExact_profile` and
`canonicalTwoLevelBalancedParensAccessOfChunksExact_profile` lift the global
width identity-index path, while the `...LocalRankBlock_profile` variants lift
the reduced rank-block parameter. The select-side two-level API now routes
local locator reads through an explicit block index, so the reusable
payload-live/exact/profile layer no longer forces one local table word at every
occurrence index; the canonical finite constructor remains the old identity
index witness until a concrete dense/sparse select builder supplies compact
block indexes. `SuccinctCloseProposal.BlockMicroCodebook.profile` and
`SuccinctCloseProposal.MacroMicroBPCloseLCADirectory.profile` add the
close-LCA micro-codebook/fallback skeleton that the final BP navigation layer
should instantiate. `SuccinctCloseProposal.BlockCodeTable.profile`,
`SuccinctCloseProposal.PayloadLiveBlockMicroCodebook.profile`, and
`SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCAFamily.profile` move that
path to a charged per-block code classifier plus componentwise LittleOLinear
codebook/macro overhead.
`SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile`
now consumes that payload-live macro/micro LCA family together with
payload-live rank/select data, giving a built-query BP close-navigation profile
with payload length `2*n + o(n)` and query cost `<= 9 + lcaQueryCost`. The
remaining BP-native succinct gaps are the concrete dense/sparse select
descriptor behind the block-indexed API, a concrete macro directory
implementation behind the new macro interface, and then an encoded/payload-only
version of this join. They are no longer rank endpoint, rank local-width,
proof-only block-code, select API-shape, or built-query close-navigation
blockers.
`SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient` pins the first
macro-design blocker: a macro keyed only by endpoint close-block pairs is false
even on a four-node right spine, so the concrete macro must store
endpoint-sensitive fringe information or use a real BP excess/RMQ macro.
`SuccinctCloseProposal.denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile`
then wires the most direct endpoint-sensitive fallback into the payload-live
macro/micro surface with charged reads and exact answers, while
`SuccinctCloseProposal.denseAllCloseBPCloseLCAOverhead_not_littleO` proves that
this dense all-close table is not an `o(n)` auxiliary payload. The remaining
macro fork is therefore not another wrapper around `macroCosted`, but a real
succinct BP-excess/RMQ macro with charged endpoint-fringe repair.
`SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.profile` and
`SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_sampled_profile` now
land the first positive charged substrate for that fork: each block stores
fixed-width minimum and maximum BP-excess samples, the query reads those payload
words with cost `<= 2`, and the sampled-overhead version is tied to a named
`LittleOLinear` budget.
`SuccinctCloseProposal.compactBPCloseSummaryPayloadOverhead_littleO` and
`SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_compact_summary_profile`
package that table under the intended compact close-summary envelope: a
log-log sampled block-code term plus sampled universal micro, block-summary,
and superblock-summary terms, with no dense endpoint-pair or interior block-pair
payload. The absolute-width compact profile is only a warning boundary, not the
final budget witness. `SuccinctCloseProposal.relativeBPCloseSummaryPayloadOverhead_littleO`
and
`SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile`
now add the missing relative/log-log version: sparse absolute superblock
baselines are stored in a sampled directory, while each block stores shifted
min/max excess deltas and a local argmin offset in a
`logLogSampledDirectoryOverhead` payload. The theorem proves the concrete table
length under those two envelopes directly, rather than assuming a compact
budget for absolute `Theta(log n)` block summaries.
`SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile`
then plugs the same concrete relative table into
`compactBPCloseSummaryPayloadOverhead`, using the log-log term for relative
block summaries and the sampled term for superblock baselines.
`SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile`
is the no-premise canonical checkpoint: it builds the concrete payload-live
relative table from fixed sampled/log-log slots, proves compact little-o
payload, finite summary-read exactness, cost `<= 4`, and machine-word bounds
for every charged baseline/min/max/arg-offset read.
`SuccinctCloseProposal.canonicalBPRelativeMinMaxArgSummaryTableActive_of_large`
and
`SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large`
now justify and expose the intended raw-parameter branch under an explicit
large-regime condition: enough sampled block density for the sparse baseline
budget, a superblock word width linear in the canonical base, relative
span/arg-width bounds, and relative entries fitting in a machine word. This is
still the block-summary layer; the exact answer-close theorem still has to
connect those relative summaries to endpoint-fringe repair.
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorOverhead_littleO` names the
compact overhead envelope for the intended rmM/min-max-tree interior navigator:
the charged relative summary table, fixed squared-log-log local offset sparse
tables, fixed log-log global macroblock routing, and fixed sampled top-level
routing, with no dense interior block-pair payload.
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large`
packages the large-regime branch equalities, raw cover and positivity facts,
relative-entry machine-word bound, relative-summary read exactness/cost, and
payload bound under that interior envelope so the later concrete interior
directory profile can consume those side conditions directly.
`SuccinctCloseProposal.canonicalBPRelativeSummaryLargeRegime_of_size_ge`
removes that raw regime premise for the canonical option-1 parameters from the
explicit threshold `2^128 <= shape.size`; the proof discharges base density,
the superblock machine-word/base comparison, span and block-size width bounds,
and the relative-width machine-word comparison.  The wrapper
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge`
feeds this threshold theorem into the same interior parameter profile, so the
next concrete directory can consume a size hypothesis instead of a bundled
`canonicalBPRelativeSummaryLargeRegime` assumption.
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge`
adds the two-level budget package A needs next: the concrete relative summary
payload plus local offset sparse tables, global macroblock sparse table, and top
routing all fit under the same `LittleOLinear` interior envelope, while local
offset width, block-count routing capacity, and every charged summary word read
remain machine-word bounded.
`SuccinctCloseProposal.bpTwoLevelInteriorCandidateCosted_erase_exact` is the
payload-backed two-level selector exactness theorem: the query reads local
offset sparse-table candidates, a global macroblock candidate, and relative
summary words, then returns the semantic complete-block range witness without
using `bpRangeArgMinBlock` as an oracle.  The concrete table payload bounds
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge`
and
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge`
connect the built local/global table payloads to the squared-log-log and
log-log reserves.  Finally
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile` packages
the actual two-level interior directory with `LittleOLinear` payload overhead,
query cost `<= SuccinctCloseProposal.concreteBPRelativeRmmInteriorQueryCost`,
semantic range-witness exactness, and machine-word bounds for charged reads
under `2^128 <= shape.size`.
`SuccinctCloseProposal.bpExcessAt_prefix_nonnegative` records the
balanced-prefix invariant needed when interpreting the Nat-subtraction excess,
and `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.summary_read_words_length_le_machine`
exposes the machine-word side condition for the charged summary table reads.
The positive C2 macro side now also has position-bearing payload reads:
`SuccinctCloseProposal.PayloadLiveBPRangeMinMaxArgSummaryTable.profile` stores
and reads a per-block argmin prefix position, while
`SuccinctCloseProposal.PayloadLiveBPRangeArgMinWitnessTable.profile` and
`SuccinctCloseProposal.PayloadLiveBPBlockPairRangeWitnessMacro.profile` lift
that idea to charged block-range witnesses and an `lcaCloseCosted`-shaped
block-pair macro candidate. These range witnesses return close candidates from
payload words with cost `<= 2`, expose machine-word read bounds, and have
sampled-overhead profile theorems. The next positive layer now has charged
endpoint repair:
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.profile` combines
left endpoint-fringe prefix witnesses, the existing interior block-range
witness, and right endpoint-fringe prefix witnesses in one counted
`lcaCloseCosted` path with cost `<= 6`;
`SuccinctCloseProposal.concreteBPEndpointFringeRangeMacro_profile` constructs
that path from fixed-width payload tables; and
`SuccinctCloseProposal.concreteBPEndpointFringeRangeMacro_read_words_length_le_machine`
exposes the machine-word bounds for every charged fringe/interior read.
`SuccinctCloseProposal.bpCloseOfInorder?_le_of_le`,
`SuccinctCloseProposal.answerClose_between_endpoint_closes`, and
`SuccinctCloseProposal.answerClose_prefix_between_endpoint_prefixes` start the
BP semantic bridge by proving endpoint containment of the representative-array
answer close. The bridge now also exposes executable prefix-range argmin
correctness via
`SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPos_excess_le_offset`,
`SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess`,
`SuccinctCloseProposal.bpPrefixRangeWitness_eq_of_leftmost_min_excess`,
`SuccinctCloseProposal.bpRangeWitness_eq_of_leftmost_block_candidate`, and
`SuccinctCloseProposal.bpEndpointPrefixRangeMinExcess_le_answerClose`, concrete
endpoint/interior slot decoding through the `endpoint*Entries_get?` and
`interiorBlockPairRange*Entries_get?` lemmas,
root-spanning BP semantic witnesses via
`SuccinctCloseProposal.endpointPrefixRangeWitness_eq_answerClose_of_spanning_root`,
the global representative-query semantic theorem
`SuccinctCloseProposal.answerClose_prefix_leftmost_min_excess_of_query`, and
charged endpoint-merge bridges including
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_merged_candidate`,
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_left_fringe_leftmost`,
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_right_fringe_candidate`,
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_middle_candidate`,
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_spanning_root_left_fringe`,
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_spanning_root_right_fringe`,
and
`SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_query_cross_block`.
The new guarded concrete layer
`SuccinctCloseProposal.PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory.profile`
routes same-block endpoint closes to the charged micro-codebook and cross-block
endpoint closes to the charged endpoint-fringe/interior macro, proving semantic
close/LCA exactness with query cost `<= 6`.
`SuccinctCloseProposal.concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile`
combines that concrete macro with a supplied payload-live micro budget and a
sampled `LittleOLinear` endpoint-fringe macro budget. That sampled theorem is
conditional: its macro-budget premise still has to pay for the dense
`interiorBlockPairRanges blockCount` payload, so it is not a concrete
`2*n + o(n)` close-directory witness. The relative-rmM successor surface is
now explicit:
`SuccinctCloseProposal.bpRelativeRmmCandidateMerge_exact` proves the pure
endpoint-fringe/interior/right-fringe merge from the representative-query BP
semantics, so the merge fact is no longer a proof-only field of the relative
macro interface.
`SuccinctCloseProposal.PayloadLiveRelativeRmmBPCloseMacro.lcaCloseCosted_exact_of_query_cross_block`
builds the cross-block query from charged left-fringe, relative-rmM interior,
and right-fringe candidate reads, and
`SuccinctCloseProposal.PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory.profile`
routes same-block queries through the charged micro-codebook while routing
cross-block queries through that relative-rmM macro.
`SuccinctCloseProposal.relativeRmmMacroMicroBPCloseLCADirectory_profile`
packages the resulting answer-close exactness, query-cost bound, and
`LittleOLinear` micro-plus-relative overhead budget without mentioning
`interiorBlockPairRanges blockCount`. The concrete relative/log-log summary
builder still has to instantiate the macro's rmM candidate-read interface.
`SuccinctCloseProposal.PayloadLiveBPRelativeMinMaxArgSummaryTable.rangeScanCosted_erase_exact`
is the honest charged scan over Worker B's relative summary table: every
interior block contributes a charged four-word summary read, and the scan
erases to the exact `(minimum excess, prefix position)` range witness.
`SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_canonical_interior_scan_not_constant`
specializes that scan to the canonical compact relative table and proves it has
no uniform constant query bound for positive block size.  Thus the canonical
relative table is now consumed by an exact payload-live range path, but that
path is formally a blocker rather than the final macro.  The positive path is
the non-scan compact two-level rmM range navigator whose charged query is O(1),
now packaged by
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile` and
consumed below by the compact close directory.
`SuccinctCloseProposal.PayloadLiveBPRelativeRmmInteriorDirectory.profile` now
pins the replacement contract for that navigator, and
`SuccinctCloseProposal.payloadLiveRelativeRmmBPCloseMacroOfInterior_profile`
immediately feeds any such interior directory into the charged
left-fringe/interior/right-fringe relative macro, including machine-word bounds
for the charged words named by `payloadWordsRead`.  The available concrete
two-level instance is now
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile`, and
`SuccinctCloseProposal.concretePayloadLiveRelativeRmmBPCloseMacro_profile`
packages it into a large-regime concrete relative-rmM cross-block macro with
payload bounded by the concrete endpoint-fringe plus two-level interior budget,
query cost `<= 4 + concreteBPRelativeRmmInteriorQueryCost`, semantic
cross-block exactness, and machine-word bounded charged reads.  The remaining
C2 work is now the final BP-native join with rank/select.
`SuccinctCloseProposal.PayloadLiveBlockEndpointFringeCodebook.profile` adds the
compact endpoint-fringe leaf needed to remove dense global
`endpointLeftFringeRanges`/`endpointRightFringeRanges` payloads from that path:
the endpoint candidate is read by a charged per-block code lookup followed by
two charged local min/arg witness reads from a finite per-code table.
`SuccinctCloseProposal.PayloadLiveCompactEndpointRelativeRmmBPCloseMacro.profile`
then consumes those local endpoint-fringe candidates together with the
relative-rmM interior directory, proving cross-block answer-close exactness,
query cost `<= 6 + middleQueryCost`, compact endpoint/interior payload length,
and machine-word bounds for the charged endpoint and interior words.  The
concrete checkpoint
`SuccinctCloseProposal.concretePayloadLiveBlockEndpointFringeCodebook_profile`
instantiates that leaf with a payload-backed block-code table and local
endpoint min/arg tables, while
`SuccinctCloseProposal.concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro_profile`
consumes it with
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile` to give a
charged endpoint+interior macro with explicit payload length, constant query
cost, cross-block exactness, and machine-word bounded reads.  The final compact
directory no longer uses that identity endpoint classifier as its surface:
`SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile` packages
same-block dispatch, charged constant-width local BP-code window reads for
endpoint repair, the concrete relative-rmM interior directory, payload length
bounded by `SuccinctCloseProposal.compactBPCloseOverhead`, the
`SuccinctCloseProposal.compactBPCloseOverhead_littleO` proof, constant query
cost, arbitrary representative-query exactness, and machine-word bounds for
every charged BP/interior word read.  This closes C2 at the bounded-local-BP-
primitive layer: the same-block and endpoint-fringe local primitives are
specified by exact local BP semantics and account for a constant BP-word window,
but the values are not yet derived by an interpreter over those listed words.
`SuccinctCloseProposal.payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle`
records the corresponding contract caveat: the generic interior-directory
record alone can be inhabited by an empty-payload proof-only oracle, so the
named compact C2 path relies on the concrete
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile` rather
than the generic record.
The coordinator-selected C2 path is to replace the dense block-pair/interior
macro payload with the compact rmM/min-max-tree-style interior navigator over
complete-block minimum candidates, prove its constant charged range-min witness
and `LittleOLinear` payload profile, and then package that directory into the
final close-navigation join; this is the path now consumed by
`SuccinctCloseProposal.concreteCompactBPCloseLCADirectory_profile`.
`SuccinctFinal.BPCloseAccessDirectory` and
`SuccinctFinal.PayloadLiveBPCloseAccessFamily.constant_query_profile` now name a
weak false-only BP close-access adapter: `selectCloseCosted` erases to
`bpCloseOfInorder?`, `rankCloseCosted` erases to false-prefix rank over
`shape.bpCode`, and the rank/select payload word reads carry machine-word
bounds. The adapter requires the non-vacuous space obligation as a field,
`payload_length_le_overhead : payload.length <= overhead`; the join consumes
this bound by padding the close-access payload up to the reserved overhead
instead of relying on an uninspected `LittleOLinear` claim. The adapter is not
the final worker target, because its costed operations are fields and can hide
semantic reference computation.
`SuccinctFinal.concreteBPNativeCloseAccessPayload_length_le_overhead` exposes
the shape-indexed bound used by the capstone theorem.
`SuccinctFinal.concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
is the BP-native built-query join over that weak access family plus the concrete
compact close/LCA directory. `SuccinctFinal.ReadBackedBPCloseAccessDirectory`
and `SuccinctFinal.ReadBackedBPCloseAccessFamily.constant_query_profile` are the
hardened two-level adapter: close-select and rank-close are derived from
stored-word rank/select data rather than supplied as arbitrary functions.
`SuccinctFinal.readBackedBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
is the research-facing final-join corollary for that adapter. Its payload is
exactly `shape.bpCode` plus padded auxiliary close-access and close-directory
payloads, the payload length is
`2*n + concreteBPNativeSuccinctRMQOverhead ... n`, the combined overhead is
`LittleOLinear`, the query cost is bounded by
`3 * closeAccessCost + concreteCompactBPCloseQueryCost`, and erasure returns the
exact representative-array RMQ answer. The old two-level rank/select family is
kept only as an adapter via
`SuccinctFinal.concreteBPNativeCloseAccessFamilyOfRankSelectFamily` and the
compatibility corollary
`SuccinctFinal.concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile_of_rankSelectFamily`.
The theorem remains conditional: the repository still needs Worker A's concrete
compact false-select/close-access family witness inhabiting
`ReadBackedBPCloseAccessFamily` with both an `o(n)` overhead and the explicit
`payload.length <= overhead shape.size` bound before the unconditional BP-native
`2*n + o(n), O(1)` theorem is closed. `scripts/succinct_cost_lint.ps1` is wired
into `scripts/gate.ps1` and now flags the audited anti-pattern
`LittleOLinear (fun _ => ...)` in succinct proposal/final source files.
`docs/SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md` pins the C1 path to a
Clark/RRR-style sparse/dense false-select inventory: super samples, explicit
long-super exceptions, local samples, explicit sparse-local exceptions, and a
dense local query that reads at most two aligned payload words before invoking
the counted word-select primitive. This design may require a sibling
close-access/final-join theorem instead of forcing the final construction
through the current one-sample/one-word `TwoLevelPayloadLiveStoredWordSelectData`
shape.
`SuccinctCloseProposal.endpointSummaryBlockMacroDirectory_not_sufficient`
sharpens the C2 blocker: a macro keyed only by endpoint block ids plus the
existing endpoint block min/max summaries still cannot return exact answer
closes, so the next positive construction needs a position-bearing
endpoint/fringe or range-min witness.
`SelectSampleWordExact.selected_position_in_read_word` and
`TwoLevelPayloadLiveStoredWordSelectData.selected_position_in_read_word_of_sample`,
together with the aligned-word refinements
`SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word` and
`TwoLevelPayloadLiveStoredWordSelectData.selected_wordIndex_eq_of_sample`, plus
the paired blocker
`TwoLevelPayloadLiveStoredWordSelectData.shared_local_locator_forces_same_selected_wordIndex`,
make the current select-side design fork explicit: with the present query path,
two successful occurrences answered through the same shared local locator must
lie in the single payload word read by that locator; if the read word is an
aligned machine chunk, both selected positions have the same `pos / wordSize`.
A compact final builder therefore needs a real descriptor that computes that
chunk choice through charged payload, or an extended local dense-block query
path, not just a non-identity `blockIndex`.
`SuccinctSelectProposal.occurrenceOnlyTwoWordDescriptorRouting_impossible`,
`occurrencePairTwoWordDescriptorRouting_not_global`, and
`coarseBaseTwoWordDescriptorRouting_not_global` further rule out the tempting
bit-blind occurrence-pair and coarse-base routes for consuming the two-word
descriptor kernel globally; the remaining positive select path needs a
bitvector-dependent charged routing/predecessor layer rather than another local
descriptor fact.

- The RMQ contract is half-open: a valid query satisfies `left < right` and
  `right <= xs.length`; invalid or empty ranges return `none`.
- Ties are resolved by the leftmost index. This is part of the semantic
  contract, not an implementation accident.
- Value-level structures use Lean `List Int` and `Nat` indices. The proof
  objects certify functional behavior over lists.
- Cost theorems are model-level `Costed` counts. They do not claim that Lean's
  executable `List` representation has random-access runtime behavior.
- `Core.TableModel` centralizes the vocabulary for model-level indexed reads
  and payload-bit accounting. It provides reference adapters for list-backed
  data but does not itself claim that Lean lists are constant-time arrays.
- `Core.RAM` is separate from `Core.TableModel`: its cost is the length of a
  primitive-operation trace, and `Impl.SparseTableInstrumented` is the first
  bridge from that derived-cost substrate back to a verified List backend.
  `RAM.Exec` and the raw one-step primitive are sealed behind typed primitives,
  but `Exec.pure` still means this is a disciplined shallow model rather than
  an interpreter-level anti-vacuity guarantee. `RAM.arrayOfList` is the generic
  counted List-to-Array materializer now reused by LCA stored node/depth views.
- `Impl.LCACost` uses `Core.TableModel` to model first-occurrence, node-list,
  and depth-list indexed accesses. The earlier association-list
  first-occurrence path was retired because lookup is linear. The direct-address
  first-occurrence table is proved equal to the generated trace lookup under
  `LabelsBoundedBySize` and supports the dense query-side capstone. Its RAM
  builder initializes an Array of empty slots and scans Euler nodes with counted
  read/branch/write steps. Euler node/depth views now have counted Array
  builders via `RAM.arrayOfList`; `Impl.LCAFischerHeun` composes those pieces
  with the Fischer-Heun RMQ build in a dense component-budget theorem.
- `Impl.LCAFischerHeun` instantiates the indexed LCA query model with the
  canonical Fischer-Heun RMQ query over Euler depths. Its `<= 13` RMQ theorem is a
  supplied-query bound in the large canonical regime. The dense
  `densePreprocessAndQuery_refines_with_steps_of_denseNatLabels` theorem
  includes Euler-trace construction in the existing tick model, counted
  node/depth stored views, counted dense first-occurrence construction, and
  Fischer-Heun RMQ-state build. It is still a component-budget theorem rather
  than one monolithic RAM program.
- Supplied sparse-table and stored microtable lookups use the standard
  RAM/unit-cost indexed-access model. This is explicitly reflected by
  one-tick row/cell lookups and two modeled reads per live microtable candidate:
  one block-signature read and one shape/query-slot read.
- The canonical Fischer-Heun profile uses
  `canonicalBlockSize xs = Nat.log2 xs.length / 4` and currently assumes
  `16 <= canonicalBlockSize xs`. Under that large-input regime the microtable
  slot budget and summary sparse-table log-row budget are discharged.
- The value-level Fischer-Heun build/query path is exact for all inputs. The
  all-input wrapper chooses linear scan outside the canonical large-input
  regime and canonical Fischer-Heun inside it; both branches have costed
  erasure/run theorems. Same-block and final-boundary windows are handled by
  padded local microtable lookups, so positive-block supplied queries are now
  bounded by a constant.
- The lower-bound scaffold works at the Cartesian-shape encoding level and now
  includes the exact-RMQ-decoder bridge, the quadratic Catalan count, and the
  unconditional fixed-length exact-RMQ `2*n - O(log n)` bit lower bound.
- The concrete canonical representative state encoding uses the explicit
  preorder shape payload of length `2*n` and decodes it back to a shape before
  scanning the canonical representative array. It is intentionally a simple
  baseline instance of the lower-bound interface, not a compressed backend
  representation.
- `Impl.FischerHeun.stateEncoding` carries an ordinary built Fischer-Heun state
  as proof-only data and exposes only the explicit shape payload through
  `encodeState`. Its decoder uses the payload-only one-block raw microtable
  query, so it exercises the implementation-layer local-query machinery while
  preserving the payload/accounting split.
- The plus-minus-one RMQ package records the Euler-depth adjacent-step
  invariant at the input/API level. It now includes normalized delta-signature
  tables and a packed-payload query wrapper over a fixed exact signature table.
  This is a model-level universal-decoder interface, not yet a broadword
  plus-minus-one RMQ implementation.
- The succinct layer remains value-level for bit contents, but it now has a
  model-level packed rank/select wrapper and packed PM1 state wrapper. Packed
  rank/select queries and supplied packed PM1 table queries cost one tick under
  the RAM/unit-cost indexed-access model; actual broadword layouts, compressed
  table overhead, and hardware word-size assumptions are future refinements.
- The project remains Mathlib-free: imports are Lean/Std plus existing Lean
  arithmetic automation such as `omega`.

## Primary Definitions And Structures

- `RMQ/Core/Spec.lean`: `ValidRange`, `betterIndex`, `combineIndex`,
  `LeftmostArgMin`, `CandidateExact`.
- `RMQ/Core/Window.lean`: `windowTailIndices`, `scanWindow`.
- `RMQ/Core/Backend.lean`: `RMQBackend`, `RMQBackend.queryBuilt`.
- `RMQ/Core/ModelHub.lean`: import-only reusable hub barrel for `Cost`, `RAM`,
  `Refine`, `TableModel`, `LowerBound`, and `PayloadLowerBound`.
- `RMQ/Core/Cost.lean`: `Costed`, `Costed.erase`, `Costed.run`,
  `Costed.pure`, `Costed.bind`, `Costed.tick`, `Costed.tickValue`,
  `Costed.map`.
- `RMQ/Core/RAM.lean`: `RAM.Op`, `RAM.Exec`, `RAM.Exec.steps`,
  `RAM.Exec.pure`, `RAM.Exec.bind`,
  `RAM.Exec.toCosted`, `RAM.branch`, `RAM.readArray?`,
  `RAM.writeArray?`, `RAM.compareLtInt`, `RAM.allocArray`,
  `RAM.pushArray`, `RAM.rankBoolWordPrefix`, `RAM.selectBoolWord`,
  `RAM.pushListToArray`, `RAM.arrayOfList`.
- `RMQ/Core/Refine.lean`: `Refine.StoredSeq`, `Refine.StoredSeq.ofList`,
  `Refine.StoredSeq.erases_eq`, `Refine.StoredSeq.get?`,
  `Refine.StoredSeq.absGet?`, `Refine.StoredSeq.get?_eq_absGet?`,
  `Refine.StoredMatrix`,
  `Refine.StoredMatrix.ofList`, `Refine.StoredMatrix.erases_eq`,
  `Refine.StoredMatrix.row?`, `Refine.StoredMatrix.absRow?`,
  `Refine.StoredMatrix.cell?`, `Refine.StoredMatrix.absCell?`,
  `Refine.StoredMatrix.row?_getD_toList_eq_absRow?_getD`,
  `Refine.StoredMatrix.cell?_getD_eq_absCell?_getD`.
- `RMQ/Core/TableModel.lean`: `TableModel.indexedReadCost`,
  `TableModel.IndexedAccess`, `TableModel.IndexedAccess.getCosted`,
  `TableModel.IndexedSeq`, `TableModel.IndexedSeq.ofList`,
  `TableModel.IndexedSeq.getCosted`, `TableModel.StoredSeq`,
  `TableModel.StoredSeq.ofList`, `TableModel.StoredMatrix`,
  `TableModel.StoredMatrix.ofList`, `TableModel.PayloadView`,
  `TableModel.PayloadView.exact`,
  `TableModel.PayloadView.withUnchargedAux`.
- `RMQ/Core/LowerBound.lean`: `LowerBound.bitStrings`,
  `LowerBound.LosslessEncoding`,
  `LowerBound.domain_length_le_two_pow_of_lossless_encoding`,
  `LowerBound.lower_le_bits_of_count_lower_bound`,
  `LowerBound.count_log_lower_of_quadratic_bound`.
- `RMQ/Core/PayloadLowerBound.lean`:
  `LowerBound.PayloadLosslessEncoding`,
  `LowerBound.PayloadLosslessEncoding.toLosslessEncoding`,
  `LowerBound.PayloadSpaceBounds`,
  `LowerBound.domain_length_le_two_pow_of_payload_lossless_encoding`.
- `RMQ/Core/CostKernels.lean`: `scanWindowCosted`, `rangeScanCost`,
  `rangeScanCosted`, `queryOffsetCosted?`, `rawMicrotableLookupCosted`.
- `RMQ/Core/Schedule.lean`: `compressedLength`, `leftBoundaryBlock`,
  `rightBoundaryBlock`.
- `RMQ/Core/Recursion.lean`: `lengthRec`, `blockMinIndex`, `blockMinValue`,
  `blockMinSummary`, `liftBlockCandidate`, `recursiveMiddleCandidate`,
  `SummaryShape`, `recurseOnSummary`, `publicBlockSummaryShape`,
  `publicSummaryDepth`.
- `RMQ/Core/Shape.lean`: `CartesianShape`, `CartesianShape.size`,
  `CartesianShape.rootOffset?`, `shapeRange`, `shape`, `SameRMQBehavior`,
  `addConst`, `CartesianShape.representative`, `ShapeOfSize`,
  `shapesOfSize`, `shapeCount`, `CartesianShape.fullCode`,
  `CartesianShape.decodeFullCode?`, `blockSignature`.
- `RMQ/Core/EncodingLowerBound.lean`: `LosslessShapeEncoding`,
  `ExactRMQShapeEncoding`,
  `ExactRMQStateEncoding`,
  `ExactRMQSpaceBounds`, `logSlackLower`,
  `losslessShapeEncoding_of_exactRMQShapeEncoding`,
  `losslessShapeEncoding_of_exactRMQStateEncoding`,
  `canonicalShapePayload`, `fullCodeOfPayload`, `decodeShapePayload?`,
  `canonicalRepresentativeStateQuery`,
  `canonicalRepresentativeStateEncoding`,
  `canonicalRepresentativePayloadSpaceBounds`,
  `canonicalRepresentativeSpaceBounds`.
- `RMQ/Core/Microtable.lean`: `CartesianShape.queryOffset?`, `LocalValid`,
  `shapeUniverse`, `localScanOffset`, `Microtable`, `Microtable.raw`,
  `Microtable.queryIndex?`, `Microtable.backend`, `Microtable.rawBackend`.
- `RMQ/Core/LCA.lean`: `RoseTree`, `UnitDepthMove`, `UnitDepthMoves`,
  `depthsFromMoves`, `depthAfterMoves`, `AdjacentDepthsDifferByOne`,
  `RoseTree.eulerDepthsAt`, `RoseTree.eulerDepths`, `LabelsUnique`,
  `eulerPaths`, `pathDepth`, `commonPrefix`, path-level and tree-level
  `pathLCA?`, `PathCommonAncestor`, `IsPathLCAOfPaths`, `IsPathLCA`,
  `firstIndexOf?`, `EulerTrace`, `EulerPathTrace`, generated Euler traces,
  `firstOccurrence?`, `occurrenceWindow`, `leftmostMinNode?`,
  `minDepthNodeInWindow`, trace/tree `lcaCandidate`, `IsLCAAnswer`,
  `TracePathAgreement`, `EulerPathWindowAgreement`,
  `PathWindowPrefixInvariant`, `EulerPathWindowPrefixInvariant`,
  `PathWindowCommonPrefixWitness`, `EulerPathWindowCommonPrefixWitness`,
  `TracePathExactOnLabels`, `labelPairAgreement`,
  `duplicateLabelCounterexample`.
- `RMQ/Core/PlusMinusOne.lean`: `PlusMinusOne.IsDepthTrace`,
  `PlusMinusOne.stepValue`, `PlusMinusOne.blockDeltaSignature`,
  `PlusMinusOne.traceFromSignature`, `PlusMinusOne.SignatureTable`,
  `PlusMinusOne.Input`, `PlusMinusOne.inputOfSignature`,
  `PlusMinusOne.Input.ofEulerTrace`, `PlusMinusOne.Input.ofRoseTree`,
  `PlusMinusOne.Backend`,
  `PlusMinusOne.Backend.toRMQBackend`,
  `PlusMinusOne.Backend.queryBuilt`.
- `RMQ/Core/Succinct.lean`: `Succinct.rankPrefix`, `Succinct.select`,
  `Succinct.BalancedPrefixes`, `Succinct.Balanced`,
  `Succinct.BalancedParens`, `Succinct.depthsFromParens`,
  `Succinct.plusMinusOneInputOfParens`, `Succinct.RankSelectIndex`,
  `Succinct.PackedBitVector`, `Succinct.PackedBalancedParens`,
  `Succinct.PackedPlusMinusOneRMQ`,
  `Succinct.PackedPlusMinusOneRMQ.signatureUniverse`,
  `Succinct.PackedPlusMinusOneRMQ.localQuerySlotBudget`,
  `Succinct.PackedPlusMinusOneRMQ.localQuerySlotIndex`,
  `Succinct.PackedPlusMinusOneRMQ.fixedTableSlotBudget`,
  `Succinct.bitOfMove`, `Succinct.bitsFromMoves`,
  `Succinct.eulerParens`, `Succinct.balancedEulerParens`,
  `Succinct.plusMinusOneInputOfEulerParens`,
  `Succinct.packedEulerParens`, `Succinct.packedBalancedEulerParens`,
  `Succinct.packedEulerParensRMQ`, `Succinct.packedEulerParensBackend`.
- `RMQ/Core/SuccinctSpace.lean`: `SuccinctSpace.LittleOLinear`,
  `SuccinctSpace.bpCode_balanced`, `SuccinctSpace.bpParensOfShape`,
  `SuccinctSpace.bpCloseOfInorder?`,
  `SuccinctSpace.PayloadWordStore`,
  `SuccinctSpace.BoundedPayloadWordStore`,
  `SuccinctSpace.FixedWidthNatTable`,
  `SuccinctSpace.FixedWidthOptionNatTable`,
  `SuccinctSpace.FixedWidthRankSampleTables`,
  `SuccinctSpace.FixedWidthSelectSampleTables`,
  `SuccinctSpace.PayloadLiveStoredWordRankData`,
  `SuccinctSpace.PayloadLiveStoredWordSelectData`,
  `SuccinctSpace.PayloadLiveStoredWordRankSelectFamily`,
  `SuccinctSpace.RankSelectDirectory`, `SuccinctSpace.RankSelectFamily`,
  `SuccinctSpace.StoredWordRankData`,
  `SuccinctSpace.StoredWordSelectData`,
  `SuccinctSpace.PayloadBackedStoredWordRankSelectData`,
  `SuccinctSpace.PayloadBackedStoredWordRankSelectFamily`,
  `SuccinctSpace.ValidRankDirectory`,
  `SuccinctSpace.ValidRankBalancedParensAccess`,
  `SuccinctSpace.StoredRankBalancedParensAccess`,
  `SuccinctSpace.StoredRankBalancedParensAccessFamily`,
  `SuccinctSpace.BalancedParensAccess`,
  `SuccinctSpace.BalancedParensAccessFamily`,
  `SuccinctSpace.BroadwordRMQDirectory`,
  `SuccinctSpace.BroadwordSuccinctRMQFamily`,
  `SuccinctSpace.BPBroadwordRMQDirectory`,
  `SuccinctSpace.StoredBPCloseLCADirectory`,
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory`,
  `SuccinctSpace.StoredBPCloseLCAFamily`,
  `SuccinctSpace.BPCloseRMQNavigationDirectory`,
  `SuccinctSpace.BPCloseRMQNavigationFamily`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationDirectory`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.SampledPayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.EncodedPayloadLiveBPCloseRMQNavigationView`,
  `SuccinctSpace.EncodedPayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.SampledEncodedPayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily`,
  `SuccinctSpace.BPBroadwordSuccinctRMQFamily`,
  `SuccinctSpace.bpAuxOverhead`,
  `SuccinctSpace.ComponentizedBPRMQFamily`,
  `SuccinctSpace.bpCloseNavigationOverhead`.
- `RMQ/Core/SuccinctReduction.lean`:
  `Succinct.rmqBackendOfEulerParensBackend`,
  `Succinct.lcaBackendOfEulerParensBackend`,
  `Succinct.lcaBackendOfEulerParensBackendUnique`,
  `Succinct.lcaCandidateOfEulerParensBackend`,
  `Succinct.packedEulerParensLCABackend`,
  `Succinct.packedEulerParensLCABackendUnique`,
  `Succinct.packedEulerParensLCACandidate`.
- `RMQ/Core/Reduction.lean`: `LCABackend`, `LCABackend.queryBuilt`,
  `RoseTree.lcaBackendOfRMQBackend`, `RoseTree.lcaBackendOfRMQBackendUnique`,
  `RoseTree.lcaBackendOfRMQBackendChecked`, `RMQToLCAReduction`,
  `RMQToLCAReduction.queryWithLCABackend`,
  `RMQToLCAReduction.rmqBackendOfLCABackend`,
  `rmq_lca_reduction_equiv`, `rmq_lca_reduction_equiv_checked`.
- `RMQ/Core/Cartesian.lean`: `childIf`, `treeRange`, `tree`, `rootLabel`,
  `InRange`, `indexPath`, `RangeLCASpec`, `reductionOfRangeLCASpec`,
  `BuiltRangeLCASpec`, `reduction`, `certifiedReduction`.
- `RMQ/Impl/LinearScan.lean`: `query`, `backend`.
- `RMQ/Impl/PlusMinusOne.lean`: `linearScanBackend`, `query`,
  `signatureBackend`, `signatureQuery`, `linearScanBackendOfEulerTrace`,
  `linearScanBackendOfRoseTree`.
- `RMQ/Impl/SparseTable.lean`: `blockLen`, `combineIndex`, `blockArgMin`,
  `sparseRow`, `rowCell`, `buildSparseTable`, `tableRow`, `queryFromTable`,
  `query`, `backend`.
- `RMQ/Impl/SparseTableInstrumented.lean`:
  `SparseTable.Instrumented.ArrayValidRange`,
  `SparseTable.Instrumented.blockArgMinArraySteps`,
  `SparseTable.Instrumented.rowArray`,
  `SparseTable.Instrumented.tableArray`,
  `SparseTable.Instrumented.tableRowArray`,
  `SparseTable.Instrumented.rowCellArray`,
  `SparseTable.Instrumented.betterIndexArray`,
  `SparseTable.Instrumented.combineIndexArray`,
  `SparseTable.Instrumented.memoNextCellArray`,
  `SparseTable.Instrumented.memoNextRowArrayValuesFrom`,
  `SparseTable.Instrumented.memoNextRowArray`,
  `SparseTable.Instrumented.blockArgMinArray`,
  `SparseTable.Instrumented.rowArrayValuesFrom`,
  `SparseTable.Instrumented.sparseRowArrayBuild`,
  `SparseTable.Instrumented.memoBuildRowsFromArray`,
  `SparseTable.Instrumented.memoBuildRowsFromArraySteps`,
  `SparseTable.Instrumented.memoBuildSparseTableArraySteps`,
  `SparseTable.Instrumented.memoBuildSparseTableArray`,
  `SparseTable.Instrumented.queryFromArrayTable`,
  `SparseTable.Instrumented.query`,
  `SparseTable.Instrumented.memoQueryWithTracedBuild`.
- `RMQ/Impl/SparseTableMemoCost.lean`: `memoNextRow`, `memoNextCellCost`,
  `memoNextRowCost`, `memoNextRowCosted`, `memoRowCount`,
  `memoBaseRowCost`, `memoBaseRowCosted`, `memoBuildSparseTableCost`,
  `memoBuildRowsFrom`, `memoBuildRowsFromCost`, `memoBuildRowsFromCosted`,
  `memoBuildSparseTable`, `memoBuildSparseTableCosted`, `memoQuery`,
  `memoBackend`.
- `RMQ/Impl/HybridBlock.lean`: `chunkSpan`, `publicBlockSize`,
  `combineIndex`, `rangeScan`, `chunkCell`, `chunkRow`, `rowCell`,
  `buildChunkSparseTable`, `tableRow`, `sparseChunkQueryFromTable`,
  `State`, `build`, `queryWithState`, `query`, `backend`.
- `RMQ/Impl/RecursiveHybrid.lean`: `combineIndex`, `rangeScan`,
  `queryWithSummaryBackend`, `backendWithSummary`, `backend`, `query`.
- `RMQ/Impl/RecursiveHybridCost.lean`: `blockSummaryEntryCost`,
  `blockMinSummaryBuildCost`, `blockMinSummaryCosted`, `buildCost`,
  `queryWithSummaryCost`, `queryWithSummaryCosted`.
- `RMQ/Impl/LCACost.lean`: `eulerTraceBuildCost`, `eulerTraceCosted`,
  `firstOccurrenceIndex`, `firstOccurrenceCosted`,
  `firstOccurrenceDirectRows`,
  `firstOccurrenceDirectSlots`, `firstOccurrenceDirectStore`,
  `firstOccurrenceDirectIndex`, `firstOccurrenceDirectCosted`, `nodeIndex`,
  `depthIndex`, `nodeAtCosted`, `depthAtCosted`, `suppliedQueryCost`,
  `queryCosted`, `queryViaRMQCosted`, `suppliedRMQQueryCost`,
  `rmqQueryCosted`,
  `minDepthNodeInWindowIndexedCosted`, `traceQueryViaRMQIndexedCosted`,
  `queryViaRMQIndexedCosted`, `queryViaEulerParensRMQIndexedCosted`,
  `queryViaEulerParensRMQIndexedCost`,
  `queryViaPackedEulerParensRMQIndexedCosted`,
  `queryViaPackedEulerParensRMQIndexedCost`.
- `RMQ/Impl/LCAFischerHeun.lean`: `LCAFischerHeun.canonicalRMQBackend`,
  `LCAFischerHeun.allInputRMQBackend`,
  `LCAFischerHeun.canonicalBackend`,
  `LCAFischerHeun.canonicalBackendUnique`,
  `LCAFischerHeun.allInputBackend`,
  `LCAFischerHeun.allInputBackendUnique`,
  `LCAFischerHeun.canonicalCandidate`,
  `LCAFischerHeun.allInputCandidate`,
  `LCAFischerHeun.canonicalMinDepthNodeCosted`,
  `LCAFischerHeun.canonicalConcreteQueryCosted`,
  `LCAFischerHeun.ConcreteQueryState`,
  `LCAFischerHeun.buildDenseConcreteQueryState`,
  `LCAFischerHeun.stateFirstOccurrenceCosted`,
  `LCAFischerHeun.stateNodeAtCosted`,
  `LCAFischerHeun.stateMinDepthNodeCosted`,
  `LCAFischerHeun.queryWithConcreteStateCosted`,
  `LCAFischerHeun.densePreprocessBuildCost`,
  `LCAFischerHeun.densePreprocessBuildBudget`,
  `LCAFischerHeun.densePreprocessLinearBudget`,
  `LCAFischerHeun.canonicalQueryCosted`,
  `LCAFischerHeun.canonicalQueryCost`,
  `LCAFischerHeun.allInputQueryCosted`,
  `LCAFischerHeun.allInputQueryCost`.
- `RMQ/Impl/FischerHeunCost.lean`: `rawLookupCostBound`,
  `rawShapeTableCount`, `localQuerySlotBudget`, `rawMicrotableSlotBudget`,
  `shapeCountEnvelope`, `canonicalBlockSize`, `summarySparseBuildCost`,
  `storedMicrotableLookupCost`, `suppliedQueryCost`, `buildCost`.
- `RMQ/Impl/FischerHeun.lean`: `MicrotableFor`, `State`,
  `paddedInput`, `storedBlockSignatures`, `MicrotableSlotKey`,
  `StoredMicrotableView`, `storedExactBlockSignatures`,
  `microtableSlotAccess`, `microtableSlotReadCosted`,
  `storedMicrotableForInputWith`, `storedMicrotableForInput`,
  `storedMicrotableForExactInputWith`, `storedLocalBlockCandidateCost`,
  `storedLocalBlockCandidateCosted`, `localBlockCandidate`,
  `storedFullBlockCandidateCosted`,
  `storedStateLocalBlockCandidateCosted`,
  `rightBoundaryCandidate`,
  `summaryBackend`, `buildWithBlockSize`, `build`,
  `tickEachCosted`, `microtableSlotTokens`,
  `microtableShapeRowBuildCosted`, `microtableRowsBuildCostedFrom`,
  `microtableRowsBuildCosted`, `microtableBuildCosted`,
  `buildWithBlockSizeCosted`, `buildCosted`,
  `queryWithState`, `localBlockCandidateCost`,
  `rightBoundaryCandidateCost`,
  `rightBoundaryCandidateCosted`, `queryWithStateCost`,
  `queryWithStateCosted`, `queryWithBlockSize`, `queryWithBlockSizeCosted`,
  `query`, `queryCosted`, `queryWithBlockSizeFreshCosted`,
  `freshQueryCosted`, `backendWithBlockSize`, `backend`, `canonicalReady`,
  `allInputQuery`, `allInputQueryCost`, `allInputQueryCosted`,
  `EncodedState`, `encodedStateOfShape`, `encodedStateQuery`,
  `stateEncoding`,
  `allInputBackend`.

## Public Theorem Inventory

The names below are grouped by source module. Repeated base names in
`Core/LCA.lean` live in different namespaces, for example `EulerTrace` and
`RoseTree`.

### Core

- `RMQ/Core/Spec.lean` (9): `LeftmostArgMin.valid`,
  `leftmostArgMin_unique`, `combineLeftmost`, `candidateExact_none`,
  `candidateExact_some`, `CandidateExact.exists_of_nonempty`,
  `candidateExact_combineAdjacent`, `candidateExact_combineThree`,
  `combineHybridLeftmost`.
- `RMQ/Core/Window.lean` (3): `singleton_leftmostArgMin`,
  `extend_leftmostArgMin`, `scanWindow_leftmost`.
- `RMQ/Core/Backend.lean` (1): `RMQBackend.queryBuilt_eq`.
- `RMQ/Core/Cost.lean` (28): `Costed.erase_mk`, `Costed.run_mk`,
  `Costed.value_pure`, `Costed.cost_pure`, `Costed.erase_pure`,
  `Costed.run_pure`, `Costed.value_bind`, `Costed.cost_bind`,
  `Costed.erase_bind`, `Costed.run_bind`, `Costed.value_tick`,
  `Costed.cost_tick`, `Costed.erase_tick`, `Costed.run_tick`,
  `Costed.value_tickValue`, `Costed.cost_tickValue`,
  `Costed.erase_tickValue`, `Costed.run_tickValue`, `Costed.pure_bind`,
  `Costed.bind_pure`, `Costed.bind_assoc`, `Costed.cost_bind_assoc`,
  `Costed.tick_bind_cost`, `Costed.bind_tick_cost`,
  `Costed.tickValue_eq_tick_bind_pure`, `Costed.map_value`,
  `Costed.map_cost`, `Costed.erase_map`.
- `RMQ/Core/RAM.lean`: `RAM.Exec.steps_pure`,
  `RAM.Exec.value_pure`, `RAM.Exec.value_bind`,
  `RAM.Exec.steps_bind`, `RAM.Exec.toCosted_value`,
  `RAM.Exec.toCosted_cost_eq_steps`,
  `RAM.Exec.toCosted_run_eq_value_steps`, `RAM.branch_value`,
  `RAM.branch_steps`, `RAM.readArray?_value`, `RAM.readArray?_steps`,
  `RAM.writeArray?_value`, `RAM.writeArray?_steps`,
  `RAM.compareLtInt_value`, `RAM.compareLtInt_steps`,
  `RAM.allocArray_value`, `RAM.allocArray_steps`,
  `RAM.pushArray_value`, `RAM.pushArray_steps`,
  `RAM.rankBoolWordPrefix_value`, `RAM.rankBoolWordPrefix_steps`,
  `RAM.selectBoolWord_value`, `RAM.selectBoolWord_steps`,
  `RAM.branch_run`,
  `RAM.readArray?_run`, `RAM.writeArray?_run`, `RAM.compareLtInt_run`,
  `RAM.allocArray_run`, `RAM.pushArray_run`,
  `RAM.rankBoolWordPrefix_run`, `RAM.selectBoolWord_run`,
  `RAM.pushListToArray_value_toList`, `RAM.pushListToArray_steps`,
  `RAM.arrayOfList_value_toList`, `RAM.arrayOfList_steps`,
  `RAM.arrayOfList_refines_with_steps`, `RAM.arrayOfList_run`.
- `RMQ/Core/TableModel.lean` (23):
  `TableModel.IndexedAccess.getCosted_value`,
  `TableModel.IndexedAccess.getCosted_erase`,
  `TableModel.IndexedAccess.getCosted_cost`,
  `TableModel.IndexedAccess.getCosted_run`,
  `TableModel.IndexedSeq.ofList_length`,
  `TableModel.IndexedSeq.ofList_get?`,
  `TableModel.IndexedSeq.getCosted_value`,
  `TableModel.IndexedSeq.getCosted_erase`,
  `TableModel.IndexedSeq.getCosted_cost`,
  `TableModel.IndexedSeq.getCosted_run`,
  `TableModel.IndexedSeq.ofList_getCosted_run`,
  `TableModel.StoredSeq.ofList_repr`,
  `TableModel.StoredSeq.ofList_erases`,
  `TableModel.StoredSeq.erases_eq`,
  `TableModel.StoredSeq.get?_eq_absGet?`,
  `TableModel.StoredMatrix.ofList_repr`,
  `TableModel.StoredMatrix.ofList_erases`,
  `TableModel.StoredMatrix.erases_eq`,
  `TableModel.StoredMatrix.ofList_heq_of_eq`,
  `TableModel.PayloadView.exact_payloadBitCount`,
  `TableModel.PayloadView.payloadBits_length_le`,
  `TableModel.PayloadView.withUnchargedAux_payloadBits`,
  `TableModel.PayloadView.withUnchargedAux_payloadBitCount`.
- `RMQ/Core/CostKernels.lean` (15): `scanWindowCosted_value`,
  `scanWindowCosted_erase`, `scanWindowCosted_cost`,
  `scanWindowCosted_run`, `scanWindowCosted_leftmost`,
  `rangeScanCosted_value`, `rangeScanCosted_erase`,
  `rangeScanCosted_cost`, `rangeScanCosted_run`,
  `CartesianShape.queryOffsetCosted?_value`,
  `CartesianShape.queryOffsetCosted?_erase`,
  `CartesianShape.queryOffsetCosted?_cost_le_size_succ`,
  `Cartesian.rawMicrotableLookupCosted_value`,
  `Cartesian.rawMicrotableLookupCosted_erase`,
  `Cartesian.rawMicrotableLookupCosted_cost_le`.
- `RMQ/Core/Schedule.lean` (4): `compressedLength_lt_self`,
  `left_lt_leftBoundaryBlock_mul`, `rightBoundaryBlock_mul_le`,
  `rightBoundaryBlock_le_compressed`.
- `RMQ/Core/Recursion.lean` (14): `block_bound_of_lt_compressedLength`,
  `block_start_lt_of_lt_compressedLength`, `blockMinSummary_length`,
  `blockMinSummary_get?_eq_blockMinValue`, `blockMinIndex_leftmost`,
  `blockMinSummary_entry_exact`, `blockMinSummary_lift_leftmost`,
  `blockMinSummary_lift_candidate`, `recursiveMiddleCandidate_exact`,
  `combineRecursiveMiddleLeftmost`, `publicBlockSize_gt_one_of_length_gt_one`,
  `publicCompressedLength_lt_self`, `recurseOnSummary_of_small`,
  `recurseOnSummary_of_large`.
- `RMQ/Core/Shape.lean` (42): `shapeRange_size`, `shape_size`,
  `rootOffset?_shapeRange`, `addConst_length`, `betterIndex_addConst`,
  `scanWindow_addConst`, `sameRMQBehavior_addConst`,
  `leftmostArgMin_congr_on_range`, `scanWindow_congr_on_range`,
  `shapeRange_congr_on_range`, `scanWindow_append_left`,
  `shapeRange_append_left`, `leftmostArgMin_append_right`,
  `scanWindow_append_right`, `shapeRange_append_right`,
  `shapeRange_eq_of_sameRMQBehavior`, `shape_eq_of_sameRMQBehavior`,
  `shapeRange_addConst`, `shape_addConst`,
  `CartesianShape.representative_length`,
  `CartesianShape.representative_nonnegative`,
  `CartesianShape.representative_shift_positive`,
  `CartesianShape.shape_representative`,
  `scanWindow_eq_of_shapeRange_eq`,
  `sameRMQBehavior_of_shapeRange_eq`, `sameRMQBehavior_iff_shapeRange_eq`,
  `ShapeOfSize.size_eq`, `ShapeOfSize.exists_representative_array`,
  `shapeCount_zero`, `shapeCount_succ`,
  `mem_shapesOfSize_shapeOfSize`, `shapeOfSize_mem_shapesOfSize`,
  `mem_shapesOfSize_iff_shapeOfSize`, `CartesianShape.fullCode_length`,
  `CartesianShape.fullCode_injective`,
  `CartesianShape.decodeFullCode?_fullCode`, `shapesOfSize_nodup`,
  `CartesianShape.fullCode_tail_length_of_shapeOfSize`,
  `shapeCount_le_four_pow`, `shapeRange_shapeOfSize`, `shape_shapeOfSize`,
  `blockSignature_shapeOfSize`.
- `RMQ/Core/LowerBound.lean` (8): `bitStrings_length`,
  `mem_bitStrings_of_length`, `length_le_of_nodup_injective_into`,
  `domain_length_le_two_pow_of_lossless_encoding`,
  `lower_le_bits_of_count_lower_bound`,
  `odd_square_le_two_pow_log_slack`,
  `two_pow_sub_le_of_le_mul_pow`,
  `count_log_lower_of_quadratic_bound`.
- `RMQ/Core/PayloadLowerBound.lean` (20):
  `LowerBound.PayloadLosslessEncoding.ofLosslessEncoding_payloadBits`,
  `LowerBound.PayloadLosslessEncoding.ofLosslessEncoding_payloadBitCount`,
  `LowerBound.PayloadLosslessEncoding.ofLosslessEncoding_toLosslessEncoding_encode`,
  `LowerBound.PayloadLosslessEncoding.withUnchargedAux_payloadBits`,
  `LowerBound.PayloadLosslessEncoding.withUnchargedAux_payloadBitCount`,
  `LowerBound.PayloadLosslessEncoding.toLosslessEncoding_encode`,
  `LowerBound.PayloadLosslessEncoding.domain_length_le_two_pow`,
  `LowerBound.PayloadLosslessEncoding.lower_le_bits_of_count_lower_bound`,
  `LowerBound.PayloadLosslessEncoding.payloadBitCount_ge_bits_of_mem`,
  `LowerBound.PayloadLosslessEncoding.bits_le_of_payloadBitCount_le_of_mem`,
  `LowerBound.PayloadLosslessEncoding.lower_le_payloadBitCount_of_mem_of_count_lower_bound`,
  `LowerBound.PayloadLosslessEncoding.lower_le_budget_of_payloadBitCount_bound`,
  `LowerBound.PayloadLosslessEncoding.exact_payloadBitCount_eq_bits_of_mem`,
  `LowerBound.domain_length_le_two_pow_of_payload_lossless_encoding`,
  `LowerBound.lower_le_budget_of_payload_lossless_encoding`,
  `LowerBound.PayloadSpaceBounds.lower_le_bits`,
  `LowerBound.PayloadSpaceBounds.lower_le_payloadBitCount_of_mem`,
  `LowerBound.PayloadSpaceBounds.lower_le_budget`,
  `LowerBound.PayloadSpaceBounds.upper_domain_length_le_two_pow`,
  `LowerBound.PayloadSpaceBounds.lower_le_upper`.
- `RMQ/Core/EncodingLowerBound.lean` (40): `bitStrings_length`,
  `mem_bitStrings_of_length`, `length_le_of_nodup_injective_into`,
  `fullCodeOfPayload_canonicalShapePayload`,
  `decodeShapePayload?_canonicalShapePayload`,
  `sameRMQBehavior_of_exactRMQShapeEncoding_eq`,
  `ExactRMQStateEncoding.payloadOf_length_eq`,
  `ExactRMQStateEncoding.sameRMQBehavior_of_payload_eq`,
  `ExactRMQStateEncoding.shape_eq_of_payload_eq`,
  `ExactRMQStateEncoding.payloadLosslessEncoding_toLosslessEncoding_encode`,
  `ExactRMQStateEncoding.payloadBitCount_ge_bits_of_mem`,
  `ExactRMQStateEncoding.payloadBitCount_eq_bits_of_mem`,
  `ExactRMQStateEncoding.payloadOf_withUnchargedAux`,
  `shapeCount_le_two_pow_of_lossless_shape_encoding`,
  `shapeCount_le_two_pow_of_exactRMQShapeEncoding`,
  `lower_le_bits_of_shapeCount_lower_bound`,
  `lower_le_bits_of_exactRMQShapeEncoding`,
  `shapeCount_pos`, `odd_square_le_two_pow_log_slack`,
  `shapeCount_quadratic_lower`, `shapeCount_log_lower_of_quadratic_bound`,
  `two_mul_sub_slack_le_bits_of_exactRMQShapeEncoding`,
  `two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding_of_quadratic_bound`,
  `two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding`,
  `shapeCount_le_two_pow_of_exactRMQStateEncoding`,
  `shapeCount_le_two_pow_of_exactRMQStateEncoding_payloadView`,
  `two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding`,
  `two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding_payloadView`,
  `two_mul_sub_log_slack_le_payloadBits_of_exactRMQStateEncoding`,
  `two_mul_sub_log_slack_le_bits_of_canonicalRepresentativeStateEncoding`,
  `logSlackLower_le_payloadBitCount_of_exactRMQStateEncoding`,
  `logSlackLower_le_budget_of_exactRMQStateEncoding`,
  `canonicalRepresentative_payloadBitCount_eq_two_mul`,
  `canonicalRepresentativePayloadSpaceBounds_lower_le_bits`,
  `canonicalRepresentativePayloadSpaceBounds_lower_le_budget`,
  `canonicalRepresentativePayloadSpaceBounds_lower_le_upper`,
  `canonicalRepresentativeSpaceBounds_lower_le_any`,
  `canonicalRepresentativeSpaceBounds_upper_bits`,
  `exactRMQ_two_sided_log_slack_space_bound`,
  `exactRMQ_tight_fixed_length_payload_space_bound`.
- `RMQ/Core/Microtable.lean` (11): `shapeUniverse_length`,
  `blockSignature_mem_shapeUniverse`, `localScanOffset_bounds`,
  `localScanOffset_add_start`, `localScanOffset_leftmost`,
  `CartesianShape.queryOffset?_blockSignature`, `Microtable.queryIndex?_eq`,
  `Microtable.queryIndex?_leftmost`, `Microtable.queryIndex?_sound`,
  `Microtable.queryIndex?_complete`, `Microtable.queryIndex?_invalid`.
- `RMQ/Core/LCA.lean` (92): `unitDepthMoves_append`,
  `depthAfterMoves_append`, `depthsFromMoves_append_cons`,
  `unitDepthMove_step`, `depthsFromMoves_adjacent`,
  `depthsFromMoves_length`, `RoseTree.eulerDepthsAt_adjacent`,
  `RoseTree.eulerDepths_adjacent`,
  `RoseTree.labelsPreorder_length_le_eulerNodes_length`,
  `RoseTree.labelsPreorderForest_length_le_eulerNodesForest_length`,
  `nodup_append_not_mem_right`,
  `nodup_append_not_mem_left`, `labelsUnique_root_not_mem_children`,
  `labelsUnique_children_nodup`, `labelsUnique_child_of_cons`,
  `labelsUnique_root_rest_of_cons`, `labelsUnique_child_not_mem_rest`,
  `labelsUnique_rest_not_mem_child`, `getLast?_append_singleton`,
  `eulerPaths_length_eq_eulerNodes`,
  `eulerDepths_eq_eulerPaths_map_pathDepth`,
  `eulerPaths_last?_eq_eulerNodes`, `pathTo?_mem_eulerPaths`,
  `getElem?_length_of_append_singleton_prefix`,
  `here_prefix_of_mem_eulerPathsAt_node`,
  `first_extra_of_mem_eulerPathsAt_node`,
  `first_extra_mem_labelsPreorderForest_of_mem_eulerPathsForestAt`,
  `commonPrefix_prefix_left`, `commonPrefix_prefix_right`,
  `commonPrefix_eq_left_of_prefix`, `commonPrefix_eq_right_of_prefix`,
  `commonPrefix_append_common`, `commonPrefix_comm`,
  `prefix_eq_of_prefix_of_length_le`, `prefix_commonPrefix_of_prefixes`,
  `getElem?_of_prefix`, `eq_commonPrefix_of_prefixes_of_length_ge`,
  `commonPrefix_eq_parentPath_of_child_and_rightForest`,
  `pathLCA?_isPathLCAOfPaths`, `RoseTree.pathLCA?_isPathLCA`,
  `RoseTree.pathLCA?_eq_of_isPathLCA`, `labels_mem_of_pathLCA?_some`,
  `isPathLCA_of_pathTo_prefixes_of_commonPrefix_length_le`,
  `pathTo?_eq_of_mem_eulerPaths_unique`, `firstIndexOf?_lt_length`,
  `firstIndexOf?_getElem?`, `firstIndexOf?_mem`,
  `firstIndexOf?_exists_of_mem`, `pathAt?_of_nodeAt?`,
  `EulerTrace.occurrenceWindow_fst_le_left`,
  `EulerTrace.occurrenceWindow_fst_le_right`,
  `EulerTrace.occurrenceWindow_left_lt_snd`,
  `EulerTrace.occurrenceWindow_right_lt_snd`,
  `EulerTrace.occurrenceWindow_shift_fst`,
  `EulerTrace.occurrenceWindow_shift_snd`,
  `EulerTrace.occurrenceWindow_valid`,
  `EulerTrace.minDepthNodeInWindow_valid_exact`,
  `EulerTrace.leftmostMinNode?_eq_of_isLCAAnswer`,
  `EulerTrace.isLCAAnswer_of_leftmostMinNode?_eq`,
  `EulerTrace.lcaCandidate_valid_exact`, `EulerTrace.lcaCandidate_isLCAAnswer`,
  `RoseTree.lcaCandidate_valid_exact`, `RoseTree.lcaCandidate_isLCAAnswer`,
  `eulerPathAt?_of_eulerTraceNodeAt?`, `pathWitness_of_isLCAAnswer`,
  `pathWitness_pathTo_of_isLCAAnswer_unique`,
  `pathAtFirstOccurrence?_pathTo_unique`,
  `pathWitness_with_endpoints_of_isLCAAnswer_unique`,
  `firstOccurrence?_exists_of_mem_labelsPreorder`,
  `leftmostMinNode?_exists_of_mem_labelsPreorder`,
  `pathWindowPrefixInvariant_cons`, `pathWindowCommonPrefixWitness_cons`,
  `pathWindowPrefixInvariant_append`, `pathWindowCommonPrefixWitness_append`,
  `eulerPathWindowAgreement_of_prefix_and_witness`,
  `tracePathAgreement_of_eulerPathWindowAgreement`,
  `tracePathAgreement_of_eulerPathWindowInvariants`,
  `eulerPathWindowPrefixInvariant_of_labelsUnique`,
  `eulerPathWindowCommonPrefixWitness_of_labelsUnique`,
  `eulerPathWindowAgreement_of_labelsUnique`,
  `tracePathAgreement_of_labelsUnique`,
  `tracePathExactOnLabels_of_tracePathAgreement`,
  `tracePathAgreement_of_leftmostMinNode_eq_pathLCA`,
  `tracePathAgreement_of_tracePathExactOnLabels`,
  `tracePathExactOnLabels_of_labelPairAgreement`,
  `tracePathAgreement_of_labelPairAgreement`,
  `lcaCandidate_isPathLCA_of_tracePathAgreement`,
  `lcaCandidate_isPathLCA_of_tracePathExactOnLabels`,
  `lcaCandidate_isPathLCA_of_labelPairAgreement`,
  `lcaCandidate_isPathLCA_of_pathLCA`,
  `duplicateLabelCounterexample_traceAnswer`,
  `duplicateLabelCounterexample_not_tracePathAgreement`.
- `RMQ/Core/PlusMinusOne.lean` (21):
  `PlusMinusOne.traceFromSignatureAt_length`,
  `PlusMinusOne.traceFromSignature_length`,
  `PlusMinusOne.traceFromSignatureAt_adjacent`,
  `PlusMinusOne.traceFromSignature_adjacent`,
  `PlusMinusOne.blockDeltaSignature_length`,
  `PlusMinusOne.SignatureTable.queryIndex?_eq`,
  `PlusMinusOne.SignatureTable.queryIndex?_leftmost`,
  `PlusMinusOne.SignatureTable.queryIndex?_sound`,
  `PlusMinusOne.SignatureTable.queryIndex?_complete`,
  `PlusMinusOne.SignatureTable.queryIndex?_invalid`,
  `PlusMinusOne.inputOfSignature_depths`,
  `PlusMinusOne.Input.ofEulerTrace_depths`,
  `PlusMinusOne.Input.ofEulerTrace_adjacent`,
  `PlusMinusOne.Input.ofRoseTree_depths`,
  `PlusMinusOne.Input.ofRoseTree_depths_eq_eulerDepths`,
  `PlusMinusOne.Input.ofRoseTree_adjacent`,
  `PlusMinusOne.Input.roseTree_eulerDepths_are_trace`,
  `PlusMinusOne.Backend.queryBuilt_sound`,
  `PlusMinusOne.Backend.queryBuilt_complete`,
  `PlusMinusOne.Backend.queryBuilt_invalid_none`,
  `PlusMinusOne.Backend.queryBuilt_eq`.
- `RMQ/Core/Succinct.lean`: `Succinct.rankPrefix_zero`,
  `Succinct.rankPrefix_nil`, `Succinct.rankPrefix_le_limit`,
  `Succinct.ram_boolRankPrefix_eq_rankPrefix`,
  `Succinct.rankBoolWordPrefix_toCosted_run`,
  `Succinct.rankPrefix_le_length`, `Succinct.rankPrefix_append_of_le`,
  `Succinct.rankPrefix_append_of_ge`, `Succinct.selectFrom_bounds`,
  `Succinct.select_bounds`, `Succinct.selectFrom_base_eq`,
  `Succinct.selectFrom_append_left_of_some`,
  `Succinct.selectFrom_append_right_after_count`,
  `Succinct.balanced_nil`,
  `Succinct.balanced_wrap_append`,
  `Succinct.BalancedParens.close_rank_le_open_rank`,
  `Succinct.BalancedParens.final_rank_eq`,
  `Succinct.depthsFromParens_adjacent`,
  `Succinct.depthsFromParens_length`,
  `Succinct.plusMinusOneInputOfParens_depths`,
  `Succinct.RankSelectIndex.rank_le_limit`,
  `Succinct.RankSelectIndex.select_bounds`,
  `Succinct.PackedBitVector.payloadCapacityBits_le_length_plus_wordSlack`,
  `Succinct.PackedBitVector.raw_payloadCapacityBits`,
  `Succinct.PackedBitVector.bitAccess_length`,
  `Succinct.PackedBitVector.bitAccess_get?`,
  `Succinct.PackedBitVector.bitAccess_getCosted_run`,
  `Succinct.PackedBitVector.rank_exact`,
  `Succinct.PackedBitVector.select_exact`,
  `Succinct.PackedPlusMinusOneRMQ.signatureUniverse_length`,
  `Succinct.PackedPlusMinusOneRMQ.mem_signatureUniverse_of_length`,
  `Succinct.PackedPlusMinusOneRMQ.signature_mem_own_universe`,
  `Succinct.PackedPlusMinusOneRMQ.localQuerySlotIndex_lt`,
  `Succinct.PackedPlusMinusOneRMQ.fixedTableSlotBudget_eq`,
  `Succinct.PackedPlusMinusOneRMQ.payloadView_bits`,
  `Succinct.PackedPlusMinusOneRMQ.payloadView_count`,
  `Succinct.PackedPlusMinusOneRMQ.payloadCapacityBits_le_signature_length_plus_wordSlack`,
  `Succinct.PackedPlusMinusOneRMQ.raw_payloadCapacityBits`,
  `Succinct.PackedPlusMinusOneRMQ.queryBuilt_eq_table`,
  `Succinct.PackedPlusMinusOneRMQ.queryBuilt_sound`,
  `Succinct.PackedPlusMinusOneRMQ.queryBuilt_complete`,
  `Succinct.PackedPlusMinusOneRMQ.queryBuilt_invalid_none`,
  `Succinct.stepValue_bitOfMove`, `Succinct.bitsFromMoves_length`,
  `Succinct.traceFromSignatureAt_bitsFromMoves`,
  `Succinct.eulerParens_length`,
  `Succinct.eulerParens_length_eq_eulerTrace_depths`,
  `Succinct.eulerParens_length_eq_eulerTrace_nodes`,
  `Succinct.eulerParens_balanced`,
  `Succinct.eulerParensForest_balanced`,
  `Succinct.depthsFromParens_eulerParens`,
  `Succinct.plusMinusOneInputOfEulerParens_depths`,
  `Succinct.plusMinusOneInputOfEulerParens_depths_eq_trace`,
  `Succinct.plusMinusOneInputOfEulerParens_adjacent`,
  `Succinct.packedBalancedEulerParens_bits`,
  `Succinct.packedEulerParensBackend_queryBuilt_eq_table`,
  `Succinct.packedEulerParensRMQ_payloadBitCount_eq`,
  `Succinct.packedEulerParensRMQ_payloadBitCount_add_one_eq_trace_nodes`,
  `Succinct.packedEulerParensRMQ_payloadCapacityBits_eq`,
  `Succinct.packedEulerParensRMQ_payloadCapacityBits_add_one_eq_trace_nodes`,
  `Succinct.select_none_of_length_le_occurrence`,
  `Succinct.select_min_length_eq`,
  `Succinct.packedEulerParensRMQ_space_profile`.
- `RMQ/Core/SuccinctSpace.lean`:
  `SuccinctSpace.bpCode_balanced`,
  `SuccinctSpace.bpParensOfShape_bits_length_of_shapeOfSize`,
  `SuccinctSpace.bpCloseOfInorder?_some_of_lt`,
  `SuccinctSpace.bpCloseOfInorder?_bounds`,
  `SuccinctSpace.bpCode_rankFalse_full`,
  `SuccinctSpace.bpCloseOfInorder?_rankFalse_succ`,
  `SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?`,
  `SuccinctSpace.littleOLinear_zero`,
  `SuccinctSpace.littleOLinear_const`,
  `SuccinctSpace.LittleOLinear.of_le`,
  `SuccinctSpace.LittleOLinear.of_eventually_le`,
  `SuccinctSpace.LittleOLinear.mul_left`,
  `SuccinctSpace.LittleOLinear.mul_right`,
  `SuccinctSpace.LittleOLinear.comp_two_mul_arg`,
  `SuccinctSpace.LittleOLinear.add`,
  `SuccinctSpace.LittleOLinear.add_const`,
  `SuccinctSpace.LittleOLinear.const_add`,
  `SuccinctSpace.littleOLinear_id_div_log2_succ`,
  `SuccinctSpace.nat_succ_le_two_pow`,
  `SuccinctSpace.nat_le_two_pow`,
  `SuccinctSpace.two_mul_le_two_pow`,
  `SuccinctSpace.eventually_scale_log2_succ_le_self`,
  `SuccinctSpace.eventually_scale_logLog_succ_le_log_succ`,
  `SuccinctSpace.sampledDirectoryOverhead_littleO`,
  `SuccinctSpace.logLogSampledDirectoryOverhead_littleO`,
  `SuccinctSpace.logLogSquaredSampledDirectoryOverhead_littleO`,
  `SuccinctSpace.natToBitsLE_length`,
  `SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt`,
  `SuccinctSpace.optionNatToBitsLE_length`,
  `SuccinctSpace.bitsToOptionNatLE_optionNatToBitsLE_of_bound`,
  `SuccinctSpace.storedWordSelectSampleToBitsLE_length`,
  `SuccinctSpace.optionStoredWordSelectSampleToBitsLE_length`,
  `SuccinctSpace.bitsToStoredWordSelectSample_optionToBits_of_bound`,
  `SuccinctSpace.flattenPayloadWords_length_of_forall_length`,
  `SuccinctSpace.flattenPayloadWords_append`,
  `SuccinctSpace.flattenPayloadWords_replicate_nil`,
  `SuccinctSpace.flattenPayloadWords_chunkPayloadWords`,
  `SuccinctSpace.chunkPayloadWords_word_length_le`,
  `SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt`,
  `SuccinctSpace.BoundedPayloadWordStore.ofChunks_erases`,
  `SuccinctSpace.BoundedPayloadWordStore.ofChunks_word_length_le`,
  `SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel_erases`,
  `SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel_word_length_le`,
  `SuccinctSpace.FixedWidthNatTable.ofEncodedWords_profile`,
  `SuccinctSpace.FixedWidthNatTable.ofEntries_profile`,
  `SuccinctSpace.FixedWidthNatTable.readCosted_cost_le_one`,
  `SuccinctSpace.FixedWidthNatTable.readCosted_erase`,
  `SuccinctSpace.FixedWidthNatTable.profile`,
  `SuccinctSpace.FixedWidthOptionNatTable.ofEncodedWords_profile`,
  `SuccinctSpace.FixedWidthOptionNatTable.ofEntries_profile`,
  `SuccinctSpace.FixedWidthRankSampleTables.ofEncodedWords_profile`,
  `SuccinctSpace.FixedWidthRankSampleTables.ofEntries_profile`,
  `SuccinctSpace.FixedWidthRankSampleTables.sampleCosted_cost_le_one`,
  `SuccinctSpace.FixedWidthRankSampleTables.sampleCosted_erase`,
  `SuccinctSpace.FixedWidthRankSampleTables.profile`,
  `SuccinctSpace.PayloadLiveStoredWordRankData.rankCosted_cost_le_three`,
  `SuccinctSpace.PayloadLiveStoredWordRankData.rankCostedClamped_cost_le_three`,
  `SuccinctSpace.PayloadLiveStoredWordRankData.rankCosted_exact`,
  `SuccinctSpace.PayloadLiveStoredWordRankData.rankCostedClamped_exact`,
  `SuccinctSpace.PayloadLiveStoredWordRankData.profile`,
  `SuccinctSpace.FixedWidthSelectSampleTable.ofEncodedWords_profile`,
  `SuccinctSpace.FixedWidthSelectSampleTable.ofEntries_profile`,
  `SuccinctSpace.FixedWidthSelectSampleTable.readCosted_cost_le_one`,
  `SuccinctSpace.FixedWidthSelectSampleTable.readCosted_erase`,
  `SuccinctSpace.FixedWidthSelectSampleTable.profile`,
  `SuccinctSpace.FixedWidthSelectSampleTables.ofEncodedWords_profile`,
  `SuccinctSpace.FixedWidthSelectSampleTables.ofEntries_profile`,
  `SuccinctSpace.FixedWidthSelectSampleTables.sampleCosted_cost_le_one`,
  `SuccinctSpace.FixedWidthSelectSampleTables.sampleCosted_erase`,
  `SuccinctSpace.FixedWidthSelectSampleTables.profile`,
  `SuccinctSpace.PayloadLiveStoredWordSelectData.selectCosted_cost_le_three`,
  `SuccinctSpace.PayloadLiveStoredWordSelectData.selectCosted_exact`,
  `SuccinctSpace.PayloadLiveStoredWordSelectData.profile`,
  `SuccinctSpace.RankSelectDirectory.auxPayload_length`,
  `SuccinctSpace.RankSelectDirectory.rankQueryCosted_cost_le`,
  `SuccinctSpace.RankSelectDirectory.selectQueryCosted_cost_le`,
  `SuccinctSpace.RankSelectDirectory.rankQueryCosted_erase`,
  `SuccinctSpace.RankSelectDirectory.selectQueryCosted_erase`,
  `SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankSelectData_profile`,
  `SuccinctSpace.PayloadLiveStoredWordRankSelectFamily.constant_query_profile`,
  `SuccinctSpace.PayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile`,
  `SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankStoredSelectData_profile`,
  `SuccinctSpace.RankSelectDirectory.ofStoredWordData_profile`,
  `SuccinctSpace.RankSelectFamily.constant_query_profile`,
  `SuccinctSpace.StoredWordRankData.rankCosted_cost_le_three`,
  `SuccinctSpace.StoredWordRankData.rankCostedClamped_cost_le_three`,
  `SuccinctSpace.StoredWordRankData.rankCosted_exact`,
  `SuccinctSpace.StoredWordRankData.rankCostedClamped_exact`,
  `SuccinctSpace.StoredWordRankData.rankCosted_profile`,
  `SuccinctSpace.StoredWordSelectData.selectCosted_cost_le_three`,
  `SuccinctSpace.StoredWordSelectData.selectCosted_exact`,
  `SuccinctSpace.StoredWordSelectData.selectCosted_profile`,
  `SuccinctSpace.PayloadBackedStoredWordRankData.rankCosted_profile`,
  `SuccinctSpace.PayloadBackedStoredWordSelectData.selectCosted_profile`,
  `SuccinctSpace.PayloadBackedStoredWordRankSelectData.directory_profile`,
  `SuccinctSpace.PayloadBackedStoredWordRankSelectFamily.constant_query_profile`,
  `SuccinctSpace.PayloadBackedStoredWordRankSelectFamily.bp_constant_query_profile`,
  `SuccinctSpace.ValidRankDirectory.ofStoredWordRankData_profile`,
  `SuccinctSpace.ValidRankFamily.constant_query_profile`,
  `SuccinctSpace.ValidRankBalancedParensAccess.profile`,
  `SuccinctSpace.ValidRankBalancedParensAccessFamily.constant_rank_excess_profile`,
  `SuccinctSpace.StoredRankBalancedParensAccess.rankCosted_cost_le_three`,
  `SuccinctSpace.StoredRankBalancedParensAccess.rankCosted_exact`,
  `SuccinctSpace.StoredRankBalancedParensAccess.close_rank_le_open_rank`,
  `SuccinctSpace.StoredRankBalancedParensAccess.final_rank_eq`,
  `SuccinctSpace.StoredRankBalancedParensAccess.excessCosted_cost_le_six`,
  `SuccinctSpace.StoredRankBalancedParensAccess.excessCosted_exact`,
  `SuccinctSpace.StoredRankBalancedParensAccess.profile`,
  `SuccinctSpace.StoredRankBalancedParensAccessFamily.constant_rank_excess_profile`,
  `SuccinctSpace.BalancedParensAccess.auxPayload_length`,
  `SuccinctSpace.BalancedParensAccess.rankCosted_cost_le`,
  `SuccinctSpace.BalancedParensAccess.selectCosted_cost_le`,
  `SuccinctSpace.BalancedParensAccess.rankCosted_erase`,
  `SuccinctSpace.BalancedParensAccess.selectCosted_erase`,
  `SuccinctSpace.BalancedParensAccess.close_rank_le_open_rank`,
  `SuccinctSpace.BalancedParensAccess.final_rank_eq`,
  `SuccinctSpace.BalancedParensAccess.excessCosted_erase`,
  `SuccinctSpace.BalancedParensAccess.excessCosted_cost_le`,
  `SuccinctSpace.BalancedParensAccess.ofPayloadBackedStoredWordRankSelectData_profile`,
  `SuccinctSpace.BalancedParensAccess.ofShapePayloadBackedStoredWordRankSelectData_close_profile`,
  `SuccinctSpace.BalancedParensAccess.ofPayloadLiveStoredWordRankSelectData_profile`,
  `SuccinctSpace.BalancedParensAccess.ofShapePayloadLiveStoredWordRankSelectData_close_profile`,
  `SuccinctSpace.BalancedParensAccessFamily.constant_query_profile`,
  `SuccinctSpace.BroadwordRMQDirectory.queryStateCosted_cost_le`,
  `SuccinctSpace.BroadwordRMQDirectory.queryStateCosted_exact`,
  `SuccinctSpace.BroadwordRMQDirectory.payloadBitCount_eq`,
  `SuccinctSpace.BroadwordRMQDirectory.payloadSpaceBounds_lower_le_upper`,
  `SuccinctSpace.BroadwordRMQDirectory.logSlackLower_le_payloadBudget`,
  `SuccinctSpace.BroadwordRMQDirectory.padToOverhead_payloadBitCount_eq`,
  `SuccinctSpace.BroadwordRMQDirectory.padToOverhead_queryStateCosted_cost_le`,
  `SuccinctSpace.BroadwordSuccinctRMQFamily.two_n_plus_o_constant_query_profile`,
  `SuccinctSpace.bpAuxOverhead_littleO`,
  `SuccinctSpace.sampledBPAuxOverhead_littleO`,
  `SuccinctSpace.BPBroadwordRMQDirectory.payloadOf_eq`,
  `SuccinctSpace.BPBroadwordRMQDirectory.payloadBitCount_eq`,
  `SuccinctSpace.BPBroadwordRMQDirectory.payloadSpaceBounds_lower_le_upper`,
  `SuccinctSpace.FixedWidthOptionNatTable.readCosted_cost_le_one`,
  `SuccinctSpace.FixedWidthOptionNatTable.readCosted_erase`,
  `SuccinctSpace.FixedWidthOptionNatTable.profile`,
  `SuccinctSpace.StoredBPCloseLCADirectory.lcaCloseCosted_cost`,
  `SuccinctSpace.StoredBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctSpace.StoredBPCloseLCADirectory.profile`,
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory.lcaCloseCosted_cost_le_one`,
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory.profile`,
  `SuccinctSpace.StoredBPCloseLCAFamily.constant_lca_close_profile`,
  `SuccinctSpace.BPCloseRMQNavigationDirectory.queryEncodedCosted_cost_le`,
  `SuccinctSpace.BPCloseRMQNavigationDirectory.queryEncodedCosted_exact`,
  `SuccinctSpace.BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile`,
  `SuccinctSpace.bpCloseNavigationOverhead_littleO`,
  `SuccinctSpace.EncodedPayloadLiveBPCloseRMQNavigationView.toBPCloseRMQNavigationDirectory`,
  `SuccinctSpace.EncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_encoded_query_profile`,
  `SuccinctSpace.SampledEncodedPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO`,
  `SuccinctSpace.SampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_sampled_encoded_query_profile`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationDirectory.queryBuiltCosted_cost_le_ten`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationDirectory.queryBuiltCosted_exact`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationDirectory.profile`,
  `SuccinctSpace.PayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`,
  `SuccinctSpace.SampledPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO`,
  `SuccinctSpace.SampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`,
  `SuccinctSpace.WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO`,
  `SuccinctSpace.WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_bounded_built_query_profile`,
  `SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.overhead_littleO`,
  `SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_word_bounded_encoded_query_profile`,
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory.ofEntries_profile`,
  `SuccinctSpace.BPBroadwordSuccinctRMQFamily.two_n_plus_o_constant_query_profile`,
  `SuccinctSpace.ComponentizedBPRMQFamily.overhead_littleO`,
  `SuccinctSpace.ComponentizedBPRMQFamily.two_n_plus_o_constant_query_profile`.
- `RMQ/Core/SuccinctRankProposal.lean`:
  `SuccinctRankProposal.rankSampleEntries_getOpt_exact`,
  `SuccinctRankProposal.canonicalSuperRankEntries_getOpt_exact`,
  `SuccinctRankProposal.canonicalBlockRankEntries_getOpt_exact`,
  `SuccinctRankProposal.chunkPayloadWords_rankPrefix_exact`,
  `SuccinctRankProposal.ofChunks_rankPrefix_exact`,
  `SuccinctRankProposal.ofChunks_word_present_of_lt`,
  `SuccinctRankProposal.ofChunksWithSentinel_word_present`,
  `SuccinctRankProposal.ofChunksWithSentinel_rankPrefix_exact`,
  `SuccinctRankProposal.canonicalSuperRankSampleTables_present`,
  `SuccinctRankProposal.canonicalBlockRankSampleTables_present`,
  `SuccinctRankProposal.canonicalBlockRankEntries_mem_bound_of_local_span`,
  `SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_present`,
  `SuccinctRankProposal.canonicalBlockRankSampleTablesOfLocalSpan_payload_length`,
  `SuccinctRankProposal.canonicalRankParts_exact_of_word_local`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfBridge`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfBridgeLocalBlock`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksPresent`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksPresentLocalBlock`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExact`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfBridge_profile`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExact_profile`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfBridgeLocalBlock_profile`,
  `SuccinctRankProposal.canonicalTwoLevelRankDataOfChunksExactLocalBlock_profile`,
  `SuccinctRankProposal.twoLevelRankOverhead_littleO`,
  `SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData.rankCosted_cost_le_four`,
  `SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankData.profile`,
  `SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankFamily.constant_query_profile`,
  `SuccinctRankProposal.canonicalTwoLevelRankSuperOverhead_littleO`,
  `SuccinctRankProposal.canonicalTwoLevelRankBlockOverhead_littleO`,
  `SuccinctRankProposal.canonicalTwoLevelRankOverhead_littleO`,
  `SuccinctRankProposal.fixedWidthRankSampleTables_payload_length_eq_budget`,
  `SuccinctRankProposal.fixedWidthRankSampleTables_payload_length_le_sampled`,
  `SuccinctRankProposal.SampledPayloadLiveStoredWordRankData.profile`,
  `SuccinctRankProposal.SampledPayloadLiveStoredWordRankFamily.bounded_constant_query_profile`,
  `SuccinctRankProposal.ExactSampledPayloadLiveStoredWordRankFamily.constant_query_profile`,
  `SuccinctRankProposal.ExactSampledPayloadLiveStoredWordRankFamily.bounded_constant_query_profile`.
- `RMQ/Core/SuccinctSelectProposal.lean`:
  `SuccinctSelectProposal.selectSampleAt?_some_fields`,
  `SuccinctSelectProposal.selectSampleAt?_some_field_bounds`,
  `SuccinctSelectProposal.selectSuperSampleEntries_present_of_lt`,
  `SuccinctSelectProposal.selectBlockDeltaEntries_present_of_lt`,
  `SuccinctSelectProposal.selectBlockDeltaEntry?_add_exact_of_le`,
  `SuccinctSelectProposal.selectBlockDeltaEntry?_select_some_exact_of_word`,
  `SuccinctSelectProposal.SelectSampleWordExact.exists_word_offset_of_select`,
  `SuccinctSelectProposal.SelectSampleWordExact.selected_position_in_read_word`,
  `SuccinctSelectProposal.SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word`,
  `SuccinctSelectProposal.SelectSampleWordExact.shared_aligned_read_word_forces_same_wordIndex`,
  `SuccinctSelectProposal.canonicalSelectSuperTablesFinite_present`,
  `SuccinctSelectProposal.canonicalSelectBlockTablesFinite_present`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectData`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectData_selectCosted_profile`,
  `SuccinctSelectProposal.selectSampleAt?_slice_word_exact`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectDataOfChunksExact`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectDataOfChunksExact_selectCosted_profile`,
  `SuccinctSelectProposal.fixedWidthSelectSampleTables_payload_length_eq_budget`,
  `SuccinctSelectProposal.fixedWidthSelectSampleTables_payload_length_le_sampled`,
  `SuccinctSelectProposal.twoLevelSelectOverhead_littleO`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.selectCosted_cost_le_four`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.selected_position_in_read_word_of_sample`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.selected_wordIndex_eq_of_sample`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.shared_local_locator_forces_same_selected_wordIndex`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.shared_local_locator_contradicts_distinct_selected_wordIndex`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData.profile`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectFamily.constant_query_profile`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectSuperOverhead_littleO`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectBlockOverhead_littleO`,
  `SuccinctSelectProposal.canonicalTwoLevelSelectOverhead_littleO`,
  `SuccinctSelectProposal.twoLevelRankSelectOverhead_littleO`,
  `SuccinctSelectProposal.canonicalTwoLevelRankSelectOverhead_littleO`,
  `SuccinctSelectProposal.twoLevelRankSelectDirectory_profile`,
  `SuccinctSelectProposal.canonicalTwoLevelRankSelectDirectoryOfChunksExact_profile`,
  `SuccinctSelectProposal.canonicalTwoLevelRankSelectDirectoryOfChunksExactLocalRankBlock_profile`,
  `SuccinctSelectProposal.canonicalTwoLevelBalancedParensAccessOfChunksExact_profile`,
  `SuccinctSelectProposal.canonicalTwoLevelBalancedParensAccessOfChunksExactLocalRankBlock_profile`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily.constant_query_profile`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily.word_bounded_constant_query_profile`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile`,
  `SuccinctSelectProposal.twoLevelBPCloseNavigationOverhead_littleO`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveBPCloseRMQNavigationDirectory.profile`,
  `SuccinctSelectProposal.TwoLevelPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`,
  `SuccinctSelectProposal.TwoLevelEncodedBPCloseRMQNavigationView.toBPCloseRMQNavigationDirectory`,
  `SuccinctSelectProposal.TwoLevelEncodedBPCloseRMQNavigationFamily.two_n_plus_o_encoded_query_profile`,
  `SuccinctSelectProposal.SampledPayloadLiveStoredWordSelectData.profile`,
  `SuccinctSelectProposal.SampledPayloadLiveStoredWordSelectFamily.bounded_constant_query_profile`,
  `SuccinctSelectProposal.ExactSampledPayloadLiveStoredWordSelectFamily.constant_query_profile`,
  `SuccinctSelectProposal.ExactSampledPayloadLiveStoredWordSelectFamily.bounded_constant_query_profile`.
- `RMQ/Core/SuccinctCloseProposal.lean`:
  `SuccinctCloseProposal.closeToInorder_eq_of_bpCloseOfInorder?`,
  `SuccinctCloseProposal.densePairSlot_lt`,
  `SuccinctCloseProposal.densePairSlot_div`,
  `SuccinctCloseProposal.densePairSlot_mod`,
  `SuccinctCloseProposal.concreteBlockLocalBPCloseLCAEntries_length`,
  `SuccinctCloseProposal.concreteBlockLocalBPCloseLCAEntries_mem_bound`,
  `SuccinctCloseProposal.concreteBlockLocalBPCloseLCAEntries_spec`,
  `SuccinctCloseProposal.blockLocalBPCloseLCA_read_exact`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.payload_length`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.lcaCloseCosted_cost_le_one`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.lcaCloseCosted_exact`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.profile`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.ofEntries_profile`,
  `SuccinctCloseProposal.BlockLocalBPCloseLCATable.concrete_profile`,
  `SuccinctCloseProposal.denseAllCloseBPCloseLCATable_profile`,
  `SuccinctCloseProposal.denseAllCloseBPCloseLCATable_payload_length_of_shapeOfSize`,
  `SuccinctCloseProposal.not_littleOLinear_square`,
  `SuccinctCloseProposal.denseAllCloseBPCloseLCAOverhead_not_littleO`,
  `SuccinctCloseProposal.blockStartOf_blockOfClose_le`,
  `SuccinctCloseProposal.close_lt_blockStartOf_blockOfClose_add`,
  `SuccinctCloseProposal.bpExcessAt_le_length`,
  `SuccinctCloseProposal.bpExcessAt_prefix_nonnegative`,
  `SuccinctCloseProposal.bpExcessAt_add_close_rank_eq_open_rank_of_le`,
  `SuccinctCloseProposal.bpExcessAt_close_succ_add_inorder_succ_eq_open_rank`,
  `SuccinctCloseProposal.bpExcessAt_node_left_prefix_succ`,
  `SuccinctCloseProposal.bpExcessAt_node_right_prefix_shift`,
  `SuccinctCloseProposal.bpCloseOfInorder?_lt_of_lt`,
  `SuccinctCloseProposal.answerClose_prefix_mem_endpoint_prefix_range`,
  `SuccinctCloseProposal.bpBlockMinExcess_le_length`,
  `SuccinctCloseProposal.bpBlockMaxExcess_le_length`,
  `SuccinctCloseProposal.bpBlockArgMinPrefixPos_le_length`,
  `SuccinctCloseProposal.bpBlockMinExcessEntries_mem_bound`,
  `SuccinctCloseProposal.bpBlockMaxExcessEntries_mem_bound`,
  `SuccinctCloseProposal.bpBlockArgMinPrefixPosEntries_mem_bound`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.payload_length`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.summaryCosted_cost_le_two`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.summaryCosted_erase`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.minExcess_read_word_length_le_machine`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.maxExcess_read_word_length_le_machine`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.summary_read_words_length_le_machine`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxSummaryTable.profile`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_profile`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_sampled_profile`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_read_words_length_le_machine`,
  `SuccinctCloseProposal.compactBPCloseSummaryPayloadOverhead_littleO`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxSummaryTable_compact_summary_profile`,
  `SuccinctCloseProposal.relativeBPCloseSummaryPayloadOverhead_littleO`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_profile`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_relative_payload_profile`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_compact_payload_profile`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_read_words_length_le_machine`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile`,
  `SuccinctCloseProposal.canonicalBPRelativeMinMaxArgSummaryTableActive_of_large`,
  `SuccinctCloseProposal.concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile_of_large`,
  `SuccinctCloseProposal.canonicalBPRelativeSummaryLargeRegime_of_size_ge`,
  `SuccinctCloseProposal.canonicalBPRelativeSummaryRelativeWidthRaw_machine_of_large`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorOverhead_littleO`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_large`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_twoLevel_budget_profile_of_size_ge`,
  `SuccinctCloseProposal.bpTwoLevelInteriorCandidateCosted_erase_exact`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorLocalTable_payload_le_budget_of_size_ge`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorGlobalTable_payload_le_budget_of_size_ge`,
  `SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile`,
  `SuccinctCloseProposal.PayloadLiveBPRangeMinMaxArgSummaryTable.profile`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxArgSummaryTable_sampled_profile`,
  `SuccinctCloseProposal.concreteBPRangeMinMaxArgSummaryTable_read_words_length_le_machine`,
  `SuccinctCloseProposal.PayloadLiveBPRangeArgMinWitnessTable.rangeCloseCosted_exact_of_prefix_pos`,
  `SuccinctCloseProposal.PayloadLiveBPRangeArgMinWitnessTable.profile`,
  `SuccinctCloseProposal.concreteBPRangeArgMinWitnessTable_sampled_profile`,
  `SuccinctCloseProposal.concreteBPRangeArgMinWitnessTable_read_words_length_le_machine`,
  `SuccinctCloseProposal.blockPairRanges_get?_of_ordered_bounds`,
  `SuccinctCloseProposal.PayloadLiveBPBlockPairRangeWitnessMacro.lcaCloseCosted_exact_of_prefix_pos`,
  `SuccinctCloseProposal.PayloadLiveBPBlockPairRangeWitnessMacro.profile`,
  `SuccinctCloseProposal.concreteBPBlockPairRangeWitnessMacro_sampled_profile`,
  `SuccinctCloseProposal.concreteBPBlockPairRangeWitnessMacro_read_words_length_le_machine`,
  `SuccinctCloseProposal.blockStartOf_succ`,
  `SuccinctCloseProposal.blockStartOf_mono`,
  `SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPosFrom_eq_best_of_best_le_all`,
  `SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPosFrom_eq_of_leftmost_min_excess`,
  `SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPos_eq_of_leftmost_min_excess`,
  `SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPos_mem_range`,
  `SuccinctCloseProposal.bpPrefixRangeArgMinPrefixPos_excess_le_offset`,
  `SuccinctCloseProposal.bpPrefixRangeMinExcess_eq_of_leftmost_min_excess`,
  `SuccinctCloseProposal.bpPrefixRangeWitness_eq_of_leftmost_min_excess`,
  `SuccinctCloseProposal.bpBlockArgMinPrefixPos_eq_prefixRangeArgMinPrefixPos`,
  `SuccinctCloseProposal.bpBlockArgMinPrefixPos_eq_of_leftmost_min_excess`,
  `SuccinctCloseProposal.bpBlockArgMinPrefixPos_mem_range`,
  `SuccinctCloseProposal.bpRangeArgMinPrefixPosFrom_eq_best_of_best_le_all`,
  `SuccinctCloseProposal.bpRangeArgMinPrefixPosFrom_eq_of_leftmost_block_candidate`,
  `SuccinctCloseProposal.bpRangeArgMinPrefixPos_eq_of_leftmost_block_candidate`,
  `SuccinctCloseProposal.bpRangeWitness_eq_of_leftmost_block_candidate`,
  `SuccinctCloseProposal.bpRangeArgMinPrefixPos_mem_prefix_range`,
  `SuccinctCloseProposal.bpPrefixRangeMinExcess_ge_of_all_prefix_ge`,
  `SuccinctCloseProposal.bpPrefixRangeMinExcess_gt_of_all_prefix_gt`,
  `SuccinctCloseProposal.bpRangeMinExcess_ge_of_all_prefix_ge`,
  `SuccinctCloseProposal.bpRangeMinExcess_gt_of_all_prefix_gt`,
  `SuccinctCloseProposal.bpPrefixRangeMinExcess_le_prefix_of_mem`,
  `SuccinctCloseProposal.bpEndpointPrefixRangeMinExcess_le_answerClose`,
  `SuccinctCloseProposal.endpointPrefixRangeWitness_eq_answerClose_of_spanning_root`,
  `SuccinctCloseProposal.answerClose_prefix_leftmost_min_excess_of_query`,
  `SuccinctCloseProposal.endpointLeftFringeMinExcessEntries_get?_of_close_bounds`,
  `SuccinctCloseProposal.endpointLeftFringeArgMinEntries_get?_of_close_bounds`,
  `SuccinctCloseProposal.endpointRightFringeMinExcessEntries_get?_of_close_bounds`,
  `SuccinctCloseProposal.endpointRightFringeArgMinEntries_get?_of_close_bounds`,
  `SuccinctCloseProposal.interiorBlockPairRangeMinExcessEntries_get?_of_gap_bounds`,
  `SuccinctCloseProposal.interiorBlockPairRangeArgMinEntries_get?_of_gap_bounds`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_merged_candidate`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_left_fringe_leftmost`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_right_fringe_candidate`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_decoded_middle_candidate`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_spanning_root_left_fringe`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_spanning_root_right_fringe`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.lcaCloseCosted_exact_of_query_cross_block`,
  `SuccinctCloseProposal.PayloadLiveBPEndpointFringeRangeMacro.profile_cross_block_exact`,
  `SuccinctCloseProposal.concreteBPEndpointFringeRangeMacro_sampled_query_profile`,
  `SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient`,
  `SuccinctCloseProposal.endpointSummaryBlockKey`,
  `SuccinctCloseProposal.endpointSummaryBlockMacroDirectory_not_sufficient`,
  `SuccinctCloseProposal.BlockMicroCodebook.payload_length`,
  `SuccinctCloseProposal.BlockMicroCodebook.lcaCloseCosted_cost_le_one`,
  `SuccinctCloseProposal.BlockMicroCodebook.lcaCloseCostedAtBlock_exact`,
  `SuccinctCloseProposal.BlockMicroCodebook.lcaCloseCosted_exact_of_left_block`,
  `SuccinctCloseProposal.BlockMicroCodebook.profile`,
  `SuccinctCloseProposal.MacroMicroBPCloseLCADirectory.payload_length`,
  `SuccinctCloseProposal.MacroMicroBPCloseLCADirectory.lcaCloseCosted_cost_le`,
  `SuccinctCloseProposal.MacroMicroBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctCloseProposal.MacroMicroBPCloseLCADirectory.profile`,
  `SuccinctCloseProposal.BlockCodeTable.payload_length`,
  `SuccinctCloseProposal.BlockCodeTable.codeAt_exists_of_lt`,
  `SuccinctCloseProposal.BlockCodeTable.codeCosted_erase`,
  `SuccinctCloseProposal.BlockCodeTable.profile`,
  `SuccinctCloseProposal.BlockCodeTable.ofEntries_profile`,
  `SuccinctCloseProposal.PayloadLiveBlockMicroCodebook.payload_length`,
  `SuccinctCloseProposal.PayloadLiveBlockMicroCodebook.lcaCloseCosted_cost_le_two`,
  `SuccinctCloseProposal.PayloadLiveBlockMicroCodebook.lcaCloseCosted_exact_of_left_block`,
  `SuccinctCloseProposal.PayloadLiveBlockMicroCodebook.profile`,
  `SuccinctCloseProposal.PayloadLiveBlockEndpointFringeCodebook.profile`,
  `SuccinctCloseProposal.PayloadLiveBlockEndpointFringeCodebook.read_words_length_le_machine`,
  `SuccinctCloseProposal.concretePayloadLiveBlockEndpointFringeCodebook_profile`,
  `SuccinctCloseProposal.concretePayloadLiveBlockEndpointFringeCodebook_canonical_profile`,
  `SuccinctCloseProposal.PayloadLiveCompactEndpointRelativeRmmBPCloseMacro.lcaCloseCosted_exact_of_query_cross_block`,
  `SuccinctCloseProposal.PayloadLiveCompactEndpointRelativeRmmBPCloseMacro.read_words_length_le_machine`,
  `SuccinctCloseProposal.PayloadLiveCompactEndpointRelativeRmmBPCloseMacro.profile`,
  `SuccinctCloseProposal.concretePayloadLiveCompactEndpointRelativeRmmBPCloseMacro_profile`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCADirectory.payload_length`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCADirectory.lcaCloseCosted_cost_le`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCADirectory.profile`,
  `SuccinctCloseProposal.PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory.payload_length`,
  `SuccinctCloseProposal.PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctCloseProposal.PayloadLiveGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory.profile`,
  `SuccinctCloseProposal.concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile`,
  `SuccinctCloseProposal.guardedEndpointFringeMacroMicroOverhead_littleO`,
  `SuccinctCloseProposal.bpRelativeRmmCandidateMerge_exact`,
  `SuccinctCloseProposal.PayloadLiveRelativeRmmBPCloseMacro.lcaCloseCosted_exact_of_query_cross_block`,
  `SuccinctCloseProposal.PayloadLiveRelativeRmmBPCloseMacro.profile`,
  `SuccinctCloseProposal.PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory.lcaCloseCosted_exact`,
  `SuccinctCloseProposal.PayloadLiveRelativeRmmMacroMicroBPCloseLCADirectory.profile`,
  `SuccinctCloseProposal.relativeRmmMacroMicroBPCloseLCAOverhead_littleO`,
  `SuccinctCloseProposal.relativeRmmMacroMicroBPCloseLCADirectory_profile`,
  `SuccinctCloseProposal.emptyPayloadLiveBlockMicroCodebook_lcaCloseCosted_erase`,
  `SuccinctCloseProposal.denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile`,
  `SuccinctCloseProposal.payloadLiveMacroMicroBPCloseLCAOverhead_littleO`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCAFamily.overhead_littleO`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseLCAFamily.profile`,
  `SuccinctCloseProposal.payloadLiveMacroMicroBPCloseNavigationOverhead_littleO`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.overhead_littleO`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.payload_length`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.queryBuiltCosted_cost_le`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.queryBuiltCosted_exact`,
  `SuccinctCloseProposal.PayloadLiveMacroMicroBPCloseNavigationFamily.two_n_plus_o_built_query_profile`.
- `RMQ/Core/SuccinctFinal.lean` (24):
  `SuccinctFinal.PayloadLiveBPCloseAccessFamily.constant_query_profile`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.payload_length_le_overhead`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.selectCloseCosted_cost_le`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.rankCloseCosted_cost_le`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.selectCloseCosted_exact`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.rankCloseCosted_exact`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.rank_read_words_length_le_machine`,
  `SuccinctFinal.ReadBackedBPCloseAccessDirectory.select_read_words_length_le_machine`,
  `SuccinctFinal.ReadBackedBPCloseAccessFamily.constant_query_profile`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQOverhead_littleO`,
  `SuccinctFinal.concreteBPNativeSelectCloseCosted_cost_le`,
  `SuccinctFinal.concreteBPNativeRankCloseCosted_cost_le`,
  `SuccinctFinal.concreteBPNativeLCACloseCosted_cost_le`,
  `SuccinctFinal.concreteBPNativeSelectCloseCosted_exact`,
  `SuccinctFinal.concreteBPNativeRankCloseCosted_exact`,
  `SuccinctFinal.concreteBPNativeCloseAccessPayload_length_le_overhead`,
  `SuccinctFinal.concreteBPNativeLCACloseCosted_exact`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQAuxPayload_length`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQPayload_length`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted_cost_le`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted_exact`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`,
  `SuccinctFinal.readBackedBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`,
  `SuccinctFinal.concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile_of_rankSelectFamily`.
- `RMQ/Core/SuccinctReduction.lean` (7):
  `Succinct.rmqBackendOfEulerParensBackend_queryBuilt`,
  `Succinct.lcaCandidateOfEulerParensBackend_eq_queryBuilt`,
  `Succinct.lcaCandidateOfEulerParensBackend_isPathLCA_of_tracePathAgreement`,
  `Succinct.lcaCandidateOfEulerParensBackend_isPathLCA_of_labelsUnique`,
  `Succinct.packedEulerParensLCACandidate_eq_queryBuilt`,
  `Succinct.packedEulerParensLCACandidate_isPathLCA_of_tracePathAgreement`,
  `Succinct.packedEulerParensLCACandidate_isPathLCA_of_labelsUnique`.
- `RMQ/Core/Reduction.lean` (6):
  `RoseTree.leftmostMinNode?_eq_pathLCA_of_labelPairAgreement`,
  `EulerTrace.lcaCandidate_eq_leftmostMinNode?`,
  `RMQToLCAReduction.queryWithLCABackend_sound`,
  `RMQToLCAReduction.queryWithLCABackend_complete`,
  `RMQToLCAReduction.queryWithLCABackend_invalid_none`,
  `rmq_lca_reduction_equiv_exists`.
- `RMQ/Core/Cartesian.lean` (25): `betterIndex_eq_left_or_right`,
  `scanWindow_bounds`, `indexPath_root`, `indexPath_exists_of_inRange`,
  `indexPath_none_of_not_inRange`, `indexPath_head_inRange`,
  `commonPrefix_eq_nil_of_head_separated`,
  `pathLCA?_root_cons_of_tail_separated`,
  `pathLCA?_root_cons_of_tail_lca`, `pathToForest?_append_none`,
  `pathToForest?_append_left_some`, `pathToForest?_append_right_of_left_none`,
  `treeRange_pathTo?_none_of_not_inRange`,
  `treeRange_pathTo?_exists_of_inRange`, `treeRange_pathTo?_eq_indexPath`,
  `treeRange_root_leftmost`, `treeRange_pathTo_root`,
  `treeRange_pathLCA_root_root`, `treeRange_pathLCA_root_of_contains`,
  `treeRange_pathLCA_left_lift`, `treeRange_pathLCA_right_lift`,
  `leftmostArgMin_restrict_containing`, `treeRange_root_leftmost_of_contains`,
  `treeRange_rangeLCASpec`, `builtRangeLCASpec`.

### Implementations

- `RMQ/Impl/LinearScan.lean` (4): `query_valid_exact`, `query_sound`,
  `query_complete`, `invalid_none`.
- `RMQ/Impl/PlusMinusOne.lean` (7): `PlusMinusOne.query_sound`,
  `PlusMinusOne.query_complete`, `PlusMinusOne.query_invalid_none`,
  `PlusMinusOne.signatureQuery_sound`,
  `PlusMinusOne.signatureQuery_complete`,
  `PlusMinusOne.signatureQuery_invalid_none`,
  `PlusMinusOne.signatureQuery_eq_linearQuery`.
- `RMQ/Impl/SparseTable.lean` (7): `blockArgMin_leftmost_exists`,
  `sparseRow_cell_eq_blockArgMin`, `tableRow_build_eq_sparseRow`,
  `query_valid_exact`, `query_sound`, `query_complete`, `invalid_none`.
- `RMQ/Impl/SparseTableInstrumented.lean` (40):
  `SparseTable.Instrumented.rowArray_get?`,
  `SparseTable.Instrumented.tableRowArray_value_toList`,
  `SparseTable.Instrumented.tableRowArray_value_toList_of_refines`,
  `SparseTable.Instrumented.rowCellArray_value`,
  `SparseTable.Instrumented.rowCellArray_value_toList`,
  `SparseTable.Instrumented.betterIndexArray_value`,
  `SparseTable.Instrumented.combineIndexArray_value`,
  `SparseTable.Instrumented.betterIndexArray_steps_le_three`,
  `SparseTable.Instrumented.combineIndexArray_steps_le_three`,
  `SparseTable.Instrumented.memoNextCellArray_value`,
  `SparseTable.Instrumented.memoNextCellArray_steps_le_five`,
  `SparseTable.Instrumented.memoNextRowArrayValuesFrom_value_toList`,
  `SparseTable.Instrumented.memoNextRowArrayValuesFrom_steps_le`,
  `SparseTable.Instrumented.memoNextRowArray_value_toList`,
  `SparseTable.Instrumented.memoNextRowArray_steps_le`,
  `SparseTable.Instrumented.blockArgMinArraySteps_pos`,
  `SparseTable.Instrumented.blockArgMinArray_value`,
  `SparseTable.Instrumented.blockArgMinArray_steps_le`,
  `SparseTable.Instrumented.rowArrayValuesFrom_value_toList`,
  `SparseTable.Instrumented.rowArrayValuesFrom_steps_le`,
  `SparseTable.Instrumented.sparseRowArrayBuild_value_toList`,
  `SparseTable.Instrumented.sparseRowArrayBuild_steps_le`,
  `SparseTable.Instrumented.memoBuildRowsFromArray_value_toList`,
  `SparseTable.Instrumented.memoBuildRowsFromArray_steps_le`,
  `SparseTable.Instrumented.memoBuildSparseTableArray_value_toList`,
  `SparseTable.Instrumented.memoBuildSparseTableArray_steps_le`,
  `SparseTable.Instrumented.tableRowArray_steps`,
  `SparseTable.Instrumented.rowCellArray_steps`,
  `SparseTable.Instrumented.queryFromArrayTable_value`,
  `SparseTable.Instrumented.queryFromArrayTable_value_of_refines`,
  `SparseTable.Instrumented.query_value`,
  `SparseTable.Instrumented.queryFromArrayTable_steps_le_seven`,
  `SparseTable.Instrumented.query_steps_le_seven`,
  `SparseTable.Instrumented.query_toCosted_sound`,
  `SparseTable.Instrumented.query_refines_and_steps_le_seven`,
  `SparseTable.Instrumented.memoBuild_refine_with_steps`,
  `SparseTable.Instrumented.memoBuild_and_query_refine_with_steps`,
  `SparseTable.Instrumented.memoQueryWithTracedBuild_value`,
  `SparseTable.Instrumented.memoQueryWithTracedBuild_steps_le`,
  `SparseTable.Instrumented.memoQueryWithTracedBuild_refine_with_steps`.
- `RMQ/Impl/SparseTableMemoCost.lean` (35):
  `blockArgMin_none_of_length_le_start`, `sparseRow_cell_eq_blockArgMin_total`,
  `memoNextRow_sparseRow`, `memoNextRowCosted_value`,
  `memoNextRowCosted_erase`, `memoNextRowCosted_cost`,
  `memoNextRowCosted_sparseRow_value`, `memoBaseRowCosted_value`,
  `memoBaseRowCosted_erase`, `memoBaseRowCosted_cost`,
  `memoBuildSparseTableCost_eq_log`, `memoBuildRowsFromCosted_value`,
  `memoBuildRowsFromCosted_erase`, `memoBuildRowsFromCosted_cost`,
  `memoBuildRowsFrom_length`, `memoBuildRowsFrom_get?_sparseRow_of_lt`,
  `memoBuildSparseTableCosted_value`, `memoBuildSparseTableCosted_erase`,
  `memoBuildSparseTableCosted_cost`, `memoBuildSparseTableCosted_run`,
  `memoBuildSparseTable_length`, `tableRow_memoBuildSparseTable_eq_sparseRow`,
  `log2_le_log2_of_le`, `queryLevel_lt_memoRowCount`, `memoQuery_eq_query`.
- `RMQ/Impl/HybridBlock.lean` (14): `chunkSpan_pos`, `chunkSpan_succ`,
  `chunkCell_leftmost_exists`, `chunkRow_cell_eq_chunkCell`,
  `tableRow_build_eq_chunkRow`, `sparseChunkIntervalCover`,
  `sparseChunkQuery_valid_exact`, `publicBlockSize_pos`,
  `queryWithState_invalid_none`, `queryWithState_eq_linear_of_small`,
  `query_valid_exact`, `query_sound`, `query_complete`, `invalid_none`.
- `RMQ/Impl/RecursiveHybrid.lean` (7):
  `queryWithSummaryBackend_invalid_none`,
  `queryWithSummaryBackend_valid_exact`, `queryWithSummaryBackend_sound`,
  `queryWithSummaryBackend_complete`, `query_sound`, `query_complete`,
  `invalid_none`.
- `RMQ/Impl/RecursiveHybridCost.lean` (15):
  `blockMinSummaryCosted_value`, `blockMinSummaryCosted_erase`,
  `blockMinSummaryCosted_cost`, `buildCost_of_small`, `buildCost_of_large`,
  `blockMinSummaryBuildCost_le_length`, `publicCompressedLength_le_half`,
  `blockMinSummary_public_length_le_half`, `two_mul_half_le`,
  `buildCost_le_two_mul_length`, `buildCost_linear`,
  `queryWithSummaryCosted_value`, `queryWithSummaryCosted_erase`,
  `queryWithSummaryCosted_cost`, `queryWithSummaryCosted_run`.
- `RMQ/Impl/LCACost.lean` (113): `LCACost.eulerTraceCosted_erase`,
  `LCACost.eulerTraceCosted_cost`, `LCACost.eulerTraceCosted_run`,
  `LCACost.firstOccurrenceIndex_get?`,
  `LCACost.firstOccurrenceCosted_erase`,
  `LCACost.firstOccurrenceCosted_cost`,
  `LCACost.firstOccurrenceCosted_run`,
  `LCACost.firstOccurrenceDirectRows_length`,
  `LCACost.firstOccurrenceDirectSlots_length`,
  `LCACost.firstOccurrenceDirectSlots_get?_of_lt`,
  `LCACost.firstOccurrenceDirectSlots_get?_of_ge`,
  `LCACost.firstOccurrenceDirectStore_erases`,
  `LCACost.firstOccurrenceDirectStore_get?_of_lt`,
  `LCACost.firstOccurrenceDirectStore_get?_of_ge`,
  `LCACost.firstOccurrence?_eq_none_of_ge_labelsPreorder_length`,
  `LCACost.firstOccurrenceDirectIndex_get?_of_bounded`,
  `LCACost.firstOccurrenceDirectCosted_erase_of_bounded`,
  `LCACost.firstOccurrenceDirectCosted_value_of_bounded`,
  `LCACost.firstOccurrenceDirectCosted_cost`,
  `LCACost.firstOccurrenceDirectCosted_run_of_bounded`,
  `LCACost.firstOccurrenceDirectCosted_eq_firstOccurrenceCosted_of_bounded`,
  `LCACost.setFirstIfNoneList_length`,
  `LCACost.setFirstIfNoneList_get?_ne`,
  `LCACost.setFirstIfNoneList_get?_same_of_none`,
  `LCACost.setFirstIfNoneList_preserves_some`,
  `LCACost.firstOccurrenceRowsFromNodes_preserves_some`,
  `LCACost.firstOccurrenceRowsFromNodes_get?_of_none`,
  `LCACost.firstOccurrenceRowsFromNodes_replicate_get?_of_lt`,
  `LCACost.firstOccurrenceRowsFromNodes_length`,
  `LCACost.firstOccurrenceRowsFromNodes_replicate_length`,
  `LCACost.initFirstOccurrenceSlots_value_toList`,
  `LCACost.initFirstOccurrenceSlots_steps`,
  `LCACost.recordFirstOccurrence_value_toList`,
  `LCACost.recordFirstOccurrence_steps_le_three`,
  `LCACost.buildFirstOccurrenceSlotsFromNodes_value_toList`,
  `LCACost.buildFirstOccurrenceSlotsFromNodes_steps_le`,
  `LCACost.buildFirstOccurrenceDirectArray_value_toReference`,
  `LCACost.buildFirstOccurrenceDirectArray_steps_le`,
  `LCACost.firstOccurrenceRowsFromNodes_replicate_eq_directRows`,
  `LCACost.buildFirstOccurrenceDirectArray_value_toRows`,
  `LCACost.buildFirstOccurrenceDirectArray_refines_with_steps`,
  `LCACost.builtFirstOccurrenceDirectStore_erases`,
  `LCACost.builtFirstOccurrenceDirectStore_get?_of_lt`,
  `LCACost.builtFirstOccurrenceDirectStore_get?_of_ge`,
  `LCACost.builtFirstOccurrenceDirectIndex_get?_of_bounded`,
  `LCACost.builtFirstOccurrenceDirectCosted_eq_firstOccurrenceCosted_of_bounded`,
  `LCACost.nodeIndex_length`,
  `LCACost.nodeIndex_get?`, `LCACost.depthIndex_length`,
  `LCACost.depthIndex_get?`,
  `LCACost.nodeIndex_length_eq_depthIndex_length`,
  `LCACost.buildNodeArray_value_toList`,
  `LCACost.buildNodeArray_steps`,
  `LCACost.buildNodeArray_refines_with_steps`,
  `LCACost.builtNodeStore_erases`,
  `LCACost.builtNodeIndex_length`,
  `LCACost.builtNodeIndex_get?`,
  `LCACost.builtNodeIndex_getCosted_eq_nodeIndex`,
  `LCACost.buildDepthArray_value_toList`,
  `LCACost.buildDepthArray_steps`,
  `LCACost.buildDepthArray_refines_with_steps`,
  `LCACost.builtDepthStore_erases`,
  `LCACost.builtDepthIndex_length`,
  `LCACost.builtDepthIndex_get?`,
  `LCACost.builtDepthIndex_getCosted_eq_depthIndex`,
  `LCACost.nodeAtCosted_erase`, `LCACost.nodeAtCosted_value`,
  `LCACost.nodeAtCosted_cost`, `LCACost.nodeAtCosted_run`,
  `LCACost.depthAtCosted_erase`, `LCACost.depthAtCosted_cost`,
  `LCACost.depthAtCosted_run`, `LCACost.queryCosted_erase`,
  `LCACost.queryCosted_cost`, `LCACost.queryCosted_run`,
  `LCACost.queryViaRMQCosted_erase`, `LCACost.queryViaRMQCosted_cost`,
  `LCACost.rmqQueryCosted_erase`, `LCACost.rmqQueryCosted_cost`,
  `LCACost.rmqQueryCosted_run`,
  `LCACost.minDepthNodeInWindowIndexedCosted_erase`,
  `LCACost.minDepthNodeInWindowIndexedCosted_value`,
  `LCACost.minDepthNodeInWindowIndexedCosted_cost`,
  `LCACost.minDepthNodeInWindowIndexedCost_of_valid`,
  `LCACost.minDepthNodeInWindowIndexedCost_le`,
  `LCACost.minDepthNodeInWindowIndexedCosted_run`,
  `LCACost.traceQueryViaRMQIndexedCosted_erase`,
  `LCACost.traceQueryViaRMQIndexedCosted_value`,
  `LCACost.traceQueryViaRMQIndexedCosted_cost`,
  `LCACost.traceQueryViaRMQIndexedCosted_cost_of_firstOccurrences`,
  `LCACost.traceQueryViaRMQIndexedCost_le`,
  `LCACost.traceQueryViaRMQIndexedCosted_cost_le`,
  `LCACost.traceQueryViaRMQIndexedCosted_run`,
  `LCACost.queryViaRMQIndexedCosted_erase`,
  `LCACost.queryViaRMQIndexedCosted_cost`,
  `LCACost.queryViaRMQIndexedCosted_cost_of_firstOccurrences`,
  `LCACost.queryViaRMQIndexedCost_le`,
  `LCACost.queryViaRMQIndexedCosted_cost_le`,
  `LCACost.queryViaRMQIndexedCosted_run`,
  `LCACost.queryViaEulerParensRMQIndexedCosted_erase`,
  `LCACost.queryViaEulerParensRMQIndexedCosted_cost`,
  `LCACost.queryViaEulerParensRMQIndexedCosted_cost_of_firstOccurrences`,
  `LCACost.queryViaEulerParensRMQIndexedCosted_run`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_erase`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_value`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_cost`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_cost_of_firstOccurrences`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCost_le`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_cost_le`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_cost_le_four`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_run`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_tracePathAgreement`,
  `LCACost.queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_labelsUnique`.
- `RMQ/Impl/LCAFischerHeun.lean` (47):
  `LCAFischerHeun.canonicalCandidate_eq_queryBuilt`,
  `LCAFischerHeun.allInputCandidate_eq_queryBuilt`,
  `LCAFischerHeun.canonicalCandidate_isPathLCA_of_tracePathAgreement`,
  `LCAFischerHeun.canonicalCandidate_isPathLCA_of_labelsUnique`,
  `LCAFischerHeun.allInputCandidate_isPathLCA_of_tracePathAgreement`,
  `LCAFischerHeun.allInputCandidate_isPathLCA_of_labelsUnique`,
  `LCAFischerHeun.canonicalRMQBackend_queryBuilt`,
  `LCAFischerHeun.fischerHeunQueryCosted_cost_le_thirteen_of_large`,
  `LCAFischerHeun.canonicalMinDepthNodeCosted_erase`,
  `LCAFischerHeun.canonicalMinDepthNodeCosted_value`,
  `LCAFischerHeun.canonicalMinDepthNodeCosted_cost_le_fourteen_of_large`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_erase`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_value`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_cost_le_sixteen_of_firstOccurrences`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_cost_le_sixteen_of_large`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_refines_with_steps_of_tracePathAgreement`,
  `LCAFischerHeun.canonicalConcreteQueryCosted_run`,
  `LCAFischerHeun.buildDenseConcreteQueryState_rmqState`,
  `LCAFischerHeun.buildDenseConcreteQueryState_firstOccurrences`,
  `LCAFischerHeun.buildDenseConcreteQueryState_nodes`,
  `LCAFischerHeun.stateMinDepthNodeCosted_denseBuilt_eq`,
  `LCAFischerHeun.stateFirstOccurrenceCosted_denseBuilt_eq`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_eq`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_value`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_cost_le_sixteen_of_large`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_tracePathAgreement`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels`,
  `LCAFischerHeun.firstOccurrenceBuildAndDenseQuery_refines_with_steps_of_denseNatLabels`,
  `LCAFischerHeun.fischerHeunBuildCosted_cost_le_fifteen_mul_depths`,
  `LCAFischerHeun.densePreprocessBuildCost_le_budget`,
  `LCAFischerHeun.densePreprocessBuildBudget_le_linearBudget`,
  `LCAFischerHeun.densePreprocessBuildCost_le_linearBudget`,
  `LCAFischerHeun.densePreprocessAndQuery_refines_with_steps_of_denseNatLabels`,
  `LCAFischerHeun.denseLCA_linearBuild_constantQuery_profile`,
  `LCAFischerHeun.queryWithBuiltDenseConcreteStateCosted_run`,
  `LCAFischerHeun.canonicalQueryCosted_erase`,
  `LCAFischerHeun.canonicalQueryCosted_cost`,
  `LCAFischerHeun.canonicalQueryCosted_cost_of_firstOccurrences`,
  `LCAFischerHeun.canonicalQueryCosted_cost_le`,
  `LCAFischerHeun.canonicalQueryCosted_cost_le_four`,
  `LCAFischerHeun.canonicalQueryCosted_run`,
  `LCAFischerHeun.allInputQueryCosted_erase`,
  `LCAFischerHeun.allInputQueryCosted_cost`,
  `LCAFischerHeun.allInputQueryCosted_cost_of_firstOccurrences`,
  `LCAFischerHeun.allInputQueryCosted_cost_le`,
  `LCAFischerHeun.allInputQueryCosted_cost_le_four`,
  `LCAFischerHeun.allInputQueryCosted_run`.
- `RMQ/Impl/FischerHeunCost.lean` (32):
  `rawShapeTableCount_eq_shapeCount`,
  `rawMicrotableSlotBudget_eq_shapeCount_mul`,
  `rawMicrotableSlotBudget_le_of_local_slots_le_shape_count`,
  `rawLookupCosted_cost_le_bound`, `rawMicrotable_cost_count_profile`,
  `rawShapeTableCount_le_envelope`, `rawShapeTableCount_le_shapeCountEnvelope`,
  `rawShapeTableCount_square_le_of_envelope_square`,
  `rawShapeTableCount_square_le_of_envelope_budget`,
  `shapeCountEnvelope_eq_two_pow_two_mul`,
  `shapeCountEnvelope_square_eq_two_pow_four_mul`,
  `shapeCountEnvelope_square_le_of_four_mul_le_log2`,
  `rawShapeTableCount_square_le_of_four_mul_le_log2`,
  `canonicalBlockSize_four_mul_le_log2`,
  `localQuerySlotBudget_le_shapeCountEnvelope`,
  `rawMicrotableSlotBudget_le_shapeCountEnvelope_square`,
  `rawMicrotableSlotBudget_le_length_of_four_mul_le_log2`,
  `rawMicrotableSlotBudget_canonical_le_length`,
  `summaryLog_canonical_le_four_mul`,
  `canonicalBlockSize_pos_length_of_ge_sixteen`,
  `blockMinSummary_length_mul_le_length`, `blockMinSummary_length_le_length`,
  `summarySparseBuildCost_le_thirteen_mul_length`,
  `suppliedQueryCost_le_thirteen`,
  `buildCost_le_fifteen_mul_length`,
  `buildCost_le_fifteen_mul_length_of_shape_budget`,
  `buildCost_linear_under_budget`, `suppliedQueryCost_constant`,
  `linearBuild_constantQuery_profile`,
  `linearBuild_constantQuery_profile_of_shape_budget`,
  `linearBuild_constantQuery_profile_canonical`.
- `RMQ/Impl/FischerHeun.lean` (101): `paddedInput_length`,
  `paddedInput_get?_eq`, `storedBlockSignatures_get?_of_lt`,
  `microtableSlotReadCosted_value`, `microtableSlotReadCosted_cost`,
  `StoredMicrotableView.queryOffsetCosted_value_of_get`,
  `StoredMicrotableView.queryOffsetCosted_cost`,
  `StoredMicrotableView.queryIndexCosted_value_of_get`,
  `StoredMicrotableView.queryIndexCosted_cost`,
  `storedMicrotableForInputWith_queryIndexCosted_value_of_lt`,
  `storedMicrotableForInputWith_queryIndexCosted_cost`,
  `storedMicrotableForInput_queryIndexCosted_value_of_lt`,
  `storedMicrotableForInput_queryIndexCosted_cost`,
  `storedLocalBlockCandidateCosted_value_of_lt`,
  `storedLocalBlockCandidateCosted_cost`,
  `storedExactBlockSignatures_get?_of_lt`,
  `storedMicrotableForExactInputWith_queryIndexCosted_value_of_lt`,
  `storedMicrotableForExactInputWith_queryIndexCosted_cost`,
  `storedFullBlockCandidateCosted_value_of_lt`,
  `storedFullBlockCandidateCosted_cost`,
  `storedStateLocalBlockCandidateCosted_value_of_lt`,
  `storedStateLocalBlockCandidateCosted_cost`,
  `leftmostArgMin_of_eq_on_range`,
  `microQueryIndex_valid_exact`, `localBlockCandidate_exact`,
  `rightBoundaryCandidate_exact`, `buildWithBlockSize_blockSize`,
  `buildWithBlockSize_summary`, `buildWithBlockSize_summaryTable`,
  `buildWithBlockSize_microtable`, `tickEachCosted_cost`,
  `microtableSlotTokens_length`, `microtableShapeRowBuildCosted_cost`,
  `microtableRowsBuildCostedFrom_cost`, `microtableRowsBuildCosted_cost`,
  `microtableBuildCosted_value`,
  `microtableBuildCosted_cost`, `buildWithBlockSizeCosted_value`,
  `buildWithBlockSizeCosted_cost`, `buildWithBlockSizeCosted_run`,
  `buildCosted_value`, `buildCosted_cost`, `buildCosted_run`,
  `localBlockCandidateCost_le_two`,
  `rightBoundaryCandidateCosted_value_of_lt`,
  `rightBoundaryCandidateCosted_cost`,
  `rightBoundaryCandidateCost_le_two`,
  `queryWithStateCosted_cost`,
  `queryWithStateCost_le_thirteen_of_blockSize_pos`,
  `queryWithStateCosted_cost_le_thirteen_of_blockSize_pos`,
  `queryWithStateCost_le_suppliedQueryCost_of_stored`,
  `queryWithStateCosted_cost_le_suppliedQueryCost_of_stored`,
  `queryWithStateCosted_value_built`, `queryWithStateCosted_run_built`,
  `queryWithBlockSizeCosted_value`, `queryWithBlockSizeCosted_run`,
  `queryCosted_value`, `queryCosted_run`,
  `queryWithBlockSizeFreshCosted_value`,
  `queryWithBlockSizeFreshCosted_cost`, `queryWithBlockSizeFreshCosted_run`,
  `freshQueryCosted_value`, `freshQueryCosted_cost`, `freshQueryCosted_run`,
  `queryWithState_valid_exact`, `queryWithState_sound`,
  `queryWithState_complete`, `queryWithState_invalid_none`, `query_sound`,
  `query_complete`, `invalid_none`, `allInputQuery_large`,
  `allInputQuery_small`, `allInputQueryCosted_value`,
  `allInputQueryCosted_cost`, `allInputQueryCosted_run`,
  `allInputQueryCost_large`, `allInputQueryCost_small`,
  `allInputQueryCost_le_build_plus_supplied_of_large_stored`,
  `allInputQueryCosted_cost_le_build_plus_supplied_of_large_stored`,
  `queryWithStateCost_built_le_thirteen_of_large`,
  `queryWithStateCosted_built_cost_le_thirteen_of_large`,
  `fischerHeun_refines_with_steps`,
  `fischerHeun_fresh_refines_with_build_query_steps_of_large`,
  `allInputQueryCost_large_le_build_plus_thirteen`,
  `allInputQueryCosted_cost_large_le_build_plus_thirteen`,
  `linearBuild_constantQuery_profile_allInput_large`,
  `allInputQuery_sound`, `allInputQuery_complete`,
  `allInputQuery_valid_exact`, `allInputQuery_invalid_none`,
  `two_mul_sub_log_slack_le_bits_of_stateEncoding`,
  `exactRMQ_two_sided_log_slack_space_bound_stateEncoding`.
- `RMQ/Impl/Equivalence.lean` (17): `linearScan_query_eq_sparseTable_query`,
  `sparseTable_query_eq_memoSparseTable_query`,
  `linearScan_query_eq_memoSparseTable_query`,
  `linearScan_query_eq_hybridBlock_query`,
  `linearScan_query_eq_recursiveHybrid_query`,
  `linearScan_query_eq_microtableRaw_query`,
  `linearScan_query_eq_fischerHeun_query`,
  `linearScan_query_eq_fischerHeun_allInputQuery`,
  `fischerHeun_query_eq_allInputQuery`,
  `sparseTable_query_eq_hybridBlock_query`,
  `sparseTable_query_eq_recursiveHybrid_query`,
  `sparseTable_query_eq_microtableRaw_query`,
  `sparseTable_query_eq_fischerHeun_query`,
  `hybridBlock_query_eq_recursiveHybrid_query`,
  `recursiveHybrid_query_eq_hybridBlock_query`,
  `recursiveHybrid_query_eq_fischerHeun_query`,
  `fischerHeun_query_eq_recursiveHybrid_query`.

## Private Helper Theorem Inventory

These are intentionally non-API helpers, but they are listed here for audit
completeness.

- `RMQ/Core/Window.lean`: `get?_some_of_lt`.
- `RMQ/Core/Shape.lean`: `sum_map_const_nat`, `get?_addConst`,
  `leftmostArgMin_append_zero_of_positive`,
  `scanWindow_append_zero_of_positive`, `fin_succ_inj`, `nodup_ofFn`,
  `finRange_nodup`, `boolLists_length`, `mem_boolLists_of_length`,
  `decodeFullCodeFuel_fullCode_append`, `mem_erase_of_ne_of_mem`,
  `length_le_of_nodup_injective_into`, `nodup_map_node_left`,
  `mem_nodeProducts`, `nodup_nodeProducts`,
  `nodup_flatMap_of_nodup_disjoint`, `mem_splitShapeProducts`,
  `splitShapeProducts_nodup`, `fullCode_eq_of_tail_eq_of_pos`.
- `RMQ/Core/EncodingLowerBound.lean`: `sum_map_const_nat`,
  `mem_erase_of_ne_of_mem`, `rightSpine`, `rightSpine_shapeOfSize`,
  `shapeOfSize_size`, `two_pow_sub_le_of_le_mul_pow`,
  `remyPositions_length`, `remyLeaves_length`, `remyInsert_size`,
  `remyNewLeaf_mem`, `remyRemoveMarkedLeaf_insert`,
  `nodup_map_injective`, `nodup_flatMap_of_nodup_disjoint`,
  `remyPositions_nodup`, `sum_map_eq_const_nat`,
  `remyInputFiber_length`, `remyInputList_length`,
  `markedLeafCodes_length`, `remyInputPair_nodup`,
  `remyInputPair_mem_path`, `remyInputFiber_mem_shape`,
  `remyInputFiber_mem_path`, `remyInputFiber_nodup`,
  `remyInputList_nodup`, `remyInputList_mem_shape`,
  `remyInputList_mem_path`, `remyEncodeInput_mem_markedLeafCodes`,
  `remyEncodeInput_injective_on`, `remyRatio_lower`,
  `remyStep_arith`, `two_pow_two_mul_succ`, `remyStep_count_bound`.
- `RMQ/Impl/SparseTable.lean`: `get?_some_of_lt`, `betterIndex_self`,
  `leftmost_singleton`, `sparseRow_get?_eq_blockArgMin`, `log2_block_bounds`.
- `RMQ/Impl/HybridBlock.lean`: `chunkRow_get?_eq_chunkCell`,
  `log2_chunk_bounds`.
- `RMQ/Impl/FischerHeunCost.lean`: `nat_le_two_pow`,
  `nat_succ_le_two_pow`, `log2_le_of_lt_pow_succ`,
  `div_lt_pow_of_lt_pow_add_four`.

## Suggested Next Milestones

1. Add a real packed plus-minus-one RMQ query structure over the generated
   Euler-parentheses input, then plug it into `Core.SuccinctReduction` and the
   Euler-parens `LCACost` wrapper.
2. Refine the packed succinct model with table-size budgets and optional
   broadword-layout parameters, without changing the exact rank/select API.
3. Tighten the stored-table trace model so the sparse summary query has an
   exact interpreter-style cost equation, not only a `steps <= 7` upper bound.
4. Port the dense LCA Euler-trace construction from the older tick model onto
   `Core.RAM` primitives and package the full preprocessing pipeline as one
   executable trace, if the project wants interpreter-level cost fidelity.
5. Promote the `RMQHub` import/build boundary into a physical package split
   only after the next spoke needs it.
