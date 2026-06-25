# RMQ Roadmap - Hub-and-Spoke Proof of Concept

## Mission and positioning

This repo is spoke #1, and the proof of concept, for a larger hub-and-spoke
library of frontier-grade formalized advanced data structures. RMQ is the
instantiation that proves the pattern; the reusable parts under `Core/` are the
hub that future spokes should share.

Two properties guide the work:

1. Independently research-grade. A formal-methods or algorithms researcher
   should find the code modular, non-vacuous, and focused on facts one actually
   relies on: correctness, cost, representation refinement, and lower bounds.
2. CSLib-compatible / portable. Modules should be shaped so they can be lifted
   into, or upstreamed toward, Lean's Computer Science Library ecosystem where
   that makes sense.

The gap this repo is meant to fill:

- CSLib has broad DS&A coverage and a manual-tick `TimeM` style, but not a
  derived RAM/query model or lower-bound framework.
- Isabelle/AFP has strong amortized functional data structures and randomized
  BST work.
- Coq has mature pockets around union-find, succinct rank/select/LOUDS, and
  approximate membership.
- No extant formalization appears to own RMQ / Fischer-Heun, data-structure
  encoding or cell-probe lower bounds, and a derived machine-step model in one
  connected story.

Our differentiators are exactly those gaps: a cost story where steps are derived
from an operational model rather than handwritten, reusable data-structure lower
bounds, and frontier structures that breadth libraries usually skip. Later
spokes should be chosen from the intersection of CS166 content, the literature,
and formalization gaps.

## How to use this file

- "Done" means the stated theorem typechecks `sorry`-free with the standard Lean
  trust base only. The build gate enforces soundness; this file enforces value.
- For the landed `2*n + o(n), O(1)` succinct RMQ finish line, read
  `docs/SUCCINCT_FINAL_PATH.md` for current status plus historical stop-audit
  guardrails. It is no longer an active missing-component contract.
- For the research-backed construction choices behind that finish line, read
  `docs/SUCCINCT_RESEARCH_AND_PLAN.md`. It records the C1/C2/C3 design path
  and the false starts that should not be reintroduced.
- Materialize a target as a compiled theorem only once its supporting
  definitions exist. Until then, keep it as prose plus the intended theorem
  shape.
- Anti-vacuity rule: targets must reference principled constructions, such as
  an interpreter or an actual encoder. A degenerate witness like `steps := 0`
  must not satisfy the statement.
- One autonomous run should aim at one full target and may chain only while the
  gate stays green. When a target closes, update `docs/FAMILY_SUMMARY.md` and
  add the new headline theorem to `scripts/axiom_check.lean`.

## Finish line

The RMQ proof-of-concept is done when A + B + C + one of D are done. This is the
bounded finish line: A/B/C re-found the current RMQ results on reusable hub
infrastructure, and D lands the extra research headline.

Current status: the proof-of-concept finish line is landed. D-LCA is the
dense-label LCA cost headline, and D-Space is now also landed as the BP-native
succinct RMQ capstone. The total public two-sided capstone is
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`.
The remaining roadmap items are post-POC hardening: a full first-order RAM
interpreter if a later target needs it, further CSLib-style extraction, an
optional flatter encoded/payload-only presentation of the succinct theorem, and
the next data-structure spoke.

Dependency order: A -> B -> (C, D). C can progress in parallel with A/B when it
is pure extraction/generalization. D-LCA depends on the A/B cost/refinement
story if it is claimed as an end-to-end time theorem.

## A - Machine-Step Cost Model

Hub target: `Core/Cost/RAM`

Status: POC complete as a hardened shallow RAM model; full interpreter future.

Intent: make "O(1)" and "O(n)" theorems about counted machine steps rather than
theorems about author-supplied ticks.

Current status:

- `Core.RAM` provides a trace-based execution substrate.
- `RAM.Exec`'s constructor and raw one-step primitive are sealed; clients build
  traces through typed value-computing primitives such as `branch`,
  `readArray?`, `compareLtInt`, `allocArray`, and `pushArray`.
- `Impl.SparseTableInstrumented` derives trace bounds for sparse-table build
  and query pieces, including the memoized build path.
- Sparse-table row construction now builds Arrays directly and charges one
  counted `pushArray` per produced row cell.
- The stored sparse-table query uses `Array.size` in its validity guard, so the
  advertised constant query trace no longer hides an `xs.toList.length` scan.
- `memoQueryWithTracedBuild_refine_with_steps` ties memoized sparse build plus
  query back to the verified List backend with a derived build budget plus a
  small query bound.
- Fischer-Heun now routes the live supplied-state query through stored local
  microtable reads: exact-input signatures for the left full block and
  padded-input signatures for the right/same-block local candidates. The
  positive-block supplied-query budget is now the honest stored signature/slot
  bound `<= 13`.

Gap:

- The shallow trace monad is disciplined but not interpreter-level: `Exec.pure`
  can still return arbitrary already-computed values. Future lower-bound-grade
  machine modeling should add a first-order interpreter.
- Some value-level plumbing remains intentionally outside the current trace
  model, especially outer table assembly and reference-side List erasure used
  for proofs.
- Fischer-Heun's summary sparse-table leg is traced and the local microtable
  reads now go through stored signature/slot adapters, but the whole assembled
  FH build/query is still not a single derived `RAM.Exec` program.

Landed theorem shape:

```lean
theorem SparseTable.Instrumented.memoBuild_and_query_refine_with_steps :
  ...

theorem fischerHeun_refines_with_steps :
  (FischerHeun.queryCosted xs left right).value =
      FischerHeun.query xs left right /\
    (FischerHeun.queryCosted xs left right).cost <= 13
```

Here `Steps` must be the trace length of programs built only through the
hardened primitive API. A full first-order `eval : Prog -> Value * Steps`
interpreter is stronger and remains a good future target for machine-model
lower bounds, but it is not required for this proof-of-concept upper-bound
milestone.

Debt reduced: turns the current trace-count caveat into a real machine-step
claim, and gives future spokes a reusable cost foundation.

## B - Refinement Framework and At Least Two Instances

Hub target: `Core/Refine`

Status: POC complete; future work is framework polish.

Intent: expose the standard reference-vs-executable pattern researchers expect:
a List-level verified reference object, an Array/RAM representation, and a
proved erasure/refinement relation used by the costed implementation.

Current status:

- `Core.Refine.StoredMatrix` is the current seed of this interface.
- `StoredMatrix.row?`, `absRow?`, `cell?`, and `absCell?` now provide a
  reusable row/cell erasure boundary for Array-backed matrix representations;
  default-row/default-cell lemmas package the common missing-row/missing-cell
  convention used by sparse tables.
- `SparseTable.Instrumented.queryFromStoredTable_value` and
  `SparseTable.Instrumented.queryFromStoredTable_steps_le_seven` package the
  sparse-table stored query through that interface.
- `SparseTable.Instrumented.tableRowArray_value_toList_of_stored` consumes the
  generic stored-row theorem instead of reproving row erasure from raw arrays.
- Fischer-Heun `State` now carries both the List summary table and a
  `StoredMatrix` Array representation of it.
- Fischer-Heun's supplied-state costed query routes the summary sparse-table
  leg through the stored traced adapter.
- Fischer-Heun now exposes the stored summary-table boundary explicitly:
  `SummaryTableRefines`, `summaryStoredQuery_value_of_refines`,
  `summaryStoredQuery_steps_le_seven`, and
  `liftedSummaryStoredQuery_refines_recursiveMiddle_with_steps` show that the
  FH middle leg is the second concrete consumer of the shared stored-matrix
  refinement certificate.
- `FischerHeun.summaryTableStore_cell_eq_summaryTable` makes the FH summary
  table a direct consumer of the generic stored-cell theorem.
- `FischerHeun.fischerHeun_refines_with_steps` bundles the public costed query's
  value refinement with the large-regime `<= 13` stored-query bound.
- The old asserted sparse-table supplied-table cost adapter was retired rather
  than kept beside the derived path.

Gap:

- This is not yet a full reusable refinement framework. `StoredMatrix` has
  reusable row/cell erasure, but build/query adapters are still algorithm
  specific and naming has not yet been hardened for CSLib-style extraction.
- Fischer-Heun's stored local microtable charges are explicit two-read
  `TableModel` accesses rather than `StoredMatrix` rows. That is a fair model
  boundary for this RMQ proof-of-concept; a future extraction pass can decide
  whether shape/query-slot tables should also be packaged as a matrix-like hub
  interface.

Done theorem shape:

```lean
theorem fischerHeun_refines_with_steps :
  (FischerHeun.queryCosted xs left right).value =
      FischerHeun.query xs left right /\
    (FischerHeun.queryCosted xs left right).cost <= 13
```

Anti-vacuity: there must be at least two real instances, such as sparse table
and Fischer-Heun summary table, using the same interface rather than bespoke
proofs.

Debt reduced: moves from one-off Array adapters toward a portable refinement
framework and keeps the asserted-cost count trending down.

## C - Lower-Bound Framework and RMQ Instance

Hub target: `Core/LowerBound`

Status: complete extraction in place.

Intent: lift the RMQ lower bound into reusable encoding/capacity infrastructure.
This is the rare part of the project: a data-structure lower-bound framework
that future spokes can instantiate.

Current status:

- `Core.EncodingLowerBound` proves the no-premise RMQ bit lower bound
  `2n - (2 * log2 (2n + 1) + 2)` using a verified Remy-style counting argument,
  and now also proves the coefficient-correct doubled integer form
  `4*n - (3*log2(2*n+1)+3) <= 2*bits`.
- The theorem is non-vacuous: a decoder must answer from the bitstring alone.
- `Core.LowerBound` now provides the generic finite bitstring universe,
  finite-domain `LosslessEncoding`, injection/capacity counting theorem,
  generic logarithmic-slack arithmetic bridge, and squared-count doubled-bit
  bridge. `Core.EncodingLowerBound` instantiates that layer for Cartesian
  shapes and routes the shape-capacity, log-slack, and doubled Catalan
  lower-bound steps through it.

Gap:

- The exact RMQ decoder/state-encoding adapters are still RMQ-specific, as they
  should be, but the naming split can be polished further into a dedicated
  `RMQ.LowerBound` client module if the project later separates reusable hub
  code from the RMQ spoke.
- The Remy/Catalan counting proof remains in `Core.EncodingLowerBound` because
  it is Cartesian-shape-specific.

Done theorem shape: a generic lower-bound API plus an RMQ module that
re-derives the existing `2n - O(log n)` theorem and the coefficient-correct
doubled Catalan slack theorem through that API.

Anti-vacuity: the generic layer must be usable by another future problem in
principle. Do not hide RMQ-specific shape facts in `Core`.

Debt reduced: turns a one-off crown-jewel theorem into reusable infrastructure.

## D - One Research Headline

Pick exactly one for the proof-of-concept finish line. Do not require both.

### D-LCA - Unified O(n)/O(1) LCA

Recommended target.

Status: POC complete with dense/preindexed normalized component profile.

Current status:

- `LCAFischerHeun` and `SuccinctReduction` prove the RMQ-to-LCA correctness
  story, including `IsPathLCA`-level statements.
- The current concrete query path has a large-regime constant bound over Euler
  depths. `canonicalConcreteQueryCosted_cost_le_sixteen_of_large` is now a
  uniform `<= 16` theorem with no supplied first-occurrence hypotheses.
- `canonicalConcreteQueryCosted_refines_with_steps_of_tracePathAgreement`
  bundles query-side path-LCA soundness with that `<= 16` bound.
- `ConcreteQueryState` bundles the Fischer-Heun RMQ state over Euler depths,
  first-occurrence access, and the Euler-node indexed view.  The only
  cost-headline instance is the dense state below.
- `RoseTree.LabelsBoundedBySize` and `RoseTree.DenseNatLabels` now name the
  dense/preindexed node-ID regime separately from arbitrary-label correctness.
  `LCACost.firstOccurrenceDirectRows` / `firstOccurrenceDirectIndex` give a
  direct-address first-occurrence table, and
  `queryWithBuiltDenseConcreteStateCosted_refines_with_steps_of_denseNatLabels`
  proves the dense built-query state returns only path-LCA answers with the same
  `<= 16` large-regime query bound.
- `LCACost.buildFirstOccurrenceDirectArray_refines_with_steps` gives the dense
  first-occurrence table a counted RAM builder: it erases to the direct-address
  rows and costs at most
  `labelsPreorder.length + 1 + 3 * eulerTrace.nodes.length` steps.
  `firstOccurrenceBuildAndDenseQuery_refines_with_steps_of_denseNatLabels`
  composes that builder with the dense query capstone.
- `Core.RAM.arrayOfList_refines_with_steps` is now the generic counted
  `List -> Array` materializer.  `LCACost.buildNodeArray_refines_with_steps`
  and `LCACost.buildDepthArray_refines_with_steps` instantiate it for Euler
  node/depth views, and `buildDenseConcreteQueryState` consumes the built node
  view.
- `densePreprocessAndQuery_refines_with_steps_of_denseNatLabels` composes the
  current dense preprocessing components: Euler trace construction in the
  existing tick model, counted node/depth stored views, counted dense
  first-occurrence construction, Fischer-Heun RMQ-state build, and the constant
  `<= 16` dense LCA query bound.
- `denseLCA_linearBuild_constantQuery_profile` is the public-facing capstone:
  under `DenseNatLabels` and canonical large-regime Euler depths, assembled
  dense preprocessing costs at most `22 * eulerTrace.nodes.length + 3`, query
  cost is at most `16`, returned nodes are path-LCA answers, and the combined
  build-plus-query cost is bounded by the linear budget plus `16`.

Gap:

- The dense LCA preprocessing theorem is an assembled component-budget theorem,
  not yet one monolithic `RAM.Exec` program.  A future polish pass can port the
  Euler-trace construction from the older tick model to the RAM trace model and
  package the whole pipeline as a single executable trace.
- The earlier arbitrary-label association-list first-occurrence path has been
  retired from source.  The O(1) query implementation story is the
  dense/preindexed path.

Landed theorem shape:

```lean
theorem denseLCA_linearBuild_constantQuery_profile :
  densePreprocessBuildCost tree <= densePreprocessLinearBudget tree /\
  (forall {node}, query.value = some node -> tree.IsPathLCA u v node) /\
  query.cost <= 16 /\
  densePreprocessBuildCost tree + query.cost <=
    densePreprocessLinearBudget tree + 16
```

Anti-vacuity: the query bound must consume the table built by the preprocessing
algorithm. It may not assume `_of_firstOccurrences`-style inputs for free.

### D-Space - Tight Succinct Space Bound

Alternative target.

Status: landed. The first fixed-length sandwich, BP-native theorem shape,
concrete relative-split false-close/select access family, compact BP
close/LCA directory, and final `2*n + o(n), O(1)` BP-native RMQ capstone all
typecheck.

Intent: pair C's lower bound with a concrete `<= 2n + o(n)` encoder whose query
procedure is proved exact, giving a two-sided `2n +/- Theta(log n)` space story.

Current status:

- `EncodingLowerBound.ExactRMQSpaceBounds` packages a universal lower side plus
  a concrete exact upper encoder.
- `canonicalRepresentativeSpaceBounds` and
  `exactRMQ_two_sided_log_slack_space_bound` give a non-vacuous fixed-length
  sandwich: every exact payload decoder needs
  `2*n - (2*log2(2*n+1)+2)` bits, and the canonical representative decoder
  answers RMQ queries exactly from a `2*n`-bit shape payload. The lower-bound
  API also exposes the sharper doubled integer Catalan slack
  `4*n - (3*log2(2*n+1)+3) <= 2*bits`, without claiming a separate rational
  theorem.
- `FischerHeun.stateEncodingSpaceBounds` and
  `exactRMQ_two_sided_log_slack_space_bound_stateEncoding` instantiate the same
  sandwich with a Fischer-Heun-shaped proof-only state and the same charged
  `2*n` payload.

Anti-vacuity: the upper side must remain a concrete encoder with proved exact
queries, not a bare existential. Those first-stage fixed-length `2*n` witnesses
are valid exact upper bounds, but by themselves they were not yet a packed
constant-time succinct RMQ query structure; the landed BP-native capstone below
is the packed constant-query upper side.

Next refinement: package an even flatter encoded/payload-only view of the same
BP-native capstone, or move to a stronger first-order RAM interpreter if a
future target needs that level of anti-vacuity.

## E - Post-POC Next Phase

### E1 - Tight RMQ Space Sandwich

Status: tight fixed-length payload-space capstone landed, the sharpened
coefficient-correct doubled Catalan slack is packaged, and the packed
`2n + o(n)` query structure now has a concrete total two-sided BP-native theorem
through the relative-split false-close/select access family and compact
close/LCA directory.

The detailed bullets below retain the construction history. Any older phrasing
about open sampled navigation, descriptor, or compact-interior checkpoints is
superseded by the final capstone theorem unless it is explicitly marked as
future presentation or model-strengthening work.

The first-stage theorem
`EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound` packages
the fixed-length exact-RMQ payload-space sandwich: every exact state decoder
needs `logSlackLower n = 2*n - (2*log2(2*n+1)+2)` bits, every uniform charged
payload budget satisfies the same lower bound, and the canonical representative
decoder charges exactly `2*n` bits on every shape. The same lower-bound layer
now also provides `doubledLogSlackLower n = 4*n - (3*log2(2*n+1)+3)` with
charged-payload and uniform-budget conclusions of the form
`doubledLogSlackLower n <= 2 * ...`. The public upper/lower join is
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`,
which pairs this doubled lower slack with the total `2*n + o(n)`, constant-query
BP-native upper structure. The older
`EncodingLowerBound.exactRMQ_two_sided_log_slack_space_bound` theorem and the
implementation-shaped companion
`FischerHeun.exactRMQ_two_sided_log_slack_space_bound_stateEncoding` remain as
coarser existential/state-shaped views.

The following E1 bullets preserve historical target layering. Active RMQ
capstone obligations are discharged by the `SuccinctFinal` theorem above; the
items below explain how the project reached that theorem and which pieces are
still useful as reusable scaffolding.

Historical model layers:

- `Succinct.PackedPlusMinusOneRMQ` packages counted signature payload bits, a
  packed bitvector view, and a fixed exact signature-table decoder.
- `Succinct.PackedPlusMinusOneRMQ.queryBuilt_sound`,
  `queryBuilt_complete` prove exact supplied PM1 queries through the fixed
  table model. The old raw `queryCosted_cost` wrapper has been retired; it was
  not a faithful stored-directory query.
- `Succinct.packedEulerParensBackend` and
  `Succinct.packedEulerParensLCACandidate_isPathLCA_of_labelsUnique` connect
  that concrete packed PM1 model to generated Euler-parentheses LCA.
- `Succinct.packedEulerParensRMQ_space_profile` records the packed PM1
  component's exact payload size: one bit per Euler move, equivalently one less
  than the generated Euler-trace node length.
- `LCACost.queryViaPackedEulerParensRMQIndexedCosted_refines_with_steps_of_labelsUnique`
  specializes the indexed LCA-via-RMQ cost path to this packed PM1 backend:
  unique labels give path-LCA soundness and the query costs at most four
  modeled reads.
- `SuccinctSpace.BroadwordRMQDirectory` is the anti-vacuous interface for the
  final word-RAM upper-bound layer: a canonical `2*n` shape payload, counted
  auxiliary payload bits, a costed payload-only query decoder, and exact
  refinement to the representative RMQ answer.
- `SuccinctSpace.BroadwordSuccinctRMQFamily.two_n_plus_o_constant_query_profile`
  states the final theorem shape for any concrete directory family whose
  auxiliary overhead satisfies `LittleOLinear`: lower-bound-compatible
  payload budget `2*n + overhead n`, exact charged payload counts, constant
  query cost, and exact valid-query answers.
- `SuccinctSpace.LittleOLinear` now has scalar/additive/constant closure
  lemmas, so independently counted rank/select/excess/microtable components
  can be combined without redoing asymptotic arithmetic.
- `SuccinctSpace.RankSelectDirectory` and `RankSelectFamily` now expose a
  reusable rank/select component interface: counted auxiliary bits and exact
  rank/select erasure to `Core.Succinct`. The old raw packed family witnesses
  have been retired; the faithful path is through stored-word data and
  payload-backed directories.
- `SuccinctSpace.BalancedParensAccess` lifts that component to certified
  balanced-parentheses access, transporting prefix/final balance through
  costed rank calls and proving a two-rank `excessCosted` query bound.
- The BP access family is now instantiated by the payload-backed stored-word
  route rather than by raw packed aggregate wrappers.
- The old raw Euler-parentheses BP-access witness has been retired; generated
  Euler-tour parentheses now flow through the same stored-word/payload-backed
  component interfaces as the rest of the succinct model.
- `SuccinctSpace.BroadwordRMQDirectory.padToOverhead` pads an exact auxiliary
  encoding to a larger published budget while preserving the original query
  decoder and cost proof.
- `SuccinctSpace.ComponentizedBPRMQFamily.two_n_plus_o_constant_query_profile`
  specializes the family theorem to the expected BP directory split:
  rank, select, excess/RMQ navigation, and microtable/block metadata overheads.
- `SuccinctSpace.bpCode_balanced` and
  `bpParensOfShape_bits_length_of_shapeOfSize` prove that Cartesian shapes have
  a literal balanced-parentheses payload of length `2*n`; this is separate from
  the older full-code-tail payload used by the lower-bound decoder.
- `SuccinctSpace.bpCloseOfInorder?_rankFalse_succ` proves that closing
  parenthesis rank recovers the inorder index of a Cartesian node, the local
  bridge needed to turn BP/LCA answers back into RMQ offsets.
- `SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?` proves the matching
  select-side bridge: stored select for closing parentheses over `shape.bpCode`
  returns the inorder node close position.
- `SuccinctSpace.BalancedParensAccess.ofShapePayloadLiveStoredWordRankSelectData_close_profile`
  uses the payload-live stored-word rank/select component to discharge the
  close-select and close-rank legs with cost `<= 3`; at this historical layer
  the BP LCA-close primitive was still abstract in the close-navigation
  adapter.
- `SuccinctSpace.BPBroadwordRMQDirectory` is the BP-native counterpart to
  `BroadwordRMQDirectory`: the counted base payload is `shape.bpCode`, not the
  canonical decoder payload.
- `SuccinctSpace.BPCloseRMQNavigationDirectory.queryEncodedCosted_exact`
  proves the select-close, LCA-close, rank-close query choreography exact for
  RMQ over Cartesian-shape representatives.
- `SuccinctSpace.StoredBPCloseLCADirectory.profile` isolates the remaining
  LCA-close primitive as a one-read stored navigation table with exactness
  against BP close positions; `StoredBPCloseLCAFamily.constant_lca_close_profile`
  gives the family-level `LittleOLinear` wrapper for that component.
- `SuccinctSpace.BPCloseRMQNavigationFamily.two_n_plus_o_close_navigation_profile`
  gives the family-level `2*n + o(n)`, constant-query theorem shape once a
  concrete close-navigation primitive and `LittleOLinear` overhead are supplied.
- The old stored-answer-table RMQ families were retired: a single modeled read
  of a precomputed RMQ answer table is not the flagship succinct query model.

Correction adopted: do not present the raw packed `SuccinctSpace` profiles as
the final succinct structure. They are interface scaffolding plus reference
correctness facts. The final theorem should now instantiate the BP-native
directory path, not the old canonical full-code-tail path.

Faithful rebuild started:

- `RAM.rankBoolWordPrefix` is now a typed word-RAM primitive with a one-step
  trace and a bridge theorem to `Succinct.rankPrefix`.
- `RAM.selectBoolWord` is the matching typed word-RAM primitive for selecting
  an occurrence inside one stored word, with a bridge theorem to
  `Succinct.select`.
- `SuccinctSpace.StoredWordRankData.rankCosted_profile` proves a bounded rank
  query assembled from one stored sample read, one stored payload-word read,
  and one word-rank primitive, with cost `<= 3` and exact rank on valid
  positions.
- `SuccinctSpace.StoredWordRankData.rankCostedClamped_exact` turns that
  valid-position rank path into total rank by clamping positions to
  `bits.length`, using the proved saturation of `Succinct.rankPrefix`.
- `SuccinctSpace.FixedWidthNatTable.profile` and
  `SuccinctSpace.FixedWidthRankSampleTables.profile` add the first
  payload-live codec layer: fixed-width natural-number sample words are read
  from the counted payload itself, with one RAM read and exact erasure to the
  reference entries.
- `SuccinctSpace.FixedWidthNatTable.ofEncodedWords_profile`,
  `FixedWidthOptionNatTable.ofEncodedWords_profile`,
  `FixedWidthRankSampleTables.ofEncodedWords_profile`,
  `FixedWidthSelectSampleTable.ofEncodedWords_profile`, and
  `FixedWidthSelectSampleTables.ofEncodedWords_profile` add the reusable
  encoded-word constructor boundary: a later builder can emit explicit
  fixed-width payload words plus decode/width proofs and immediately obtain the
  counted table contract.
- `SuccinctSpace.bitsToNatLE_natToBitsLE_of_lt`,
  `bitsToOptionNatLE_optionNatToBitsLE_of_bound`, and
  `bitsToStoredWordSelectSample_optionToBits_of_bound` close the bounded-field
  codec layer: natural-number counters, optional close/LCA entries, and select
  locator triples now have concrete little-endian encoders with exact decoders
  under explicit field-width bounds. The corresponding `ofEntries_profile`
  constructors build counted fixed-width tables directly from bounded semantic
  entries.
- `SuccinctSpace.flattenPayloadWords_chunkPayloadWords`,
  `SuccinctSpace.chunkPayloadWords_word_length_le`,
  `SuccinctSpace.BoundedPayloadWordStore.ofChunks_word_length_le`, and
  `SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel_word_length_le`
  provide the bounded fixed-size payload-word constructors needed by the final
  broadword model. The sentinel-padding variant preserves the represented
  payload while giving exact-boundary rank queries a concrete empty word to
  read.
- `SuccinctSpace.PayloadLiveStoredWordRankData.profile` rebuilds rank on top of
  those payload-live sample tables plus a payload-word store for the underlying
  bitvector, proving total rank exactness and cost `<= 3` without arbitrary
  sample decoders.
- `SuccinctSpace.StoredWordSelectData.selectCosted_profile` proves the
  analogous faithful select path: one stored occurrence-locator read, one
  stored payload-word read, and one word-select primitive, with cost `<= 3`.
- `SuccinctSpace.FixedWidthSelectSampleTable.profile`,
  `SuccinctSpace.FixedWidthSelectSampleTables.profile`, and
  `SuccinctSpace.PayloadLiveStoredWordSelectData.profile` move select locators
  onto counted fixed-width payload words: a presence bit plus fixed-width
  `wordIndex`, `wordStart`, and `rankBefore` fields.
- `SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankSelectData_profile`
  combines the payload-live rank and payload-live select components into the
  reusable rank/select interface with the same `<= 3` query bound.
- `SuccinctSpace.PayloadLiveStoredWordRankSelectFamily.constant_query_profile`
  and `SuccinctSpace.PayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile`
  package that non-leaky rank/select boundary as reusable `o(n)` families for
  ordinary bitvectors and balanced parentheses.
- `SuccinctSpace.BalancedParensAccess.ofPayloadLiveStoredWordRankSelectData_profile`
  and
  `SuccinctSpace.BalancedParensAccess.ofShapePayloadLiveStoredWordRankSelectData_close_profile`
  lift that payload-live rank/select directory into balanced-parentheses access
  and the Cartesian close-select/rank-close bridge.
- `SuccinctSpace.RankSelectDirectory.ofPayloadLiveRankStoredSelectData_profile`
  exposes the migration hook for the final stack: rank is now payload-live,
  while select still uses the existing stored locator component.
- `SuccinctSpace.FixedWidthOptionNatTable.profile` and
  `SuccinctSpace.PayloadLiveBPCloseLCADirectory.profile` add the matching
  payload-live one-read boundary for BP close/LCA navigation: stored close
  answers are optional fixed-width natural numbers read from counted payload
  words.
- `SuccinctSpace.PayloadLiveBPCloseRMQNavigationDirectory.profile` composes the
  payload-live close-select, BP LCA-close, and close-rank legs for built
  Cartesian shapes, proving exact RMQ answers with derived query cost `<= 10`
  and payload length `2*n + rank + select + lca`.
- `SuccinctSpace.PayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`
  lifts that stateful built-query story to the `2*n + o(n)` family level.
- `SuccinctSpace.SampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`
  specializes that capstone to the canonical sampled-directory envelope
  `slots * (n / (log2 n + 1))` for rank, select, and BP LCA-close overhead.
- `SuccinctSpace.WordBoundedSampledPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_bounded_built_query_profile`
  adds the broadword discipline missing from the sampled stateful theorem:
  stored rank/select payload words are explicitly bounded by per-component word
  sizes, while retaining the `2*n + o(n)` and `<= 10` built-query profile.
- `SuccinctSpace.EncodedPayloadLiveBPCloseRMQNavigationView.toBPCloseRMQNavigationDirectory`
  is the payload-only bridge for the BP close-navigation path: encoded
  select-close, LCA-close, and close-rank functions refine the stateful
  payload-live directory only on built payloads, so the theorem does not hide a
  shape decoder in the query.
- `SuccinctSpace.SampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_sampled_encoded_query_profile`
  combines that encoded bridge with the canonical sampled-directory envelope,
  giving the final broadword-facing theorem target once concrete sampled
  rank/select/LCA-close builders are supplied.
- `SuccinctSpace.WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_word_bounded_encoded_query_profile`
  is now the strongest abstract target: sampled `2*n + o(n)` payload-only
  encoded queries together with bounded rank/select payload-word accounting in
  one reusable wrapper.
- `SuccinctRankProposal.SampledPayloadLiveStoredWordRankFamily.bounded_constant_query_profile`
  isolates the rank-side builder target: produce payload-live rank sample data
  whose auxiliary payload is bounded by the sampled-directory envelope, and the
  existing counted rank path immediately gives cost `<= 3` and exact erasure
  to `Succinct.rankPrefix`.
- `SuccinctRankProposal.rankSampleEntries_getOpt_exact` starts the concrete
  sampled-rank builder side: word-boundary sample lists return exactly the
  corresponding `Succinct.rankPrefix` value.
- The single-level sampled-rank target is now explicitly caveated: with
  full-width samples, `o(n)` overhead and exact rank force a larger-than-word
  payload block unless the model treats `wordRank` over super-logarithmic words
  as a primitive. The researcher-respectable target is the classic two-level
  directory.
- `SuccinctRankProposal.TwoLevelPayloadLiveStoredWordRankFamily.constant_query_profile`
  adds that target interface: separate superblock/block payload accounting,
  `o(n)` combined overhead, exact rank through counted supertable,
  block-table, payload-word, and word-rank reads, and every payload word
  bounded by the modeled machine word size `Nat.log2 n + 1`.
- `SuccinctSelectProposal.SampledPayloadLiveStoredWordSelectFamily.bounded_constant_query_profile`
  isolates the select-side builder target: produce payload-live select locator
  data whose auxiliary payload is bounded by the sampled-directory envelope,
  and the existing counted select path immediately gives cost `<= 3` and exact
  erasure to `Succinct.select`.
- `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectFamily.constant_query_profile`
  adds the select-side two-level target: separate coarse-locator/local-delta
  payload accounting, `o(n)` combined overhead, exact select through counted
  coarse-table, local-table, payload-word, and word-select reads, and every
  payload word bounded by `Nat.log2 n + 1`.
- `SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily.bp_constant_query_profile`
  combines the two-level rank and select components into the existing generic
  `RankSelectDirectory` and `BalancedParensAccessFamily` contracts. This is
  the bridge that lets BP-close/LCA navigation consume the two-level
  rank/select components without a special-purpose BP API.
- `SuccinctSelectProposal.TwoLevelPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_built_query_profile`
  gives the stateful BP close-navigation profile over two-level rank/select
  plus payload-live LCA-close: payload length `2*n + o(n)`, query cost
  `<= 3 * queryCost + 1`, and exact RMQ answer recovery.
- `SuccinctSelectProposal.TwoLevelEncodedBPCloseRMQNavigationFamily.two_n_plus_o_encoded_query_profile`
  lifts the same path to payload-only encoded component functions, with
  explicit agreement fields tying encoded select/LCA-close/rank operations to
  the built payloads.
- `SuccinctSpace.RankSelectDirectory.ofStoredWordData_profile` combines the
  stored rank and stored select components into the reusable rank/select
  interface without using the old raw packed aggregate wrappers.
- `SuccinctSpace.PayloadBackedStoredWordRankSelectData.directory_profile`
  records that the stored words/samples/locators are decoded from explicit
  counted auxiliary payload bits, closing the proof-only table leakage at this
  component boundary.
- `SuccinctSpace.StoredRankBalancedParensAccess.profile` lifts that to
  balanced parentheses, transporting prefix/final balance and proving exact
  excess with cost `<= 6`.
- `SuccinctSpace.BalancedParensAccess.ofPayloadBackedStoredWordRankSelectData_profile`
  remains as the older compatibility lift for payload-backed rank/select
  components.
- `SuccinctSpace.PayloadBackedStoredWordRankSelectFamily.bp_constant_query_profile`
  packages the same payload-backed rank/select component as a family-level
  balanced-parentheses access structure with `o(n)` auxiliary overhead.
- `SuccinctSpace.StoredRankBalancedParensAccessFamily.constant_rank_excess_profile`
  packages the same faithful rank/excess story for any family whose sampled
  directory overhead is proved `LittleOLinear`.

The old E1 interface-building work is closed for RMQ. The payload-live
BP-close-navigation codecs, bounded payload words, dense/sparse select witness,
compact BP close/LCA directory, and rank-seeded local decoder are consumed by
the final BP-native capstone. For rank/select as a reusable spoke, the remaining
work has moved to compressed/FID payload bounds, a clearer word-bounded public
presentation, and balanced-parentheses navigation. The historical two-level
rank and select query paths were forced through counted
supertable/block-table/payload-word reads, and fixed-width encoded-word plus
bounded-entry constructors bridged emitted payload words to the counted table
contracts. The canonical builder layer moved past the rank/select endpoint
blockers: rank has generated super/block sample entries, fixed-width sample
tables, presence/bound lemmas, local chunk-rank exactness, sentinel-backed
endpoint presence, `canonicalTwoLevelRankDataOfChunksExact`, and its profile
theorem. Select has generated coarse/local locator entries, fixed-width locator
table constructors, bounded-query clamping, slice-local word-select exactness,
`canonicalTwoLevelSelectDataOfChunksExact`, and its profile theorem. The select
two-level API uses an explicit local block-index function for block-table reads,
so the reusable profile no longer forces compact builders to expose one
globally addressed local locator word per occurrence. The two sides are combined
by
`canonicalTwoLevelRankSelectDirectoryOfChunksExact_profile` and lifted to
balanced-parentheses access by
`canonicalTwoLevelBalancedParensAccessOfChunksExact_profile`.
`PayloadLiveBPCloseLCADirectory.ofEntries` packages supplied BP close/LCA
entries into the counted optional-Nat payload table, and
`SuccinctCloseProposal.BlockLocalBPCloseLCATable.ofEntries_profile` records the
local block-table component that the later succinct BP navigation scheme fed
into. The earlier missing payload-live BP close/LCA construction has now been
discharged by the compact relative rmM/min-max-tree-style interior navigator,
the endpoint-fringe repair, and the rank-seeded local decoder path. The live C2
checkpoint is now the landed theorem
`SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile`, consumed
by the final BP-native capstone rather than a remaining blocker.

Current final-path spec: `docs/SUCCINCT_FINAL_PATH.md`. Historically the path
split into the C2 compact interior navigator, the concrete macro/micro
BP-close/LCA component that consumes it, and a final join theorem. Select-side
descriptor work remains relevant only if the final BP-native join exposes a
live select gap; it should not displace the current C2 interior target.

### E2 - Reusable Hub Extraction

Status: first standalone import/build surface landed, with a payload-accounted
lower-bound adapter exposed through the hub.

`RMQ.Core.ModelHub` imports exactly the reusable model layer (`Cost`, `RAM`,
`Refine`, `TableModel`, `LowerBound`, and `PayloadLowerBound`). The `RMQHub`
Lake target builds this surface independently, `docs/HUB.md` documents the
import/API contract, and `scripts/hub_axiom_check.lean` gives the hub its own
trust-base gate.

`LowerBound.PayloadLosslessEncoding` is the joint between
`TableModel.PayloadView` and fixed-length capacity counting. The RMQ spoke now
routes `ExactRMQStateEncoding` through it via
`EncodingLowerBound.shapeCount_le_two_pow_of_exactRMQStateEncoding_payloadView`
and
`EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQStateEncoding_payloadView`.
It also exposes uniform charged-budget lower bounds through
`LowerBound.PayloadLosslessEncoding.lower_le_budget_of_payloadBitCount_bound`
and the RMQ corollary
`EncodingLowerBound.logSlackLower_le_budget_of_exactRMQStateEncoding`.
`LowerBound.PayloadSpaceBounds` now packages the reusable two-sided version of
that pattern, and
`EncodingLowerBound.canonicalRepresentativePayloadSpaceBounds_*` instantiates
it for exact RMQ over Cartesian-shape representatives.

Next refinement: move from an import/build boundary to a physical package split
only after the API stabilizes and the next spoke needs it. The current
repository should remain the RMQ spoke until that trigger fires; see
`docs/REPOSITORY_STRATEGY.md`.

The first extraction spoke is now standalone succinct rank/select. The
`RMQRankSelect` import root exposes an RMQ-independent spec and the public
Jacobson/Clark theorem:
`GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile`.
It proves an `n + o(n)` payload theorem with constant modeled `access`, `rank`,
and `select` queries. The next rank/select research targets are compressed/FID
payload bounds, a tighter word-bounded public presentation, and
balanced-parentheses navigation over the same spec surface.

## Target Hub Layout

```text
Core/
  Cost/Time      -- writer-style cost layer, CSLib-TimeM-compatible
  Cost/RAM       -- operational step model and soundness theorem
  Refine         -- reference/executable refinement framework
  LowerBound     -- encoding/capacity/lower-bound framework
  PayloadLowerBound -- payload-accounted state encodings
RMQ/
  Core/*         -- RMQ reference semantics, windows, shapes, LCA bridge
  Impl/*         -- RMQ backends and instrumented representations
  LowerBound     -- RMQ instance of Core/LowerBound
```

The existing `LeftmostArgMin` / `RMQBackend` correctness layer is the stable
reference layer. The RMQ spoke has now routed the main cost, refinement,
succinct-space, and lower-bound claims through reusable hub-style APIs. The
next question is which APIs survive contact with a second spoke.

## Dependency Policy

- Default to Mathlib-free Lean/Std for this repo and this proof sprint. That
  keeps the current extraction portable and avoids unnecessary dependency churn.
- This is not a categorical forever ban. If a future target becomes
  substantially cleaner, more robust, or more CSLib-compatible with a narrow
  Mathlib import, make that an explicit policy decision, isolate it behind the
  hub boundary where possible, and document the reason.
- Align naming and module shape with CSLib conventions where practical, without
  forcing a mass dependency migration before it pays for itself.

## Non-Goals

- No new RMQ backend just for breadth.
- No formalizing every RMQ variant in the literature.
- No probability layer inside the RMQ proof-of-concept.
- D-Space is no longer optional future work for RMQ; the BP-native succinct
  capstone is landed. Future work here is presentation and model strengthening,
  not another hidden RMQ finish-line obligation.
- No new `_value/_erase/_cost/_run` wrapper families unless the active
  refinement target actually needs them.
- A green build is necessary but not sufficient. Each round must close a target
  or reduce a tracked debt metric.
