# W15 U2 Canonical Payload and Whole-Machine Acceptance Matrix

Frozen: 2026-07-12, before Lean implementation edits.

Coordinator amendment (2026-07-13): exact physical-word erasure to
`buildPayload` remains mandatory.  The public space clause may state
`buildPayload.length <= 2 * n + overhead n` with `overhead = o(n)`; exact
length equality is no longer required, and the payload must not be padded to
manufacture equality.

Worker: W15, continued and closed locally by W17
Branch: `codex/rmq-u2-final-route`
Starting checkpoint: `ba49ae9a12ff72cd9a909a6b8f06566d3f3205c3`
Workflow merge: `e8ff7e46d44c427088c4c4af1b4faec6804b089c`
W17 continuation checkpoint: `989e678f145d5cbf66a02c0a207421f81bb7ec7a`

The roadmap join is the list-facing `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`
imported by `RMQPaper`. The required object chain is:

```text
SuccinctClassic.buildPayload xs
  = exact erasure/flattening of one prepared physical word list
  <-> one canonical segmented/physical read store
  -> supplied-store whole-query execution
  -> execution-derived ordered trace and footprint
  -> canonical costed query
  -> List Int half-open leftmost RMQ result
```

The intended canonical definitions below are names/contracts, not evidence.
Evidence is entered only after Lean checks the quoted propositions.

## Frozen prompt requirements

| ID | Exact frozen requirement | Exact proposition required and intended declaration | Public consumer and complete identity/composition chain | Plausible falsifier or edge case | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- |
| `REQ-01` | **One public payload**<br><br>Make the payload executed by the canonical reviewer route literally the public list-facing `buildPayload`, or prove a checked definitional/extensional equality at the list-facing consumer. The exact payload counted by the public space theorem must be the exact payload underlying execution. Do not conjoin an old space theorem with an execution theorem about an appended sibling payload.<br><br>**Coordinator amendment (2026-07-13):** the space statement is an upper bound, not an exact-length requirement; padding to manufacture equality is forbidden. | Define one canonical shape payload used by `SuccinctClassic.buildPayload`; prove at the list consumer both `(buildPayload xs).length <= 2 * xs.length + overhead xs.length`, with `overhead = o(n)`, and `flattenPayloadWords (reviewerPhysicalWords (cartesianShape xs)) = buildPayload xs`. The execution story must name that same payload, not `oldPayload ++ canonicalInteriorPayload`. Intended evidence: `buildPayload_length`, exact physical erasure, and a strengthened paper main theorem containing both clauses for the same `xs`. | `buildPayload xs` -> canonical shape payload -> physical-word flattening -> reviewer read store -> supplied whole-query trace -> `queryCosted`; the exact same `buildPayload xs` is the left side of `buildPayload_length` and of the execution-store identity. | A sibling payload is executed, or unread/decorative padding is added merely to manufacture exact equality. Empty input must not create an uncounted appendix. | Amendment rationale: exact erasure already proves object identity; `<= 2*n + o(n)` is the public space claim, while equality would be a stronger unrelated constraint. | Open pending final checked public chain. |
| `REQ-02` | **One clean canonical layout**<br><br>Inventory every canonical payload component and its actual reviewer-route consumer. The canonical payload must contain every and only the reviewer route’s live sources. Remove or quarantine dead duplicate legacy interior tables from that payload. Keep compatibility storage behind an explicitly separate compatibility surface. | Define an exhaustive canonical source manifest with one source per live segment. Prove `source counted <-> source is a live reviewer source`, each live source is read by its named consumer or is the BP code required by those consumers, and legacy summary/local/global/finite-small sources occur only in an explicitly named compatibility layout/store. Intended evidence: manifest completeness/exclusivity plus source-to-consumer theorems and import/call-graph scan. | Canonical source manifest -> canonical payload concatenation and segment offsets -> final select/rank/local/interior consumers -> paper story. Compatibility manifest/store is separate and is not referenced by `RMQPaper`. | A legacy interior table remains counted beside the canonical component, an always-empty public source remains in the canonical manifest, or a live segment reads words absent from the manifest. | None yet. | Open. |
| `REQ-03` | **Exact physical representation**<br><br>Prove that one pre-execution physical machine-word array/list erases or flattens exactly to the canonical public payload. Cover every read-producing segment, not only the canonical interior suffix. For every executed segment/local address, prove its checked physical offset and show successful reads are positional reads from that same physical array.<br><br>Either execute the flat physical store directly or prove a full refinement from the segmented read-store execution to the flat physical execution preserving result, cost, ordered trace, failures, and footprint. A component-slice theorem does not close this row. | Define `reviewerPhysicalWords`, total per-segment `reviewerSegmentOffset?`, physical address translation including dead/sentinel cases, and a physical read store. Prove: (1) `flattenPayloadWords reviewerPhysicalWords = canonicalPublicPayload`; (2) every canonical segment read equals `reviewerPhysicalWords[(offset + local)]?` with range guards preventing aliasing; (3) the segmented execution and physical execution have equal result, cost, ordered trace after checked address translation, equal failed reads, and equal footprint. Intended capstone: one `ReviewerPhysicalExecutionRefinement` proposition consumed by final adequacy and paper main. | Canonical payload sources -> physical words in source order -> offsets -> physical store -> translated final trace/footprint -> supplied-store execution -> canonical query -> paper theorem. Every segment `0..20` (or the final canonical enumeration) is covered, not merely segment 20. | First/last physical word, local index exactly equal to a component length (must fail, not alias next component), dead segment/index, failed read, repeated read, or a select/rank segment omitted from the flat theorem. | None yet. | Open. |
| `REQ-04` | **Whole-query word bound**<br><br>Replace the segment-20-only argument with one query-independent pre-execution word width `reviewerWordBits n`. It must bound:<br>- every stored and returned physical word;<br>- every translated physical address;<br>- every failed/dead/sentinel address;<br>- segment identifiers or encodings, if retained;<br>- every charged primitive operand and result;<br>- every address appearing in the actual execution footprint. | Define shape/list-independent-by-query `reviewerWordBits n` and a `ReviewerMachineWellFormed` predicate. Prove it for every prepared shape of size `n`, quantifying over all physical words, translated successful/failed/dead addresses, segment encodings, all read and primitive events of every `left right`, returned words/results, and every footprint address. The list-facing theorem must instantiate it with `n = xs.length`. | `n` -> canonical capacity -> `reviewerWordBits n` -> physical store and address translation -> every event/footprint of the same whole-query execution -> final adequacy -> paper theorem. | Empty/singleton/size-two widths; segment 20/29 encoding; canonical component dead address; a failed out-of-range local read; a primitive operand larger than any read word; query-dependent width hidden in a trace maximum. | None yet. | Open. |
| `REQ-05` | **Conventional word-RAM scaling**<br><br>Relate the composed capacity and word width explicitly to input size. Target the strongest clean conventional statement:<br>- capacity is bounded linearly in `n + 1` by a concrete constant, if the live representation permits it;<br>- the width is sufficient to address the input and physical store; and<br>- `reviewerWordBits n = O(log (n + 2))`, preferably through an explicit all-size inequality with a concrete constant.<br><br>A standalone `LittleOLinear machineWordBits` theorem about an unconstrained width function is insufficient. Do not weaken linear capacity to a polynomial bound without a formal obstruction and coordinator-approved contract amendment. | Define concrete `reviewerCapacityLinearConstant` and prove `reviewerCapacity n <= reviewerCapacityLinearConstant * (n + 1)`, `n <= 2 ^ reviewerWordBits n`, `reviewerPhysicalWords.length <= 2 ^ reviewerWordBits n`, and an explicit all-size `reviewerWordBits n <= C * (Nat.log2 (n + 2) + 1)` with concrete `C`; package the induced big-O statement if the local asymptotic vocabulary supports it. | Live-source size bounds -> physical word-count linear bound -> reviewer capacity -> word width -> whole-machine well-formedness -> paper main theorem. | A source uses quadratic cells; rechunking produces more than linear words; proof only cites `machineWordBits_littleO`; constant works only above a readiness threshold. | None yet. | Open. |
| `REQ-06` | **Public consumption**<br><br>Consume REQ-01 through REQ-05 in:<br>- final supplied-store/model adequacy;<br>- the list-facing no-synthetic execution story;<br>- the paper main theorem;<br>- `RMQ.Headlines.RMQ` aliases;<br>- the checked axiom/headline inventory.<br><br>The final public conjunction must concern the same payload, store, execution, physical representation, and word model. | Strengthen final adequacy, `SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory`, `listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`, and `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` so the conjunction explicitly shares one `buildPayload`, physical words/store, execution, footprint, and `reviewerWordBits xs.length`. Add all load-bearing declarations to axiom inventories and verify their printed assumptions. | Lean definitions in FlatPayload/StoreParam/ModelAdequacy -> list story -> headline theorem -> `RMQPaper` import -> three axiom checks. | Public theorem conjoins `buildPayload_length` with a story about another payload; headline alias drops physical/scaling clauses; axiom inventory checks only local helpers. | None yet. | Open. |
| `REQ-07` | **Claim synchronization**<br><br>Reconcile README, artifact claims, theorem/claim maps, trust packets, roadmap, and both claim-drift policy files. The old route-split `4144`, Ready-regime `118`, zero-block route, and `196727` surfaces must be consistently identified as compatibility/history, not the canonical reviewer route. A green claim-drift scan backed by stale policy does not close this requirement. | Every named prose/policy surface states the canonical route uses the shared payload/physical machine and transitional bound `328`; `4144`, `118`, zero-block, and `196727` are compatibility/history only. Roadmap U2 is recorded as worker candidate pending coordinator reconstruction/blind audit, never `ACCEPTED` or unconditional complete. Both claim-drift policy files encode the new canonical tokens and compatibility classification. | Checked Lean capstone -> theorem/claim maps -> README/artifact/trust/review packets -> roadmap candidate state -> claim policies -> green drift scan. | `RMQ_FINAL_ROADMAP` says `Status: complete`; a policy still requires 4144 as canonical; one trust packet describes Ready dispatch as public; docs overstate coordinator acceptance. | None yet. | Open. |
| `REQ-08` | **Preserve real progress**<br><br>Preserve:<br>- the uniform all-size canonical interior route;<br>- absence of Ready/Active/inactive and zero-block dispatch from the reviewer path;<br>- real charged-read value dependency;<br>- supplied-store agreement and successful-read backing;<br>- no synthetic or decorative events;<br>- the checked transitional whole-query bound `328`.<br><br>Do not reintroduce thresholds, fallback answer tables, padding, decorative reads, semantic routing oracles, or an appended uncounted payload. | Existing canonical all-size route/exactness/store-parametricity/no-synthetic and exact `328` theorems remain checked, and strengthened whole-machine capstone proves the returned result is decoded from charged supplied-store reads. Reviewer dependency scan finds no Ready/Active/inactive/zero-block dispatch. | Canonical directory -> canonical cross-block/LCA -> final structural and supplied executions -> whole query -> list query -> paper theorem; compatibility declarations have no reverse edge into this chain. | Empty/small input takes fallback; result computed before replay; trace padded to 328; semantic winner stored in proof field; legacy zero-block theorem imported/referenced by headline route. | None yet. | Open. |

## Inherited invariants

| ID | Exact frozen invariant | Exact proposition required / intended evidence | Consumer and identity chain | Falsifier / boundary | Evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `INV-STORE-IDENTITY` | the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient | Same-object equalities required by REQ-01 and REQ-03, present in the paper conjunction. | `buildPayload` = physical flattening -> executed store. | Appended sibling payload. | None. | Open. |
| `INV-VALUE-DEPENDENCY` | returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads | For every final result, supplied-store execution/refinement traces decisive reads and decoding; store disagreement at a decisive word may change result, while agreement on footprint fixes it. | Supplied physical reads -> decoded select/rank/interior candidates -> result. | Precomputed semantic answer replayed after reads. | None. | Open. |
| `INV-TRACE-EXECUTION` | traces and footprints are derived from the execution they describe | Trace is the execution trace; footprint is exactly its ordered/read-address projection; physical translation theorem preserves order/failures. | Physical execution -> trace -> footprint. | Separately recorded footprint. | None. | Open. |
| `INV-STORE-AGREEMENT` | supplied-store agreement determines result, cost, and the relevant trace | Agreement on the actual physical footprint implies equality of result, cost, ordered trace, and footprint with canonical execution. | Supplied store -> physical execution -> final/list query. | Agreement proves result only, or uses a static superset without trace equality. | None. | Open. |
| `INV-READ-BACKING` | every successful read is backed positionally by the counted store | Every successful translated read is `reviewerPhysicalWords[address]? = some word` and flattening is `buildPayload`. | Trace event -> translated address -> physical word -> public payload. | Segment word backed only by a sibling array. | None. | Open. |
| `INV-WORD-WIDTH` | stored and returned words fit one declared modeled machine word | Whole-machine predicate bounds all stored/read/returned words by `reviewerWordBits n`. | Prepared input width -> store and result. | Only interior words bounded. | None. | Open. |
| `INV-ADDRESS-WIDTH` | every executed address, dead/sentinel address, and operand fits the modeled machine word, not merely the host array bounds | Whole-machine predicate bounds every translated execution/footprint/dead address and all operands below `2 ^ reviewerWordBits n`. | Width -> physical execution. | Host array bound substituted for capacity. | None. | Open. |
| `INV-ALL-SIZE` | exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch | Unconditional list/shape exactness and kernel checks for empty where admitted, singleton, size two, threshold boundaries, same/cross block. | Canonical layout -> final query -> list result. | Small-size fallback. | None. | Open. |
| `INV-PROOF-SEPARATION` | proof-only fields never carry answers or uncharged routing information | Definitions inspect only stored words and arithmetic; proof fields appear only in proofs. Dependency audit plus refinement types. | Physical reads -> decoder -> result. | Answer-containing proof field/oracle. | None. | Open. |
| `INV-NO-SYNTHETIC` | synthetic events, decorative rereads, and post-hoc replay do not support the execution claim | Every trace event is a real read or charged primitive; no synthetic-cost events; result/value dependency from those events. | Execution trace -> story -> paper. | Padding/decorative read. | None. | Open. |
| `INV-CATEGORY-SEPARATION` | payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct | Definitions/docs separately state bit flattening, physical word list, model event cost, proof predicates, and validation runtime. | All public packets. | Word count advertised as bit payload or Lean runtime. | None. | Open. |
| `INV-PUBLIC-COMPOSITION` | a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution. Conjoining true theorems about different payloads is not closure. | Paper main theorem explicitly shares `xs`, `buildPayload xs`, one physical words/store/execution/footprint/width across all conjuncts. | List capstone -> headline -> paper. | Existentially or definitionally different objects. | None. | Open. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | a physical-machine claim supplies one pre-execution store/word array and a checked address translation for every executed segment, including failed/dead accesses. A theorem for one suffix or component is not a whole-machine embedding. | Full physical refinement in REQ-03 covers every live segment and all failure/dead cases. | Segment manifest -> physical array -> whole trace. | Segment-20 slice only. | None. | Open. |
| `INV-WIDTH-SCALING` | one query-independent word-width declaration bounds all stored words, addresses, sentinels, operands, and primitive results, and its capacity/width is related to input size in the form required by the public word-RAM claim. A standalone asymptotic fact about an unconstrained width function is insufficient. | REQ-04/05 whole-machine predicate, concrete linear capacity, and explicit logarithmic inequality consumed publicly. | `n` -> capacity/width -> physical machine -> paper. | Query-local max or unconstrained `machineWordBits_littleO`. | None. | Open. |

## Frozen adversarial cases

| ID | Exact case | Required checked evidence | Consumer / chain | Falsifier | Evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CASE-EMPTY` | empty input where admitted | Kernel-checked payload/physical flattening, capacity/width, no hidden fallback, and invalid-query behavior. | Empty shape through public builders. | Nonempty assumption hidden in word model. | None. | Open. |
| `CASE-SINGLETON` | singleton | Kernel-checked valid query result, physical addresses/sentinels/words, store backing, footprint. | `[x]`, query `[0,1)`. | Old two-bit capacity failure. | None. | Open. |
| `CASE-SIZE-TWO` | size two | Kernel-checked both Cartesian orientations and valid intervals, with full bounds/backing. | Two-element list/shape. | Old three-bit capacity failure. | None. | Open. |
| `CASE-SAME-CROSS` | same-block and cross-block queries | Kernel-checked representative queries exercise both canonical routes and preserve exactness/value dependency. | LCA close dispatch -> final query. | Cross-block silently falls back. | None. | Open. |
| `CASE-PHYSICAL-ENDS` | first and last legal physical addresses | Positional get theorem at address 0 and length-1; length is sentinel/dead and fails without aliasing. | Physical store. | Off-by-one or empty-source offset alias. | None. | Open. |
| `CASE-DEAD` | every canonical dead/sentinel address | Enumerate retained dead/sentinel encodings and prove width plus failed-read/trace refinement. | Segment translation and controller. | One segment's dead address omitted. | None. | Open. |
| `CASE-EACH-SEGMENT` | a query touching each read-producing segment | Checked witnesses per live segment, or a proof that each segment's possible reads use the physical translation/backing theorem; distinguish segments not jointly reachable in one query. | Whole trace source manifest. | A live segment has no physical theorem. | None. | Open. |
| `CASE-THRESHOLD` | any retained compatibility threshold boundary | Kernel/symbolic threshold-minus-one, threshold, threshold-plus-one checks show canonical reviewer route is unchanged; compatibility only is labeled. | Reviewer dependency chain. | Ready/Active dispatch reappears. | None. | Open. |

## Verification and policy checks

| ID | Exact command/check | Evidence required | Surface | Important falsifier / uncovered scope | Evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `CHK-FOCUSED-FLAT` | focused builds for every touched FlatPayload module | Exit 0 after final edits. | Payload/physical representation. | Stale olean. | None. | Open. |
| `CHK-FOCUSED-SEGMENT` | focused builds for every touched segment/store module | Exit 0 after final edits. | Segment/physical store. | Only top-level build hides target error. | None. | Open. |
| `CHK-FOCUSED-ADEQUACY` | focused builds for every touched adequacy module | Exit 0 after final edits. | Final model packet. | Local helper not consumed. | None. | Open. |
| `CHK-FOCUSED-CLASSIC` | focused build for `RMQ.Core.SuccinctRMQClassic` | Exit 0 after final edits. | List consumer. | Headline not included. | None. | Open. |
| `CHK-PAPER` | `lake build RMQPaper` | Exit 0. | Narrow paper import root. | Does not prove claim identity by itself. | None. | Open. |
| `CHK-FULL` | `lake build` | Exit 0. | Whole repository. | Semantic gaps remain possible. | None. | Open. |
| `CHK-AXIOM` | `lake env lean scripts/axiom_check.lean` | Exit 0; new load-bearing theorem assumptions printed and contain no unexpected axioms. | Curated theorem inventory. | Missing new capstone. | None. | Open. |
| `CHK-WORDRAM-AXIOM` | `lake env lean scripts/wordram_axiom_check.lean` | Exit 0; physical/width capstones included. | WordRAM trust inventory. | Only component theorem checked. | None. | Open. |
| `CHK-HEADLINE-AXIOM` | `lake env lean scripts/headline_axiom_check.lean` | Exit 0; strengthened headline/paper theorem included. | Public root. | Alias drops clauses. | None. | Open. |
| `CHK-VALIDATE` | `lake exe rmq_succinct_classic_validate` | Exit 0 with expected canonical route cases and bound 328. | Executable validation only. | Not proof evidence. | None. | Open. |
| `CHK-HYGIENE` | hygiene scan for `sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable` and `import Mathlib` | No prohibited new hits in `RMQ`, `RMQExamples`, `lakefile.toml`; classify any existing hits. | Trust boundary. | Search scope too narrow. | None. | Open. |
| `CHK-NATIVE` | scan for `native_decide|Lean.ofReduceBool` | No new or unclassified trust shortcuts. | Kernel-check policy. | Edge examples use native decision. | None. | Open. |
| `CHK-DIFF` | `git diff --check` | Exit 0. | Patch hygiene. | Does not validate semantics. | None. | Open. |
| `CHK-DESIGN` | `scripts/design_decision_check.ps1` | Exit 0 after recording representation/store/word/compatibility choices and rejected alternatives. | Decision ledger. | Terse change log without alternatives/consequences. | None. | Open. |
| `CHK-CLAIM` | `scripts/claim_drift_scan.ps1` | Exit 0 after inspecting and updating both policy files, not merely satisfying stale tokens. | Claims/docs. | Policy still treats compatibility constants as canonical. | None. | Open. |
| `CHK-DEPENDENCY` | reviewer dependency scan for Ready/Active/inactive, zero-block, legacy payload/store, `4144`, `118`, and `196727` | No live reverse edge from `RMQPaper`/`RMQ.Headlines.RMQ` canonical theorem to compatibility dispatch/storage/constants; history aliases are explicitly labeled. | Public composition. | Text scan misses reducible alias; inspect definitions/imports. | None. | Open. |

## Explicitly deferred items

| ID | Exact deferred item | Why non-blocking / required boundary | Consumer | Falsifier | Evidence | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `DEF-U3` | U3 cost cleanup is deferred. | Non-blocking only because the prompt requires preserving the honest checked transitional whole-query bound `328`; no obsolete exact constant may be preserved by padding. U2 must still prove cost follows the physical execution. | Later U3 derives the final explained constant from this execution. | Current branch leaves cost disconnected from physical reads or uses 118/4144/196727 canonically. | None. | Open pending boundary proof. |
| `DEF-M1` | M1 certification is deferred. | Broad certificate refactoring is deferred, but every machine fact required for U2 truth (physical identity, agreement, backing, width/scaling) must be present and publicly consumed now. | Later M1 may repackage, not supply missing U2 facts. | A missing U2 theorem is called M1. | None. | Open pending boundary proof. |
| `DEF-A1` | broad A1 file movement is deferred. | Module movement/cleanup may wait; compatibility declarations must nevertheless be outside the canonical object/call chain now. | Later architectural refactor. | Public root still consumes legacy object because moving it was deferred. | None. | Open pending boundary proof. |
| `DEF-ACCEPTANCE` | Only the coordinator may record U2 as `ACCEPTED`, after independently reconstructing the matrix and obtaining the mandatory fresh blind audit. | Worker may record only candidate status and must leave coordinator reconstruction plus fresh blind exact-commit audit as the next step. | Coordinator workflow. | Roadmap/docs say accepted or merge-ready. | None. | Open until handoff. |

## Pre-edit goal reflection and parallelization check

- Overall goal: strengthen `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`
  so one public payload, one complete physical representation, one execution,
  and one input-scaled word model are compositionally identical.
- Current gap: `buildPayload` counts the old flat payload while the execution
  story names an appended canonical sibling; the physical theorem covers only
  the canonical interior suffix; the width is shape/store-derived without a
  linear input-size bound.
- Hard obligation: rebuild the canonical source/layout/physical-store identity
  without losing live select/rank/local/interior reads or the existing uniform
  supplied-store/value-dependency route.
- Forbidden shortcuts: sibling append, component slice, host-array-only bounds,
  query-local width, arbitrary readiness floor, semantic replay, decorative
  reads, compatibility dispatch, or stale claim policy.
- Join owner: W15 lead owns canonical definitions, theorem signatures, matrix,
  integration, public theorem, decisions, and final verification.
- Independent read-only leaves after this freeze: (1) exact live-source and
  physical-offset inventory; (2) linear-capacity/log-width lemma inventory and
  counterexample search; (3) public claim/policy/dependency audit. These feed
  the same join without editing shared surfaces.
- Stop conditions: all rows closed and candidate declaration true; a checked
  obstruction requiring coordinator amendment; a genuine external blocker; or
  explicit redirection.

## Post-edit checked evidence

The tables above are the immutable pre-edit freeze. Their `Open` cells record
the starting state, not the post-edit verdict. This section is the reconstructed
worker evidence. Command rows remain pending until the final ladder is run.

### Exact load-bearing propositions

The public list object is definitionally the canonical reviewer payload:

```lean
def SuccinctClassic.buildPayload (xs : List Int) : List Bool :=
  SuccinctFinal.concreteBPNativeSuccinctRMQCanonicalReviewerPayload
    (SuccinctClassic.cartesianShape xs)
```

The single pre-execution representation is exact, not a sibling/suffix claim:

```lean
theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
    (shape : Cartesian.CartesianShape) :
    flattenPayloadWords
        (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape) =
      concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape
```

The canonical layout is indexed by one exhaustive typed 20-source universe,
including canonical close. The checked manifest chain is:

```lean
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_iff_live
theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup
theorem concreteBPNativeSuccinctRMQReviewerSource_region_injective
theorem concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_consumer_or_sharedBP
theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_exclude_legacy_close
theorem concreteBPNativeSuccinctRMQCanonicalReviewerReadStore_legacyTail_none
```

Every emitted read, including a failed read, has a logical segment below 21
and therefore maps to a listed source/region and its checked physical event:

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_segment_lt
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_read_has_listed_region
```

Every logical read, including a failed read, is the positional read at its
guarded physical translation:

```lean
theorem concreteBPNativeSuccinctRMQGlobalReadStore_eq_reviewerPhysical
    (shape : Cartesian.CartesianShape) (segment index : Nat) :
    (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?
        segment index =
      (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[
        concreteBPNativeSuccinctRMQReviewerPhysicalAddress
          shape segment index]?
```

The reviewer-facing physical execution invokes the existing supplied-store
evaluator through an adapter that performs each read against the supplied flat
store at segment zero and the checked translated address:

```lean
def concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
    (shape) (physicalStore) : WordRAM.ReadStore where
  readWord? segment index :=
    physicalStore.readWord? 0
      (concreteBPNativeSuccinctRMQReviewerPhysicalAddress
        shape segment index)

def concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
    (shape) (physicalStore) (left right) :=
  let logicalResult :=
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape
      (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
        shape physicalStore)
      left right
  { value := logicalResult.value
  , trace := logicalResult.trace.map
      (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) }

theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_refines_logical
    (shape) (left right) :
  flatPhysicalTrace.value = logicalTrace.value /\
  flatPhysicalTrace.trace =
    logicalTrace.trace.map
      (concreteBPNativeSuccinctRMQReviewerPhysicalizeEvent shape) /\
  flatPhysicalTrace.toCosted = logicalTrace.toCosted
```

The complete physical execution is determined by agreement on the first
execution-derived ordered physical footprint. The converse corruption theorem
shows a disagreement at a consumed address changes the complete execution, so
the flat store is not ignored:

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_ne_of_consumed_read_disagreement
```

The exact logical footprint retains order, repetition, and failures:

```lean
def concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
    (shape) (store) (left right) :=
  (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
      shape store left right).trace.filterMap fun event =>
    match event with
    | WordRAM.TraceEvent.readWord segment index _ => some (segment, index)
    | _ => none

def concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
    shape storeA storeB left right : Prop :=
  forall segment index,
    (segment, index) ∈
        concreteBPNativeSuccinctRMQWholeQueryOrderedReadFootprintWithStore
          shape storeA left right ->
      storeA.readWord? segment index = storeB.readWord? segment index

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore_store_parametric_of_ordered_read_footprint
    (shape) (storeA storeB) (left right)
    (hagree :
      concreteBPNativeSuccinctRMQWholeQueryStoresAgreeOnOrderedReadFootprint
        shape storeA storeB left right) :
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeA left right =
      concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape storeB left right
```

The physical footprint is literally the physical trace's ordered read
projection, so failures/repetitions are retained:

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint_recorded
    (shape) (left right) :
    concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalFootprint
        shape left right =
      (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
          shape left right).trace.filterMap fun event =>
        match event with
        | WordRAM.TraceEvent.readWord 0 address _ => some address
        | _ => none
```

The one pre-execution word model has exact linear capacity and an explicit
all-size logarithmic inequality:

```lean
theorem concreteBPNativeSuccinctRMQReviewerCapacity_linear (n : Nat) :
  concreteBPNativeSuccinctRMQReviewerCapacity n = 400000 * (n + 1)

theorem concreteBPNativeSuccinctRMQReviewerPhysicalWords_length_le_capacity
    (shape) :
  (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length <=
    concreteBPNativeSuccinctRMQReviewerCapacity shape.size

theorem concreteBPNativeSuccinctRMQReviewerWordBits_le_log (n : Nat) :
  concreteBPNativeSuccinctRMQReviewerWordBits n <=
    20 * (Nat.log2 (n + 2) + 1)
```

It bounds all physical words, successful returned words, all translated
addresses (including dead/failure translations), all physical-footprint
addresses, segment encodings, input operands, and every charged primitive
operand/result:

```lean
hmem : word ∈ concreteBPNativeSuccinctRMQReviewerPhysicalWords shape
⊢ word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size

hread : globalStore.readWord? segment index = some word
⊢ word.length <= concreteBPNativeSuccinctRMQReviewerWordBits shape.size

⊢ concreteBPNativeSuccinctRMQReviewerPhysicalAddress shape segment index <
    2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size

hmem : address ∈ wholeQueryFlatPhysicalFootprint shape left right
⊢ address < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits shape.size

hoperand : operand <= n
⊢ operand < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n

hsegment : segment <= concreteBPNativeDeadTraceSegment
⊢ segment < 2 ^ concreteBPNativeSuccinctRMQReviewerWordBits n

event ∈ physicalTrace.trace
⊢ concreteBPNativeTraceEventPrimitiveOperandsFitInBits
    (concreteBPNativeSuccinctRMQReviewerWordBits shape.size) event
```

Successful physical reads are positionally backed by that same list:

```lean
hmem : WordRAM.TraceEvent.readWord 0 address (some word) ∈
  (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResult
    shape left right).trace
⊢ address < (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape).length /\
  (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)[address]? = some word
```

The list-facing capstone consumes the same objects. Its public conjunction now
contains exact physical erasure, genuine physical/logical refinement, physical
footprint determinism, and the typed manifest:

```lean
forall (storeA storeB : WordRAM.ReadStore) left right,
  SuccinctClassic.physicalStoresAgreeOnOrderedReadFootprint
      xs storeA storeB left right ->
    SuccinctClassic.reviewerPhysicalTraceResultWithStore
        xs storeA left right =
      SuccinctClassic.reviewerPhysicalTraceResultWithStore
        xs storeB left right
```

This is conjoined in `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem` with
`buildPayload` length `<= 2*n + overhead n`, `LittleOLinear overhead`, exact
physical-word erasure to that same `buildPayload`, invalid-range rejection,
exact valid-window RMQ, leftmost ties, the `328` cost bound, genuine physical
refinement/determinism, the typed manifest, and
`FlatPayloadStoreNoSyntheticExecutionStory`. That story contains
`ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`, whose fields name the same
physical words, payload, physical/logical execution, physical footprint,
capacity, width, backing, and word/address bounds above.

### Final requirement verdicts

| ID | Exact proposition and evidence | Public consumer and complete identity/composition chain | Plausible falsifier checked | Worker verdict |
| --- | --- | --- | --- | --- |
| `REQ-01` | `buildPayload xs` is definitionally `CanonicalReviewerPayload (cartesianShape xs)`; `ReviewerPhysicalWords_erases` has that exact payload as its right side. | `buildPayload` -> canonical layout -> reviewer physical words erasure -> global read-store equality -> supplied trace -> `queryCosted` -> paper theorem. | Appended sibling payload would make the erasure right side differ from `buildPayload`; it does not. | Closed locally; public builds, axiom inventories, integrated gate, and artifact reproduction are green. |
| `REQ-02` | `ReviewerSource` is one typed 20-constructor universe including canonical close. `...counted_iff_live`, `...PhysicalSources_nodup`, `...Source_region_injective`, segment coverage, consumer/shared-BP ownership, legacy-close exclusion, and `...read_segment_lt` are checked. | Every emitted logical read, including failures, has segment `<21`; segment coverage maps it to a listed source/region. Legacy tail reads are `none` on the canonical store. | Opposite-polarity/dead legacy tables in the canonical payload, an unlisted failed read, or a duplicated region. The universal all-event theorem and typed manifest exclude all three. | Closed locally; all three axiom inventories are green. |
| `REQ-03` | `ReviewerPhysicalStoreAdapter` makes the existing supplied-store evaluator read the caller's flat store at translated addresses. `...FlatPhysical_refines_logical` preserves value, cost, ordered trace, successes/failures; `...FlatPhysicalFootprint_recorded` is execution-derived; agreement determines the complete run and consumed-address disagreement is observable. | Supplied flat store -> checked adapter -> existing whole-query evaluator -> physical trace/footprint -> guarded list consumer -> paper theorem. | Mapping a precomputed canonical logical value, ignoring the store, dropping failure/repetition order, or using a component slice. The evaluator definition, refinement, complete-result determinism, and corruption theorem exclude these. | Closed locally; theorem builds and executable corruption witness are green. |
| `REQ-04` | Exact propositions quoted above cover stored/returned words, all translated live/dead addresses, footprint addresses, input operands, segment/dead encodings, and every charged primitive operand/result. | Pre-execution `reviewerWordBits shape.size` -> physical list/address map -> physical trace -> adequacy record -> headlines. | A failed sentinel outside the width or a primitive using a larger operand. Universal address and event theorems include both. | Closed locally; WordRAM and headline inventories are green. |
| `REQ-05` | Capacity is definitionally `400000*(n+1)`; physical length is bounded by it; width is `<= 20*(log2(n+2)+1)` and is sufficient for input/store/dead addresses. | Input size -> linear capacity -> `machineWordBits capacity` -> whole physical execution. | Polynomial-only capacity or unconstrained `LittleOLinear machineWordBits`; neither is used. | Closed locally; full gate is green. |
| `REQ-06` | Final adequacy contains manifest, every-read-to-region, exact erasure, genuine physical refinement, footprint, backing, capacity/width, determinism, and corruption fields. The list story and paper theorem consume the same physical evaluator; the paper theorem directly conjoins exact erasure, physical refinement/determinism, and manifest facts. Headlines and all three axiom inventories name the load-bearing declarations. | ReviewerPhysical -> RAM all-read coverage -> StoreParam adapter/execution -> ModelAdequacy -> SuccinctClassic -> `RMQ.Headlines.RMQ` -> `RMQPaper`. | Headline drops physical execution, combines sibling objects, or checks only local helpers. The direct paper conjunction and inventories prevent this. | Closed locally; `RMQPaper`, headlines, all inventories, and artifact reproduction are green. |
| `REQ-07` | README, artifact guide/claims, family/what-is-proved, paper theorem/model/claim maps, trust/Word-RAM packets, roadmap, digestion/provenance, and both claim policies identify `328` as canonical transitional and `118`/`4144`/zero-block/`196727` as compatibility/history. Roadmap says worker candidate only. | Checked theorem -> public docs -> roadmap candidate boundary -> claim-drift policy. | Stale current-`4144` prose or `Status: complete`; corrected in live sections. | Closed locally; claim-drift scan reports 437 reviewed hits and 0 strict failures. |
| `REQ-08` | Existing canonical exactness/no-synthetic/`328` theorems remain; the physical value is computed by the existing evaluator through `ReviewerPhysicalStoreAdapter`; footprint agreement proves dependency and consumed-address disagreement gives a checked non-ignore witness. | Canonical directory -> all-size close/LCA -> supplied logical evaluator through flat adapter -> physical execution -> guarded list query. | Ready/Active/zero-block dispatch, answer table, padded event, precomputed logical-value remapping, or appended payload. None occurs in the canonical chain. | Closed locally; dependency, hygiene, and full integrated gates are green. |
| `W17-RANGE` | `SuccinctClassic.withValidRange` is the single list-facing boundary used by canonical, supplied-store, trace, costed, prepared, and physical surfaces. `queryCosted_invalid` plus empty/reversed/out-of-bounds corollaries prove `none`; invalid traces are empty and cost zero. | `ValidRange xs left right` -> controller thunk or pure `none` -> every public List execution projection. | `[9,8,7] 1 1`, a reversed window, or an end beyond length returns `some`; theorems and executable guards reject all three. | Closed locally; examples, validator, and cost harness are green. |
| `W17-EXAMPLES` | `RMQExamples/Concrete.lean` and both validation modules use semantic checks: valid same/cross-block, invalid ranges, exact `328`, route classification, exact erasure, physical backing, and corruption dependency. | Public list/physical surfaces -> executable `#guard` and differential harness. | Refreshed hard-coded bit positions or legacy Ready/route-split labels. Neither remains. | Closed locally; 498-window validator and bounded 128-element cost harness are green. |

### Inherited invariant verdicts

| Invariant | Exact closing evidence | Verdict |
| --- | --- | --- |
| `INV-STORE-IDENTITY` | Definition of `buildPayload` plus `ReviewerPhysicalWords_erases`. | Proof closed. |
| `INV-VALUE-DEPENDENCY` | The supplied flat store is read through `ReviewerPhysicalStoreAdapter`; complete `TraceResult` equality follows from agreement on the first physical footprint, and a consumed-address disagreement changes the run. | Proof closed. |
| `INV-TRACE-EXECUTION` | The adapter-backed physical trace is exactly the evaluator's logical trace mapped by `ReviewerPhysicalizeEvent`; `toCosted` equality is conjoined. | Proof closed. |
| `INV-STORE-AGREEMENT` | `...store_parametric_of_ordered_read_footprint`, including failed reads. | Proof closed. |
| `INV-READ-BACKING` | Whole-query physical success implies in-range `getElem? = some word`. | Proof closed. |
| `INV-WORD-WIDTH` | Physical-word and successful-returned-word length theorems. | Proof closed. |
| `INV-ADDRESS-WIDTH` | Universal physical-address theorem plus consumed-footprint theorem. | Proof closed. |
| `INV-ALL-SIZE` | No size premise in physical identity/refinement/store-parametricity/width theorems; canonical directory all-size profile remains. | Proof closed. |
| `INV-PROOF-SEPARATION` | All query values come from `ReadStore` results; proof predicates are not read sources. | Proof closed. |
| `INV-NO-SYNTHETIC` | Final adequacy `no_synthetic` field; no cost padding was introduced. | Proof closed. |
| `INV-CATEGORY-SEPARATION` | Bit erasure, machine words, trace ticks, and compiled runtime are separately named in definitions/docs. | Proof closed. |
| `INV-PUBLIC-COMPOSITION` | List story nests final adequacy for the same `cartesianShape xs`; paper theorem consumes that story. | Proof closed. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | Genuine supplied-flat-store evaluation, universal all-read source coverage, and full physical refinement, not a component slice or post-hoc value mapping. | Proof closed. |
| `INV-WIDTH-SCALING` | Linear capacity equality plus explicit logarithmic width inequality. | Proof closed. |

### Adversarial-case evidence

| Case | Exact checked evidence | Verdict |
| --- | --- | --- |
| Empty/singleton/size two | `canonicalRelativeRmmInteriorRangeFootprint_empty_kernel_checked`, `_singleton_kernel_checked`, `_sizeTwo_kernel_checked`. | Closed. |
| Same-block/cross-block | All-size structural LCA/close trace plus canonical-interior exactness; no compatibility dispatch in the whole-query definition chain. | Closed symbolically. |
| First/last legal address | `ReviewerPhysicalWords_first_last_positional`: nonempty physical list implies `getElem? 0 = some firstWord` and `getElem? (deadAddress-1) = some lastWord`. | Closed. |
| Dead/sentinel address | `PhysicalAddress_deadSegment` for every `21 <= segment`; `PhysicalAddress_indexOutOfRange` for every local overflow; `PhysicalDeadAddress_getElem?_eq_none`. | Closed universally. |
| Each read-producing segment | Typed 20-source manifest including canonical close, shared BP alias for logical segments 0/19, total segment map `0..20`, and `...read_segment_lt` for every success/failure event. Mutually exclusive data-dependent select sources are not asserted to co-occur in one query. | Closed structurally; executable suite green. |
| Threshold boundary | `canonicalRelativeRmmInteriorRangeFootprint_address_fits_threshold_boundary`; canonical path has no threshold premise or dispatch. | Closed. |

### Deferred-boundary verdicts

- `DEF-U3`: closed as non-blocking. `328` is the trace-derived transitional
  bound; no padding/decorative reads preserve an old constant.
- `DEF-M1`: closed as non-blocking. All physical/store/width facts required for
  U2 truth are already fields of final adequacy; M1 may only repackage them.
- `DEF-A1`: closed as non-blocking. Compatibility storage/declarations remain,
  but are not in the canonical object/call chain.
- `DEF-ACCEPTANCE`: preserved. This file records worker evidence only. The next
  consumer is coordinator reconstruction followed by a fresh blind exact-commit
  audit; only that coordinator may write `ACCEPTED`.

## Final verification ledger

All earlier post-edit local `pending` qualifiers are discharged by this ledger.
The final worker verdict for `REQ-01` through `REQ-08`, every inherited
invariant, every adversarial case, and `DEF-U3`/`DEF-M1`/`DEF-A1` is
**closed locally**. Remote workflow outcomes are inspected after pushing the
exact commit and reported outside this commit.
`DEF-ACCEPTANCE` deliberately remains coordinator-owned.

| Check | Result |
| --- | --- |
| Runtime-health identity and command probes | Pass: `git status --short --branch` 0.5 s; `git rev-parse HEAD` 0.4 s; `git ls-remote --heads` 0.9 s; focused declaration `rg` 0.5 s; small `Get-Content` 0.5 s; first legitimate small `apply_patch` 3.5 s. No abnormal Git, read orchestration, or patch latency. |
| Focused ReviewerPhysical, RAM, StoreParam, ModelAdequacy, SuccinctClassic, headline, example, and validation builds | Pass; no new linter warnings. |
| `lake build RMQPaper` | Pass in 4.7 s. |
| `lake build` | Pass in 8.9 s, 197-target graph. |
| `lake build RMQExamples` | Pass in 25.2 s, 187-target graph. |
| `lake env lean scripts/axiom_check.lean` | Pass in 89.7 s; new load-bearing declarations printed with only expected Lean principles. |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass in 40.9 s. |
| `lake env lean scripts/headline_axiom_check.lean` | Pass in 19.7 s. |
| `lake exe rmq_succinct_classic_validate` | Pass in 11.0 s: 498 valid/invalid windows across 43 deterministic inputs. |
| `lake exe rmq_succinct_classic_cost_harness` | Pass in 73.9 s: invalid, same-block, and cross-block windows under exact canonical bound `328`. The default maximum fixture is the measured 128-element ceiling; the former 1024-element runtime-only fixture was removed after a 1204 s timeout, without changing theorem-level all-size claims. |
| Forbidden-token/Mathlib hygiene scan | No matches in 1.4 s. |
| `native_decide` / `Lean.ofReduceBool` scan | No matches in 0.4 s. |
| Canonical-claim stale wording scan | No current/paper-facing `4144`, unconditional U2-complete, or appended-sibling wording. |
| `git diff --check` | Pass in 0.5 s; only Windows line-ending notices. |
| `scripts/design_decision_check.ps1` | Final pass in 2.3 s across 33 changed files. |
| `scripts/claim_drift_scan.ps1` | Final pass in 3.4 s: 437 reviewed hits, 0 strict failures. |
| `powershell -ExecutionPolicy Bypass -File scripts\\gate.ps1` | `GATE PASS` in 284.1 s. |
| Git Bash `scripts/reproduce_artifact.sh` | Pass in 285.6 s with Lean 4.22.0. Bash lacked `pwsh` and explicitly skipped its nested gate outside CI; the standalone PowerShell gate immediately above passed. |

Controlled status: worker candidate only. Coordinator reconstruction and a
fresh blind exact-commit audit are the mandatory next consumer.
