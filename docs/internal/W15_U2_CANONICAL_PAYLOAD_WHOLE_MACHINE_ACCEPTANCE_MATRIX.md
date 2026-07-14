# W15 U2 Canonical Payload and Whole-Machine Acceptance Matrix

Frozen: 2026-07-12, before Lean implementation edits.

Coordinator amendment (2026-07-13): exact physical-word erasure to
`buildPayload` remains mandatory.  The public space clause may state
`buildPayload.length <= 2 * n + overhead n` with `overhead = o(n)`; exact
length equality is no longer required, and the payload must not be padded to
manufacture equality.

Coordinator amendment (2026-07-13, semantic gate): add
`INV-SEMANTIC-NONVACUITY`; reopen `REQ-02`, `REQ-06`,
`INV-VALUE-DEPENDENCY`, `INV-PUBLIC-COMPOSITION`, and the bundled W17
validity/composition evidence.  Each applicable semantic subclaim requires its
own attempted anti-vacuity mutation; prior bundled evidence is not silently
reinterpreted.

Worker: W15, continued as the W17 semantic candidate
Branch: `codex/rmq-u2-final-route`
Starting checkpoint: `ba49ae9a12ff72cd9a909a6b8f06566d3f3205c3`
Workflow merge: `e8ff7e46d44c427088c4c4af1b4faec6804b089c`
W17 continuation checkpoint: `989e678f145d5cbf66a02c0a207421f81bb7ec7a`

Coordinator verdict on W17: `REPAIR_REQUIRED`.  At exact remote commit
`a96f40b12c42133260a3fe840ccf0e4d33dbda6b`, the physical store,
value-dependency, invalid-range, space, width, and uniform-`328` rows remain
accepted candidate evidence.  `REQ-02.a`, `REQ-02.b`,
`INV-SEMANTIC-NONVACUITY`, and their dependent `REQ-06`/public-documentation
rows are reopened because the W17 theorem joined a static segment category to
an arbitrary same-category instruction at an arbitrary state.

W18 repair branch: `codex/rmq-u2-producer-provenance`
W18 exact base: `a96f40b12c42133260a3fe840ccf0e4d33dbda6b`

Coordinator verdict on W18 commit
`63d503d24aadeb501284a658c303bf69861953df`: `REPAIR_REQUIRED`.
The actual-prefix-state event-value theorem is accepted checkpoint evidence,
but the occurrence-level, invocation-preserving, and semantic-nonvacuity rows
remain open. `ReviewerSource.HasProducerMayPath` is the positive direct
component predicate; the fresh mutation rejects the stronger
`ReviewerUnusedSourceMutation.HasOperationalProducer`; no checked implication
connects them. `WholeQueryProgram.ProducesEvent` begins from event-value
membership and `ReviewerProducerReadPath` erases invocation parameters. W19
must replace or bridge these relations and consume the result publicly.

W19 repair branch: `codex/rmq-u2-positional-provenance`
W19 exact base: `af8791150b64038e9c0776e3639634f1d83518ea`

W19 checkpoint `e7278f66d87bd9f90bc9ba71a7107f67cbaa45e1` is accepted evidence
for occurrence/invocation proofs and symbolic source witnesses, but its public
composition is `REPAIR_REQUIRED`: global existential liveness was nested under
unused current-query parameters and validity premises. The continued W19
candidate separates that global packet from exact-query provenance. Coordinator
acceptance and a fresh blind exact-commit audit remain pending. The amendment
at the end of this file records the current propositions and evidence without
rewriting the historical W15--W18 ledgers.

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
| `INV-SEMANTIC-NONVACUITY` | semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. A predicate defined to be `True`, an enumeration restated as membership, or a separately hand-written consumer label does not establish operational liveness by itself | Operational segment/source/leaf maps and actual evaluator-branch equalities in both directions; semantic mutations must fail per subclaim. | Closed whole-query evaluator -> emitted reads and counted sources -> typed manifest -> final adequacy -> public story. | `True`, `False`, enumeration membership, dead addition, used removal, forged label, or free-standing label passes as liveness. | Added by explicit 2026-07-13 coordinator amendment; current evidence is in the semantic-gate table below. | Reopened/amended. |
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
candidate evidence. The final ladder results are recorded in the verification
ledger below.

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
including canonical close. The load-bearing producer chain is:

```lean
theorem WholeQueryProgram.evalGlobalWordTrace_event_producer
theorem WholeQueryProgram.ProducesEvent.prefix_state
theorem WholeQueryInstr.evalGlobalWordTrace_read_producer_path
theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_producer_provenance
theorem concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path
theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected
theorem concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer
theorem concreteBPNativeSuccinctRMQReviewerPhysicalSources_nodup
theorem concreteBPNativeSuccinctRMQReviewerSource_region_injective
theorem concreteBPNativeSuccinctRMQReviewerSegmentSource?_coverage
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
execution-derived ordered physical footprint. Answer provenance is stated
separately at `.value`, not inferred from aggregate-record inequality:

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_eq_of_orderedFootprint
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne
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

### Pre-semantic-audit requirement verdicts (historical)

The following W17 verdict table records the state before the 2026-07-13
semantic-gate amendment.  Its `REQ-02`, `REQ-06`, `INV-VALUE-DEPENDENCY`,
`INV-PUBLIC-COMPOSITION`, and W17 validity/composition verdicts are explicitly
reopened and superseded by the current-format amendment table below; the old
word `Closed` is not current evidence for those rows.

| ID | Exact proposition and evidence | Public consumer and complete identity/composition chain | Plausible falsifier checked | Worker verdict |
| --- | --- | --- | --- | --- |
| `REQ-01` | `buildPayload xs` is definitionally `CanonicalReviewerPayload (cartesianShape xs)`; `ReviewerPhysicalWords_erases` has that exact payload as its right side. | `buildPayload` -> canonical layout -> reviewer physical words erasure -> global read-store equality -> supplied trace -> `queryCosted` -> paper theorem. | Appended sibling payload would make the erasure right side differ from `buildPayload`; it does not. | Candidate evidence satisfied; public builds, axiom inventories, and integrated gate are green. Local Bash was unavailable, so artifact reproduction remains a required remote workflow. |
| `REQ-02` | `ReviewerSource` is one typed 20-constructor universe including canonical close. `Live` is derived from read-producing leaf ownership or a checked shared-BP dependency. Counted/live equivalence, physical-region uniqueness, segment coverage, both evaluator-connection directions, legacy-close exclusion, and compatibility-tail absence are checked. | Every emitted read, including failures, maps through actual segment/source/leaf maps to a counted live source and evaluator branch. Every counted source reaches an actual evaluator leaf or checked shared-BP consumer. | Dead addition, used-source removal, forged labels, `True`, enumeration, and `False` liveness mutants. Separate checked theorems reject or expose each mutant. | Candidate evidence satisfied; all three axiom inventories are green. |
| `REQ-03` | `ReviewerPhysicalStoreAdapter` makes the existing supplied-store evaluator read the caller's flat store at translated addresses. Refinement preserves value, cost, ordered successes/failures, repeated reads, and execution-derived footprint; footprint agreement determines the complete run. Projection equality proves physical `.value` is the translated supplied evaluator's `.value`, and a decisive consumed-word corruption changes that value. | Supplied flat store -> checked adapter -> existing whole-query evaluator -> physical trace/footprint/value -> guarded list consumer -> paper theorem. | Mapping a precomputed canonical value, ignoring the store, dropping failure/repetition order, or using a component slice. The evaluator/refinement theorem, projection identity, determinism, and six-part corruption witness exclude these. | Candidate evidence satisfied; theorem builds and executable projection-level corruption witness are green. |
| `REQ-04` | Exact propositions quoted above cover stored/returned words, all translated live/dead addresses, footprint addresses, input operands, segment/dead encodings, and every charged primitive operand/result. | Pre-execution `reviewerWordBits shape.size` -> physical list/address map -> physical trace -> adequacy record -> headlines. | A failed sentinel outside the width or a primitive using a larger operand. Universal address and event theorems include both. | Candidate evidence satisfied; WordRAM and headline inventories are green. |
| `REQ-05` | Capacity is definitionally `400000*(n+1)`; physical length is bounded by it; width is `<= 20*(log2(n+2)+1)` and is sufficient for input/store/dead addresses. | Input size -> linear capacity -> `machineWordBits capacity` -> whole physical execution. | Polynomial-only capacity or unconstrained `LittleOLinear machineWordBits`; neither is used. | Candidate evidence satisfied; full local gate is green. |
| `REQ-06` | Final adequacy contains operational manifest connections, every-read evidence, exact erasure, physical refinement, `.value` provenance, footprint, backing, capacity/width, and determinism. The List story exposes raw adequacy only under `ValidRange`; its invalid branch is one pure-none/empty/zero packet for every supplied store. The paper theorem and headlines consume both branches and all load-bearing semantics. | ReviewerPhysical -> RAM evaluator branches -> StoreParam adapter/execution -> ModelAdequacy -> guarded SuccinctRMQClassic story -> `RMQ.Headlines.RMQ` -> `RMQPaper`. | Unconditional raw adequacy inside an all-input packet, aggregate inequality substituted for answer dependency, sibling objects, or label-only liveness. The strengthened record, guarded story, direct paper conjunction, and curated inventories reject these. | Candidate evidence satisfied; `RMQPaper`, headlines, all inventories, and full local gate are green. |
| `REQ-07` | README, artifact guide/claims, family/what-is-proved, paper theorem/model/claim maps, trust/Word-RAM packets, roadmap, digestion/provenance, and both claim policies identify `328` as canonical transitional and `118`/`4144`/zero-block/`196727` as compatibility/history. Roadmap says candidate evidence only. | Checked theorem -> public docs -> roadmap candidate boundary -> claim-drift policy. | Stale current-`4144` prose or `Status: complete`; corrected in live sections. | Candidate evidence satisfied; claim-drift scan reports 493 reviewed hits and 0 strict failures. |
| `REQ-08` | Existing canonical exactness/no-synthetic/`328` theorems remain; the physical value is computed by the existing evaluator through `ReviewerPhysicalStoreAdapter`; the universal projection theorem and decisive corruption witness establish supplied-store answer dependency with exact quantifiers. | Canonical directory -> all-size close/LCA -> supplied logical evaluator through flat adapter -> physical execution -> guarded list query. | Ready/Active/zero-block dispatch, answer table, padded event, precomputed logical-value remapping, aggregate-only disagreement, or appended payload. None occurs in the canonical chain. | Candidate evidence satisfied; dependency, hygiene, and full integrated local gates are green. |
| `W17-RANGE` | `SuccinctClassic.withValidRange` is the single list-facing boundary used by canonical, supplied-store, trace, costed, prepared, and physical surfaces. The invalid packet proves logical/physical `none`, empty traces/footprint, zero cost, and pure `none` for every supplied store. | `ValidRange xs left right` -> controller thunk or pure `none` -> every public List execution projection. | `[9,8,7] 1 1`, a reversed window, or an end beyond length returns `some`; theorems and per-projection executable mutations reject all three. | Candidate evidence satisfied; examples, validator, and cost harness are green. |
| `W17-EXAMPLES` | `RMQExamples/Concrete.lean` and validation use semantic checks: valid same/cross-block, invalid ranges, exact `328`, route classification, exact erasure, physical backing, decisive corruption, and raw/guarded invalid mismatch. | Public list/physical surfaces -> executable theorem examples, `#guard`, and differential harness. | Refreshed hard-coded bit positions, legacy route labels, or aggregate-only corruption. None remains. | Candidate evidence satisfied; 498-window validator and the cost harness are green. |

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

### W17 semantic-gate amendment: current acceptance-matrix format

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-02.a` | Every emitted read maps to a counted operational source. | Local and public | For every read event in the actual whole-query trace, produce source, leaf, instruction, source/leaf segment equalities, `Counted`, `Live`, operational ownership, closed-program membership, and actual evaluator-branch equality. | Historical W17 chain: static segment map -> category-matching instruction. | W17 selected an arbitrary instruction with the same category and used an arbitrary state; it did not retain event membership in that instruction's actual trace. | Historical W17 theorem `...read_operational_source`, quoted below. | **W17 REPAIR_REQUIRED.** Superseded by the W18 producer-provenance row below. |
| `REQ-02.b` | Every counted source reaches an actual read-producing evaluator leaf or a checked shared-BP consumer. | Local and public | From `source.Counted`, produce either checked shared-BP dependency plus an instruction/branch equality, or segment-derived ownership plus an instruction/branch equality. Separately quantify over all select, rank, and canonical-close shared-BP consumers. | Historical W17 chain: counted source -> static category -> category-matching evaluator. | W17 did not prove an actual possible read event. Its shared-BP proof could combine source segment `0` with an unrelated leaf witness at segment `20`. | Historical W17 category theorems, quoted below. | **W17 REPAIR_REQUIRED.** Superseded by W18 may-read and same-event shared-BP rows below. |
| `REQ-02.c` | A separately hand-written consumer label is not sufficient evidence; legacy duplicates remain compatibility-only. | Local and public | Consumer claims require an operational leaf witness; legacy-close exclusion and compatibility-tail `none` remain checked. | Segment source/leaf maps -> `CheckedConsumerClaim` -> derived compatibility label; canonical manifest -> physical layout -> paper story. | Forge a consumer label distinct from the derived one. `...forged_consumer_rejected` proves the forged `CheckedConsumerClaim` is impossible. A label-only `consumer?` equality is deliberately absent from final adequacy. | `...ReviewerSource_forged_consumer_rejected`, `...PhysicalSources_exclude_legacy_close`, and `...CanonicalReviewerReadStore_legacyTail_none`. | Candidate evidence satisfied; final local verification ledger green. |
| `REQ-06.a` | Final adequacy, List story, paper theorem, and headlines consume the operational manifest and supplied-store answer semantics for the same execution. | Public composition | Final adequacy fields contain both provenance directions and `.value` provenance; list story consumes raw adequacy only under `ValidRange`; paper theorem directly consumes the strong packet. | Historical W17 public chain consumed category-only liveness. | Removing the W17 category fields exposed that the public theorem did not require actual producer state/event evidence. | W17 focused builds were green but the proposition was insufficient. | **W17 REPAIR_REQUIRED.** Superseded by W18 public-consumption row below. |
| `REQ-06.b` | Curated inventories expose every load-bearing semantic declaration. | Verification | All three axiom scripts name load-bearing semantic declarations. | Historical W17 inventories printed category-only aliases. | A green axiom print cannot strengthen a weak proposition. | W17 inventory evidence was propositionally insufficient. | **W17 REPAIR_REQUIRED.** Superseded by W18 inventory row below. |
| `INV-VALUE-DEPENDENCY.a` | Returned values depend on actual charged supplied reads, not a semantic answer computed before the reads. | Local and public | Physical `.value` equals the existing supplied-store evaluator `.value` after translation; differing translated evaluator values imply differing physical values, with exact quantifiers. | Physical store -> checked adapter -> existing supplied-store evaluator -> flat physical `.value` -> valid list wrapper -> paper theorem. | Substitute the canonical value while retaining the supplied trace. The validation mutant does exactly this and is separated from the real execution at `.value` by the decisive corruption. Aggregate record inequality is not used in final adequacy or headlines. | Two universal projection theorems plus valid list wrappers, quoted below. | Candidate evidence satisfied; final local verification ledger green. |
| `INV-VALUE-DEPENDENCY.b` | Include a nontrivial decisive corruption witness without claiming every read is decisive. | Executable kernel evidence | One valid query consumes an address whose changed word changes `.value`; separately check consumption and store disagreement. | Singleton canonical physical store -> address `7` -> supplied evaluator -> public physical answer. | Ignore the supplied returned value: mutant remains `some 0`, while actual dropped-word execution is `none`. Six separate `#guard`s check canonical value, corrupted value, consumption, changed store word, mutant value, and real-vs-mutant value inequality. | `RMQ/Validation/SuccinctClassic.lean`; focused validation and RMQExamples builds green. | Candidate evidence satisfied; final local verification ledger green. |
| `INV-PUBLIC-COMPOSITION.a` | Raw adequacy may appear only under a valid-range premise. | Public | `ValidRange xs left right -> FinalTraceModelAdequacy (cartesianShape xs) left right`. | `withValidRange` -> `flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid` -> paper main theorem. | Mix unconditional raw adequacy into the invalid branch. `invalidEmptyRawPhysicalResult.value != invalidEmptyPublicPhysicalResult.value` is kernel-checked, so the mutant describes a different execution. | Exact valid theorem quoted below; raw/public mismatch guard passes. | Candidate evidence satisfied; final local verification ledger green. |
| `INV-PUBLIC-COMPOSITION.b` | Every invalid input has one guarded result/trace/cost/footprint/supplied-store execution. | Public | Under `Not (ValidRange xs left right)`: logical and physical results are pure `none`, cost is pure `none` (zero), footprint is `[]`, and every supplied store yields pure `none`. | One validity boundary -> guarded logical and physical wrappers -> list story -> paper theorem/headline. | Mutate each semantic projection separately: result to `some 0`, trace to a synthetic event, cost to `1`, footprint to `[0]`, or supplied-store result to `some 0`. Five separate guards reject the five mutations. | `flatPayloadStoreNoSyntheticExecutionStory_invalid_semantics`, quoted below, plus five guards. | Candidate evidence satisfied; final local verification ledger green. |
| `INV-PUBLIC-COMPOSITION.c` | Space, erasure, execution, and semantics concern the same construction. | Public | The same `xs` and `cartesianShape xs` occur in `buildPayload`, exact physical erasure, guarded physical result, adequacy, width, and paper conjunction. | `buildPayload xs` = canonical payload <- physical-word erasure -> adapter-backed evaluator -> guarded story -> paper theorem. | Replace physical words by a sibling payload or pad to equality. Exact erasure would fail; no padding edit exists. Replace guarded execution by raw invalid evaluator: raw/public mismatch guard fails. | Existing exact erasure plus strengthened story/paper theorem. | Candidate evidence satisfied; final local verification ledger green. |
| `W17-VALIDITY.a` | Empty range returns `none` with empty/zero execution. | Executable and theorem | Instantiate the complete invalid packet at `[9,8,7] 1 1`. | Public validity boundary -> all projections. | Raw-invalid substitution and five per-projection mutations above are rejected. | `RMQExamples/Concrete.lean` full packet example and validation guards. | Candidate evidence satisfied; final local verification ledger green. |
| `W17-VALIDITY.b` | Reversed range returns `none` with empty/zero execution. | Executable and theorem | Instantiate the physical-result invalid conjunct at `[9,8,7] 2 1`; general theorem covers every projection/store. | Same guarded packet. | Reversed query returning any `some` value contradicts `queryCosted_reversed_range` and the packet. | RMQExamples theorem example and existing guard. | Candidate evidence satisfied; final local verification ledger green. |
| `W17-VALIDITY.c` | Out-of-bounds range returns `none` with empty/zero execution. | Executable and theorem | Instantiate the footprint-invalid conjunct at `[9,8,7] 0 4`; general theorem covers every projection/store. | Same guarded packet. | Nonempty footprint contradicts the packet; the `[0]` footprint mutant is rejected separately. | RMQExamples theorem example and existing guard. | Candidate evidence satisfied; final local verification ledger green. |
| `INV-SEMANTIC-NONVACUITY` | Semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction they describe. `True`, membership restatement, or a separately hand-written consumer label is insufficient. | Inherited invariant | Occurrence-level producer state/event evidence, same-event source/path evidence, reverse may-read construction, projection-level value identity, guarded object identity, and per-subclaim mutation failures. | Closed program/read trace -> producer occurrence -> operational manifest -> adapter-backed physical evaluator -> guarded list story -> paper main theorem. | W17's category join passed while failing to identify the producer occurrence/state; its dead/label mutations did not target this defect. | The old theorem types below document the failed candidate. | **W17 REPAIR_REQUIRED.** Superseded by W18 actual-producer and fresh-unused-source mutation rows below. |

### Historical W17 theorem types rejected by the producer audit

The following declarations remain compatibility facts, but the coordinator
found that they do not establish producer provenance.  They are not the
load-bearing W18 evidence.

```lean
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_iff_live
    (source : ReviewerSource) :
    source.Counted ↔ source.Live

theorem concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_read_operational_source
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    ∀ {segment index : Nat} {word? : Option WordRAM.Word},
      WordRAM.TraceEvent.readWord segment index word? ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace →
        ∃ source : ReviewerSource,
        ∃ leaf : ReviewerReadLeaf,
        ∃ instr : WholeQueryInstr,
          concreteBPNativeSuccinctRMQReviewerSegmentSource? segment =
              some source ∧
          concreteBPNativeSuccinctRMQReviewerSegmentLeaf? segment =
              some leaf ∧
          source.Counted ∧ source.Live ∧
          source.OperationallyOwnedBy leaf ∧
          instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
          instr.reviewerReadLeaf? = some leaf ∧
          WholeQueryInstr.reviewerReadLeafEvaluatorBranch
            shape left right WholeQueryState.empty leaf instr
```

```lean
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_evaluator_connection
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (source : ReviewerSource)
    (hcounted : source.Counted) :
    (source = .sharedBPCode ∧
      ∃ consumer : ReviewerSharedBPConsumer,
      ∃ instr,
        consumer.Checked ∧
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some consumer.leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state consumer.leaf instr) ∨
    (∃ leaf : ReviewerReadLeaf,
      ∃ instr,
        source.OperationallyOwnedBy leaf ∧
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state leaf instr)

theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_evaluator_connection
    (shape : Cartesian.CartesianShape) (left right : Nat)
    (state : WholeQueryState) (consumer : ReviewerSharedBPConsumer) :
    consumer.Checked ∧
      ∃ instr,
        instr ∈ concreteBPNativeSuccinctRMQWholeQueryProgram ∧
        instr.reviewerReadLeaf? = some consumer.leaf ∧
        WholeQueryInstr.reviewerReadLeafEvaluatorBranch
          shape left right state consumer.leaf instr
```

```lean
theorem concreteBPNativeSuccinctRMQReviewerManifest_add_dead_rejected
    (manifest : List ReviewerSourceCandidate) :
    ¬ ReviewerSourceCandidate.ManifestSound (.dead :: manifest)

theorem concreteBPNativeSuccinctRMQReviewerManifest_remove_used_rejected
    (removed : ReviewerSource) :
    ¬ ReviewerSource.ManifestComplete
      (concreteBPNativeSuccinctRMQReviewerManifestWithout removed)

theorem concreteBPNativeSuccinctRMQReviewerSource_forged_consumer_rejected
    (source : ReviewerSource) (actual forged : ReviewerConsumer)
    (hactual : source.consumer? = some actual)
    (hforged : forged ≠ actual) :
    ¬ source.CheckedConsumerClaim forged

theorem concreteBPNativeSuccinctRMQReviewerManifest_vacuousLive_accepts_dead :
    ReviewerSourceCandidate.VacuousLive .dead

theorem concreteBPNativeSuccinctRMQReviewerManifest_enumeration_accepts_dead
    (manifest : List ReviewerSourceCandidate) :
    ReviewerSourceCandidate.Enumerated (.dead :: manifest) .dead

theorem concreteBPNativeSuccinctRMQReviewerManifest_falseLive_rejected :
    ¬ (∀ source : ReviewerSource, source.Counted ↔ False)
```

```lean
theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_value_eq_suppliedStoreEvaluator
    (shape : Cartesian.CartesianShape) (physicalStore : WordRAM.ReadStore)
    (left right : Nat) :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape physicalStore left right).value =
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter
          shape physicalStore)
        left right).value

theorem concreteBPNativeSuccinctRMQWholeQueryFlatPhysical_value_ne_of_suppliedStoreEvaluator_value_ne
    (shape : Cartesian.CartesianShape) (storeA storeB : WordRAM.ReadStore)
    (left right : Nat)
    (hneq :
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeA)
        left right).value ≠
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
        shape
        (concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter shape storeB)
        left right).value) :
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape storeA left right).value ≠
    (concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore
      shape storeB left right).value
```

```lean
theorem flatPayloadStoreNoSyntheticExecutionStory_rawAdequacy_of_valid
    (xs : List Int) (left right : Nat)
    (hvalid : ValidRange xs left right) :
    SuccinctFinal.ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy
      (cartesianShape xs) left right

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
          WordRAM.TraceResult.pure none
```

### W18 producer-provenance repair

The W18 propositions below supersede the rejected W17 category joins.  The
accepted physical store, value-dependency, invalid-range, space, width, and
uniform-`328` evidence is unchanged.

| ID | Repaired exact requirement | Operational evidence and consumer chain | Counterfactual / falsifier | Evidence obtained | Status |
| --- | --- | --- | --- | --- | --- |
| `REQ-02.a` | Every emitted whole-query read exposes the actual instruction occurrence, the actual state produced by folding the exact preceding program prefix, and membership of that same event in that instruction evaluation.  The same event resolves to its physical source, region, logical segment, leaf, and component read path. | `WholeQueryProgram.evalGlobalWordTrace_event_producer` -> `ProducesEvent.prefix_state` / `.event_mem_instruction_trace` -> `WholeQueryInstr.evalGlobalWordTrace_read_producer_path` -> `...read_producer_provenance` -> `...WholeQueryProducerProvenance_checked`. | Replacing `preState` by `WholeQueryState.empty`, selecting an arbitrary same-category instruction, or independently joining source/leaf facts cannot construct `ProducesEvent` or `ProducedReadBy`. | Exact producer theorem and compact proposition quoted below. | Candidate evidence satisfied; final W18 verification ledger green. |
| `REQ-02.b` | Every counted source has an actual possible attempted-read path in the concrete select/rank/LCA construction.  Producer ownership is relational, so segments `17`--`19` can be read by LCA or final rank. | `ReviewerProducerReadPath` -> `ReviewerSource.HasProducerMayPath` -> `...ReviewerSource_counted_producer_may_path` -> final adequacy -> list story -> paper theorem. | A counted source with only a static category label cannot produce the required event membership in a concrete component trace.  This is may-read, not a universal claim that every query reads every source. | `concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path`. | Candidate evidence satisfied; final W18 verification ledger green. |
| `REQ-02.b.shared` | Every select/rank/canonical-close BP consumer reaches the shared BP physical source through one event in its own concrete component path. | `ReviewerSharedBPConsumer.ProducerConnected` -> `...all_producer_connected` -> final adequacy/list/paper. | Joining source segment `0` to an unrelated leaf witness at segment `20` does not satisfy the same-event relation. | `concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected`. | Candidate evidence satisfied; final W18 verification ledger green. |
| `REQ-06.a` | Final adequacy, valid List Int story, paper theorem, and headline aliases consume actual producer provenance, counted-source may paths, same-event shared-BP paths, and the fresh-unused-source rejection. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy` -> `FlatPayloadStoreNoSyntheticExecutionStory` -> `listIntSuccinctRMQPaperMainTheorem` -> `RMQPaper`. | Removing any strengthened field makes the downstream constructor/conjunction fail; category-only headline aliases have been removed. | Focused source consumers and new public aliases are checked in Lean. | Candidate evidence satisfied; final W18 verification ledger green. |
| `REQ-06.b` | All curated inventories expose the actual-producer, reverse may-read, same-event shared-BP, fresh counterfactual, list projection, and strengthened paper declarations. | Core theorem -> List Int projection -> headline alias -> three curated axiom inventories. | Printing only the W17 category theorems no longer covers the load-bearing fields. | `scripts/axiom_check.lean`, `scripts/wordram_axiom_check.lean`, and `scripts/headline_axiom_check.lean` name every strengthened declaration. | Candidate evidence satisfied; final W18 verification ledger green. |
| `INV-SEMANTIC-NONVACUITY` | Operational evidence is obtained from instruction/program evaluation and concrete component traces, not from `True`, enumeration membership, static categories, or separately selected labels. | Actual program trace -> occurrence/prefix state -> instruction trace -> relational source/component path -> final adequacy/public theorem. | Fresh segment `21` with plausible `.canonicalClose` label is rejected because no instruction trace can emit it; its liveness is not defined as `False`. | `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer`. | Candidate evidence satisfied; final W18 verification ledger green. |

The occurrence-level public packet has the checked shape:

```lean
def ConcreteBPNativeSuccinctRMQWholeQueryProducerProvenance
    (shape : Cartesian.CartesianShape) (left right : Nat) : Prop :=
  forall {segment index} {word?},
    readWord segment index word? ∈ wholeQueryTrace shape left right ->
      exists source leaf instr preState before after,
        wholeQueryProgram = before ++ instr :: after /\
        preState = (evalGlobalWordTrace shape left right before empty).value /\
        source.ProducedReadBy
          shape left right instr preState segment index word? /\
        instr.reviewerReadLeaf? = some leaf /\
        ReviewerProducerReadPath shape leaf segment index word? /\
        source.Counted

theorem concreteBPNativeSuccinctRMQWholeQueryProducerProvenance_checked
theorem concreteBPNativeSuccinctRMQReviewerSource_counted_producer_may_path
theorem concreteBPNativeSuccinctRMQReviewerSharedBPConsumer_all_producer_connected
theorem concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer
```

Here `ProducedReadBy` includes the same event's source-map equality, physical
region equality, and membership in `instr.evalGlobalWordTrace ... preState`.
The segment-to-leaf function and W17 `Live`/`Checked` theorems remain only as
compatibility metadata and are absent from the load-bearing headline aliases.

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
The final candidate evidence for `REQ-01` through `REQ-08`, every inherited
invariant, every adversarial case, and `DEF-U3`/`DEF-M1`/`DEF-A1` satisfies the
worker gate. Remote workflow outcomes are inspected after pushing the exact
commit and reported outside this commit. `DEF-ACCEPTANCE` deliberately remains
coordinator-owned.

| Check | Result |
| --- | --- |
| Runtime-health identity and command probes | Pass: `git status --short --branch` 0.4 s; `git rev-parse HEAD` 0.4 s; branch `git rev-parse` 0.4 s; `git ls-remote --heads` 0.8 s; focused declaration `rg` 0.4 s; small `Get-Content` 0.5 s; first legitimate small `apply_patch` 3.4 s. No abnormal Git, read orchestration, or patch latency. |
| Focused ReviewerPhysical, RAM, StoreParam, ModelAdequacy, SuccinctClassic, headline, example, and validation builds | Pass in 191.3 s; no new linter warnings. |
| `lake build RMQPaper` | Pass in 6.2 s. |
| `lake build` | Pass in 32.1 s, 197-target graph. |
| `lake build RMQExamples` | Pass in 4.8 s, 187-target graph. |
| `lake env lean scripts/axiom_check.lean` | Pass in 142.4 s; load-bearing declarations printed with only expected Lean principles. |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass in 63.6 s. |
| `lake env lean scripts/headline_axiom_check.lean` | Pass in 67.4 s. |
| `lake exe rmq_succinct_classic_validate` | Pass in 7.6 s: 498 valid/invalid windows across 43 deterministic inputs. |
| `lake exe rmq_succinct_classic_cost_harness` | Pass in 20.5 s: invalid, same-block, and cross-block windows under exact canonical bound `328`. |
| Forbidden-token/Mathlib hygiene scan | No matches in 1.0 s. |
| `native_decide` / `Lean.ofReduceBool` scan | No matches in 0.2 s. |
| Canonical-claim stale wording scan | No current/paper-facing `4144`, unconditional U2-complete, or appended-sibling wording. |
| `git diff --check` | Pass in 0.2 s; only Windows line-ending notices. |
| `scripts/design_decision_check.ps1` | Final pass in 1.4 s across 26 changed files. |
| `scripts/claim_drift_scan.ps1` | Final pass in 1.9 s: 491 reviewed hits, 0 strict failures. |
| `powershell -ExecutionPolicy Bypass -File scripts\\gate.ps1` | Post-ledger `GATE PASS` in 226 s. |
| Local artifact reproduction | Not run: a direct `Get-Command bash` probe reported that Bash is unavailable after 8.0 s. The required remote Artifact Reproducibility workflow remains part of the post-push gate. |

Controlled status: candidate evidence only. Coordinator reconstruction and a
fresh blind exact-commit audit are the mandatory next consumer.

## W18 repair verification ledger

Historical worker status: `CANDIDATE_COMPLETE`. Coordinator disposition:
`REPAIR_REQUIRED`. A read-event value is connected to a producing instruction
and folded pre-state, but occurrence position and invocation parameters are not
retained, and the fresh unused source is rejected by a stronger relation than
the positive counted-source theorem. A fresh blind audit is deferred until W19
closes those rows.

| Check | W18 result |
| --- | --- |
| Exact branch/base | `codex/rmq-u2-producer-provenance` created from verified remote `origin/codex/rmq-u2-final-route` at `a96f40b12c42133260a3fe840ccf0e4d33dbda6b`. |
| Focused producer/physical build | Pass: `lake build RMQ.Core.SuccinctFinal.RAM.ReviewerPhysical RMQ.Core.SuccinctFinalRAM`. |
| Focused adequacy/List/headline/paper build | Pass: `lake build RMQ.Core.SuccinctFinalModelAdequacy RMQ.Core.SuccinctRMQClassic RMQ.Headlines.RMQ RMQPaper`. |
| `lake build` and `lake build RMQExamples` | Pass. |
| All axiom inventories | Pass: broad, WordRAM, headline, hub, archive, rank/select, BP navigation, and union-find; new producer declarations use only expected Lean principles. |
| Validator | Pass: 498 valid/invalid windows across 43 deterministic inputs; canonical same/cross routes, `328`, physical erasure/backing, and flat-store dependency checked. |
| Cost harness | Pass: valid answers agree; invalid windows are none/zero; all modeled costs are below the exact canonical bound `328`. |
| Forbidden-token/Mathlib hygiene | No matches in `RMQ`, `RMQExamples`, or `lakefile.toml`. |
| `native_decide` / `Lean.ofReduceBool` | No matches in `RMQ` or `RMQExamples`. |
| Design decision check | Strict pass across 27 changed files, with code and workflow decisions recorded. |
| Claim drift | Strict pass: 526 reviewed hits, 0 strict failures; policy JSON version 4 parses. |
| `git diff --check` | Pass; only expected Windows line-ending notices. |
| Aggregate repository gate | `GATE PASS` from `powershell -ExecutionPolicy Bypass -File scripts\\gate.ps1`. |

## W19 occurrence-level and closed-valid-reachability amendment

This amendment reopens and re-evaluates `REQ-02.a`, `REQ-02.b`, `REQ-06.a`,
`INV-SEMANTIC-NONVACUITY`, `INV-TRACE-EXECUTION`, and
`INV-PUBLIC-COMPOSITION`. Historical W15--W18 rows remain evidence about those
checkpoints; they are not the current proposition.

### Exact predicates, domains, and quantifiers

Common occurrence domain `D` is `ReviewerProducerClaim`, a pair of a logical
segment and a `ReviewerReadLeaf`. For `claim : D` and
`word? : Option WordRAM.Word`, the common operational relation is:

```lean
claim.HasClosedValidOccurrence word? :=
  exists (xs : List Int) (left right globalPos index : Nat),
    ValidRange xs left right /\
    closedGlobalTrace (Cartesian.shape xs) left right |>.trace[globalPos]? =
      some (.readWord claim.segment index word?) /\
    exists instrPos instr preState localPos invocation,
      ProducesEventAt ... globalPos instrPos instr preState localPos /\
      instr.InvokesReviewerRead left right preState invocation /\
      invocation.leaf = claim.leaf /\
      invocation.componentTrace (Cartesian.shape xs) |>.getElem? localPos =
        some (.readWord claim.segment index word?)
```

The accepted positive predicate is
`P claim := claim.HasSuccessfulClosedValidOccurrence`, i.e.
`exists word : WordRAM.Word, claim.HasClosedValidOccurrence (some word)`.
The mutation predicate is
`Q claim := claim.HasOperationalProducer`, i.e.
`exists word? : Option WordRAM.Word, claim.HasClosedValidOccurrence word?`.
They share domain `D` and the exact operational relation but are not
definitionally equal because `P` requires success and `Q` also permits failed
attempts. The checked bridge is:

```lean
ReviewerProducerClaim.hasOperationalProducer_of_successful :
  forall {claim : D}, P claim -> Q claim
```

Canonical-source coverage quantifies
`forall source : ReviewerSource, source.Counted -> exists claim : D,
segmentSource? claim.segment = some source /\ P claim`. Shared-BP coverage
quantifies `forall consumer : ReviewerSharedBPConsumer,
P consumer.producerClaim`. The fresh mutation tests the same `Q` at
`concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource.toProducerClaim` and
proves its negation. No component may-read, arbitrary state, or event-value
membership predicate appears in these load-bearing conclusions.

Forward provenance quantifies over every shape, query pair, global trace
position, segment, address, and optional returned word. From
`globalTrace.trace[globalPos]? = some (.readWord segment index word?)`, it
returns `ReviewerReadOccurrenceReceipt ... globalPos ...`. The receipt records
the same global position, program instruction position, exact prefix-folded
pre-state, component-local position, exact `ReviewerReadInvocation`, source,
region, component event, and the multiplicity-preserving equation
`globalPos = prefixTrace.length + localPos`.

### Reopened-row ledger

| Row | W19 proposition/evidence | Anti-vacuity check | W19 worker status |
| --- | --- | --- | --- |
| `REQ-02.a` | `WholeQueryProgram.evalGlobalWordTrace_getElem?_producer` -> `WholeQueryInstr.evalGlobalWordTrace_getElem?_read_invocation` -> `concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`. | Equal event values cannot erase positions: `repeated_equal_read_occurrences_have_distinct_receipts` returns both receipts, and the singleton validator checks identical successful events at distinct global positions `0` and `12`. | Candidate evidence satisfied. |
| `REQ-02.b` | `concreteBPNativeSuccinctRMQReviewerSource_counted_successful_closed_valid_occurrence`; exact shared-BP theorem `...ReviewerSharedBPConsumer_successful_closed_valid_occurrence`. | Every witness includes ordinary `xs`, `ValidRange`, an indexed event in the actual closed whole-query trace, exact invocation, and successful `some word`; direct component may-read cannot inhabit this proposition. | Candidate evidence satisfied. |
| `REQ-06.a` | The parameterized `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right` consumes indexed occurrence provenance for that exact trace. The separate non-parameterized `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` consumes counted-source reachability, shared-BP reachability, the checked `P -> Q` bridge, fresh-source rejection, and manifest structure. `listIntSuccinctRMQPaperMainTheorem` consumes the global packet once and keeps raw trace adequacy plus occurrence provenance under the current `ValidRange`. W18 event-value facts remain compatibility-only. | Removing the indexed receipt breaks the current-query packet. Removing a reachability theorem, bridge, or fresh rejection breaks the global packet. No conclusion with an unused current-query validity premise remains. | Candidate evidence satisfied after W19 composition repair. |
| `INV-SEMANTIC-NONVACUITY` | Positive `P` and mutation `Q` share `HasClosedValidOccurrence`; checked `P -> Q`; fresh segment `21` proves `not Q`. | The negative is not an arbitrary-state or stronger unrelated predicate. Every accepted source has top-level successful execution evidence. | Candidate evidence satisfied. |
| `INV-TRACE-EXECUTION` | The forward theorem starts from `getElem?` in the actual closed global trace and carries instruction/local positions and computed invocation parameters. The reverse theorem also starts from that same actual closed evaluator. | Event-value `List.Mem`, arbitrary instruction state, and erased-parameter leaf paths remain insufficient compatibility facts. | Candidate evidence satisfied. |
| `INV-PUBLIC-COMPOSITION` | Query path: `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy shape left right` -> valid `List Int` raw adequacy and indexed occurrence -> paper theorem. Global path: `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` -> one top-level paper conjunct. Both flow through `RMQ.Headlines.RMQ` to `RMQPaper`; curated inventories name both. | The split prevents a global existential witness from masquerading as liveness of every current query. `SuccinctRMQClassicProvenance` remains proof-only, so native executables import neither symbolic witness family. | Candidate evidence satisfied after W19 composition repair. |

### Source-family evidence

The authoritative source split is:

| Family | Sources | Formal evidence |
| --- | --- | --- |
| Small closed-valid witnesses | 1--11 and 20 | `ReviewerReachabilitySmall.lean`, including the singleton and increasing-length-16 executions. |
| Symbolic long-super witness `L` | 12--15 | `ReviewerReachabilityLong.lean`; a kernel-safe `N = 2^15` shape proves the long-super arithmetic and successful segments 9--12 symbolically. |
| Symbolic sparse-local witness `S` | 16--19 | `ReviewerReachabilitySparse.lean`; the `N = 2^128` shape proves the sparse-local arithmetic and successful segments 13--16 symbolically without materializing the list. |

The scout report at exact commit
`17287f25d1241ab6e4609f19863eced66dd9e62b` was audited design input only. Its
table supplied the corrected split above; its prose summary error and its L/S
arithmetic were not treated as proof evidence or as a contract amendment.

### Preserved rows and next consumer

Genuine supplied flat-physical execution, one public payload and exact erasure,
invalid-range none/empty/zero semantics, logarithmic reviewer width,
no-synthetic trace, and the checked canonical transitional bound `328` are
unchanged. No threshold, category join, decorative read, component-only
liveness endpoint, or U3 work was introduced.

Controlled status remains candidate evidence only. Coordinator reconstruction
and a fresh blind exact-commit audit are the mandatory next consumers before
`ACCEPTED`.

### W19 final local verification ledger

| Check | Result |
| --- | --- |
| Exact branch base | Verified `HEAD = af8791150b64038e9c0776e3639634f1d83518ea` before editing in the isolated W19 worktree. |
| Focused occurrence/reachability/adequacy/List/headline/paper/validation build | Pass for `ReviewerPhysical`, `SuccinctFinalRAM`, all four `ReviewerReachability*` modules, `SuccinctFinalModelAdequacy`, `SuccinctFinalSemanticProvenanceAdequacy`, `SuccinctRMQClassic`, `SuccinctRMQClassicProvenance`, `RMQ.Headlines.RMQ`, `RMQPaper`, and both validation modules. |
| `lake build RMQPaper` | Pass. |
| Full `lake build` | Pass. |
| `lake build RMQExamples` | Pass. |
| Eight curated axiom inventories | Pass: headline, hub, WordRAM, broad, archive, rank/select, BP navigation, and union-find. W19 declarations report only the repository-standard `propext`, `Classical.choice`, and `Quot.sound` where applicable. |
| `lake exe rmq_succinct_classic_validate` | Pass: 498 valid/invalid windows across 43 deterministic inputs, including route, exact `328`, erasure, backing, dependency, and repeated-equal-event structural evidence. |
| `lake exe rmq_succinct_classic_cost_harness` | Pass: all invalid, same-block, and cross-block windows agree with reference `List Int` semantics and remain below exact canonical bound `328`. |
| Strict design-decision check | Pass across 34 changed files. |
| Strict claim-drift scan | Pass: 544 classified hits, 0 strict failures. |
| Prohibited-token and `native_decide`/`Lean.ofReduceBool` scans | No matches across live RMQ, example, paper, facade, archive, and lake roots. |
| `git diff --check` | Pass. |
| `scripts/gate.ps1` | `SHIM LINT PASS`; `GATE PASS`. |

### W19 claim-policy gate-effectiveness amendment

Frozen on 2026-07-14 before implementation from exact checkpoint
`82406d93ae18e9cfc5fab6823286adb4d738d5c6`. This amendment is a
proof-independent workflow/tooling leaf: it changes no Lean proposition and
preserves every previously checked U2 invariant. Its downstream join is the
actual strict verdict used by the focused regression, aggregate gate, and CI.

| ID | Exact frozen requirement | Evidence needed | Named consumer / composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- |
| `POLICY-01` | Test the final strict-policy verdict, not merely whether the raw forbidden regex matches. The regression must exercise the same pattern, allowance, path, and strictness logic used by `claim_drift_scan.ps1`. | Each fixture must be passed to `claim_drift_scan.ps1 -Strict`; must-reject cases require its strict forbidden-term failure and nonzero exit, while must-accept cases require exit zero. The policy-path allowance must also be exercised through that scanner. | Policy JSON -> scanner matching and path/line allowance -> strict failure count -> regression exit -> gate/CI. | Make the raw regex match but add a line allowance; a raw-match test would incorrectly reject while the required strict verdict accepts. The final-verdict run also found that one-file `rg` output omitted the filename and the scanner silently dropped ordinary matches. | `claim_drift_policy_regression.ps1` launches the real scanner in a child process for every fixture, checks nonzero plus the forbidden `[fail]` label for rejection, checks exit zero plus `[allowed]` where applicable, and separately exercises both exact path allowances. `claim_drift_scan.ps1` now uses `rg --with-filename`, preserving `file:line:text` for one-file scans. | Closed. |
| `POLICY-02` | Reject at least the existing five positive fixtures plus:<br>- "The canonical execution's activation premise is 2^128."<br>- "The canonical execution is activated at 2^128."<br>- "The canonical reviewer route uses a 2^128 activation threshold."<br>- equivalent exponent-first and spaced forms. | The focused regression must receive nonzero final strict verdicts, specifically from `forbidden-2pow128-canonical-activation`, for every listed misuse and both exponent spellings/directions. | Fixture -> actual scanner -> strict term -> regression -> gate/CI. | Reorder possessive, activated-at, threshold, exponent-first, and spaced forms; all must still fail. | Pass: 13 must-reject fixtures all receive the actual scanner's forbidden-term `[fail]` classification and nonzero strict verdict, covering the existing five plus possessive, activated-at, threshold, exponent-first, and spaced variants. | Closed. |
| `POLICY-03` | Accept at least the existing truthful fixtures plus:<br>- noncanonical and non-canonical execution wording;<br>- "It is not true that the canonical execution uses 2^128 as an activation premise.";<br>- explicitly historical, compatibility, and proof-only witness roles. | The actual strict scanner must exit zero for every truthful fixture. Role-scoped cases that match the suspicious detector must be accepted only by narrow, explicit line/path allowances. | Fixture -> same scanner pattern -> explicit role allowance or no suspicious canonical token -> zero strict failures. | Use `noncanonical`, `non-canonical`, scoped negation, historical, compatibility, and proof-only prefixes; no truthful fixture may fail. | Pass: 11 must-accept fixtures all receive exit zero. Direct/current negations, `not true`, historical, compatibility, and proof-only suspicious lines also report `[allowed]`; `noncanonical` and `non-canonical` do not become canonical-token matches. | Closed. |
| `POLICY-04` | Make strict violations gate-effective. `scripts/gate.ps1` and CI must not permit a strict claim-policy violation to remain advisory-only. Avoid duplicating independent policy logic between the scanner and regression test. | `gate.ps1` must invoke the regression and repository `claim_drift_scan.ps1 -Strict`; CI must invoke a strict claim scan, directly or through a blocking gate, with no advisory-only escape. Regression fixture classification must delegate to `claim_drift_scan.ps1 -Strict`. | Shared scanner -> focused regression + aggregate gate -> `.github/workflows/ci.yml` blocking steps. | Insert a forbidden fixture that the raw detector finds; both focused regression and aggregate/CI configuration must reject it. | `gate.ps1` invokes both the delegating regression and `claim_drift_scan.ps1 -Strict`; full gate passes. CI's blocking `Run strict claim-drift scan` step invokes `claim_drift_scan.ps1 -Strict`, while its earlier repository-gate step independently consumes the same strict scan. No second classifier exists. | Closed. |
| `POLICY-05` | Prefer a broad, token-bounded suspicious-claim detector plus narrow, explicit role allowances or another structured classifier over continued accretion of fragile negative lookarounds. Document this as a controlled claim-language lint, not a complete natural-language semantic checker. | Policy version must use one bounded canonical/exponent/activation token detector and anchored role allowances; human policy and WDD must state the lint's controlled-language scope and limitations. | Policy JSON -> scanner verdict -> reviewer-facing policy explanation and workflow rationale. | Vary grammar without changing the three suspicious token classes; detector must match. Use arbitrary natural-language paraphrase outside the controlled vocabulary; docs must not claim completeness. | Policy version 9 uses one 240-character three-token detector and anchored negation/history/compatibility/proof-only allowances; `CLAIM_DRIFT_POLICY.md` and WDD-20260713-005 explicitly call it a controlled claim-language lint, not unrestricted semantic analysis. | Closed. |
| `POLICY-06` | Update `CLAIM_DRIFT_POLICY.md`, its JSON version/date, the W19 acceptance ledger, and `WORKFLOW_DESIGN_DECISIONS.md`. Record the fixture-overfitting/gate-scope failure, rejected alternatives, and publication-facing reasoning. | All named files updated coherently with exact final evidence and the reason a strict publication-claim tripwire must block gate/CI. | Implemented scanner/gate/CI truth -> policy docs -> WDD -> this matrix. | Leave version/date stale, retain the checkpoint's five-fixture claim, or omit the publication-facing consequence. | JSON is version 9 dated 2026-07-14; the human policy, this ledger, and WDD record raw-regex fixture overfitting, one-file parser scope, advisory gate/CI scope, rejected duplicate/negative-lookaround/fixture-only alternatives, and the publication claim boundary. | Closed. |

Requested verification rows:

| ID | Exact check | Required outcome | Evidence obtained | Status |
| --- | --- | --- | --- | --- |
| `POLICY-CHK-01` | `claim_drift_policy_regression.ps1` | Every must-reject fixture gets the actual strict failure verdict; every must-accept fixture gets the actual strict pass verdict. | Pass: 13 reject, 11 accept, and 2 exact-path allowance verdicts. | Closed. |
| `POLICY-CHK-02` | `claim_drift_scan.ps1 -Strict` | Exit 0 with zero strict failures. | Pass after final POLICY evidence update: 576 classified hits, 0 strict failures. | Closed. |
| `POLICY-CHK-03` | `design_decision_check.ps1 -Base 82406d93ae18e9cfc5fab6823286adb4d738d5c6 -Strict` | Exit 0. | Pass across 8 changed files. | Closed. |
| `POLICY-CHK-04` | `git diff --check` | Exit 0. | Pass after final POLICY evidence update. | Closed. |
| `POLICY-CHK-05` | full `scripts/gate.ps1` | Exit 0 after running both the focused mutation regression and repository strict claim scan. | Final-tree pass in 305.1 s; focused verdict suite, repository strict scan, and `GATE PASS` all present. | Closed. |
| `POLICY-CHK-06` | verify the relevant CI invocation is strict | CI YAML contains a blocking `claim_drift_scan.ps1 -Strict` invocation and the aggregate gate also runs strict. | Pass: `.github/workflows/ci.yml` gives `./scripts/claim_drift_scan.ps1 -Strict` its own blocking `Run strict claim-drift scan` step, so no later command can overwrite its exit status; `scripts/gate.ps1` independently invokes the strict scan. | Closed. |
| `POLICY-CHK-07` | verify local and remote HEAD match | After commit/push, both resolve to the same exact SHA and the worktree is clean. | Pass after the implementation push: clean worktree; local `HEAD` and `origin/codex/rmq-u2-positional-provenance` both resolved to `c3d1c57dbea88b0433128fe50ace08cedf84445f`. The ledger-only follow-up is verified again in the final handoff. | Closed. |

### W19 category-level `2^128` policy-semantics amendment

Frozen on 2026-07-14 before implementation from exact checkpoint
`c3c3b51b216c9c01be20dca46e8acfc6872e7d57`. This is a
proof-independent workflow/tooling amendment. It changes no Lean proposition,
preserves all accepted W19 occurrence/reachability evidence, and joins at the
production scanner's final strict verdict as consumed by the focused
regression, aggregate gate, and blocking CI steps.

| ID | Exact frozen requirement | Evidence needed | Named consumer / composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- |
| `POLICY-R1` | Replace the three-token detector with a broad two-token suspicion boundary: any bounded line containing standalone canonical execution/route/query language and 2^128 is suspicious. Do not require a third activation/premise/threshold word. Narrow explicit role allowances should determine whether the suspicion is accepted.<br><br>The strict verdict must reject, among other equivalent statements:<br>- The canonical execution requires 2^128.<br>- The canonical reviewer route is available only at 2 ^ 128.<br>- The canonical query needs 2^128.<br>- 2^128 is required by the current canonical execution. | The production policy must detect a bounded line from only the standalone canonical-role and exponent token classes, with spaced/unspaced exponent support; every listed and category-level held-out misuse must receive the scanner's final strict failure verdict. | Policy JSON pattern -> `claim_drift_scan.ps1` classification -> focused regression -> aggregate gate and blocking CI. | Remove all activation/premise/threshold words and vary verbs, word order, reviewer modifier, and exponent spacing; every remaining canonical-role plus exponent line must still be suspicious. | Policy version 10 removes the third lookahead entirely. The production regression rejects all four stated lines plus threshold-free held-outs using `works`, `bounds`, and `mentions`; all are checked through scanner nonzero exit plus the strict forbidden-term `[fail]` classification. | Closed. |
| `POLICY-R2` | Preserve controlled truthful language. Support the existing accepted fixtures and ordinary explicit negations such as:<br>- The canonical execution's activation premise is not 2^128.<br>- The canonical route has no 2^128 activation threshold.<br>- Unlike the old theorem, no canonical execution has 2^128 as an activation premise. | Existing truthful fixtures and all three stated negations must receive final strict exit zero; suspicious canonical/exponent lines may pass only through explicit narrow line or role allowances. | Same policy pattern and allowance classifier -> production strict verdict -> regression/gate/CI. | Exercise direct `is not`, `has no`, prefixed `no canonical`, `It is not true that`, noncanonical token boundaries, and explicit historical/compatibility/proof-only roles; also exercise deceptive negative-looking positive claims that must remain rejected. | All 15 must-accept fixtures receive exit zero. Eleven suspicious cases also require `[allowed]`, covering the stated negations, exponent-first negation, historical note, compatibility companion, and proof-only witness; `noncanonical` and `non-canonical` remain outside the standalone token boundary. Clause-smuggling mutations with `no canonical` or `not true` before a forbidden second clause are rejected. | Closed. |
| `POLICY-R3` | Remove the whole-file acceptance-matrix bypass. If rejected examples must remain quoted there, use a checked conjunctive path-and-line context or an equally narrow explicit contract-row marker. A fresh positive canonical claim elsewhere in that file must fail. | The acceptance matrix must not match the ordinary whole-path allowance. Only the conjunction of its exact path and a frozen `POLICY-*` contract-row marker may allow quoted mutations. A fresh unmarked forbidden line inserted into that file must receive a nonzero final strict verdict. | Policy context fields -> production scanner's conjunctive allowance -> regression's shadow-file bypass mutation -> gate. | Place a fresh positive canonical/exponent claim outside a marked policy row in a temporary shadow tree at the exact acceptance-matrix relative path; scanning that exact relative filename must fail without modifying any tracked file. | The whole-file matrix path is absent from `allowedPathRegex`. New `allowedPathLinePathRegex` and `allowedPathLineRegex` fields require the exact W15 path and exact frozen policy-row marker together. The regression now creates a temporary shadow root containing `docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md`: a marked `POLICY-R3` row receives the conjunctive `[allowed]` verdict, while an unmarked forbidden line at the same relative filename receives the strict `[fail]` verdict. It resolves scanner and policy paths absolutely before changing the child scan working directory and checks git status plus tracked hash snapshots before and after the allowed and rejected shadow verdicts. | Closed. |
| `POLICY-R4` | Replace colon-splitting of ripgrep output with structured `rg --json` parsing so relative files, absolute Windows paths, paths containing colons, and single-file scans share one correct implementation. | The production scanner must parse `rg --json` match records, normalize absolute paths under the repository to policy-relative form, and apply the same final verdict logic for relative, drive-qualified Windows, colon-bearing, and single-file inputs. | `rg --json` -> one scanner record parser -> normalized policy path + original display path -> shared allowance/strict verdict. | Run a focused drive-qualified absolute-Windows single-file fixture containing a forbidden line and scan the marked acceptance matrix by absolute path; both must produce the same classifications as relative paths without parsing loss. | `claim_drift_scan.ps1` consumes `rg --json` match records, decodes text/byte fields, normalizes repository-local absolute paths, and never splits display text on colons. `-AbsoluteWindowsOnly` proves a drive-qualified single-file misuse fails and the absolute matrix path reaches the same conjunctive allowance as its relative form. | Closed. |
| `POLICY-R5` | Add category-level holdouts beyond the sentences above. The listed fixtures are minimum examples, not the acceptance boundary. Add a regression showing that a forbidden line inserted under the acceptance-matrix path is not accepted merely because of its filename. | The regression must include held-out verbs/orderings that follow only the two-token category boundary, negative-looking allowance-bypass mutations, and the acceptance-matrix filename mutation in a non-mutating shadow context. It must delegate every result to the production strict scanner. | Held-out/bypass fixtures -> production scanner final verdict -> regression summary -> aggregate gate. | Include category representatives not used to motivate grammatical branches plus lines that contain `not`, `historical`, or `compatibility` without occupying an explicitly allowed role; all must reject. | The 26 must-reject cases include category-level held-outs and six allowance-bypass mutations: `does not avoid`, `not optional`, irrelevant historical/compatibility prefixes, and two negated-first-clause smuggling attempts. The unmarked matrix-path mutation also fails in the temporary shadow tree at the exact relative filename, not by appending to the tracked matrix. Every verdict comes from the production scanner child process. | Closed. |
| `POLICY-R6` | Either retain CI's new strict design-decision check and log its rationale, rejected alternatives, and operational consequences, or revert that unassigned change. Update the WDD and acceptance ledger accordingly. | Choose exactly one disposition. If retained, CI must show a blocking strict base-relative design-decision invocation and the WDD must record why, rejected alternatives, and push/PR consequences; if reverted, the CI change must be absent. | Workflow decision -> `.github/workflows/ci.yml` -> base-relative changed-file classification -> blocking CI verdict -> WDD and this ledger. | Compare retaining an advisory check, folding it only into the aggregate gate without base context, reverting it, and keeping a separate blocking strict step. | Retained. CI has a separate `if: always()` strict design-decision step with PR-base fetch/compare and push `HEAD~1` compare; it has no advisory escape. WDD-20260713-005 records the publication-control rationale, rejected advisory/revert/gate-only alternatives, and the operational base-selection and failure-reporting consequences. | Closed. |

The completion-protocol amendment is also frozen: finite mutation fixtures are
lower bounds, not classifier/linter completeness evidence. Category-level
holdouts and allowance-bypass mutations must exercise the production final
verdict, and the completion gate, known-failure guidance, worker prompt, matrix
template, and WDD must state that rule and its publication-facing significance.

Non-mutating regression repair (2026-07-14, from exact checkpoint
`2dc0fb33ab4f59ece6b8ed8e3dba0d6fe526ea4a`): policy behavior is unchanged.
The focused regression no longer appends to or restores the tracked acceptance
matrix. It writes all ordinary fixtures under a temporary root, creates a
temporary shadow repository/root for the exact matrix-relative path, invokes the
production scanner and actual policy by absolute path from that shadow context,
and checks that tracked status plus hash snapshots are unchanged before and
after both the successful marked-row verdict and the deliberately failing
unmarked-line verdict. This records a test-harness repair only; it adds no Lean,
public-claim, policy-category, skill, roadmap, or workflow-process change.

Requested verification rows:

| ID | Exact check | Required outcome | Evidence obtained | Status |
| --- | --- | --- | --- | --- |
| `POLICY-R-CHK-01` | `claim_drift_policy_regression.ps1` | All category-level must-reject, must-accept, allowance-bypass, path-context, parser-shape, and non-mutating shadow-matrix fixtures receive the expected production final strict verdict. | Pass: 26 must-reject, 15 must-accept, and 5 path/context/bypass production verdicts. The marked shadow matrix row accepts, the unmarked shadow matrix line rejects, and tracked status/hash snapshots remain unchanged around both verdicts. | Closed. |
| `POLICY-R-CHK-02` | `claim_drift_scan.ps1 -Strict` | Exit 0 with zero unapproved strict failures in the repository. | Pass: 581 classified hits, 0 strict failures. | Closed. |
| `POLICY-R-CHK-03` | focused absolute-Windows-path scanner regression | A drive-qualified single-file misuse fails, and absolute scanning of the marked shadow matrix uses the same checked contextual allowance as its relative path. | Pass: `ABSOLUTE-WINDOWS PASS (2 production path verdicts)`; the drive-qualified misuse rejects, the absolute shadow-matrix context accepts, and tracked status/hash snapshots remain unchanged around both verdicts. | Closed. |
| `POLICY-R-CHK-04` | `design_decision_check.ps1 -Base c3c3b51b216c9c01be20dca46e8acfc6872e7d57 -Strict` | Exit 0. | Pass: `DESIGN-CHECK: checked 12 changed files`. | Closed. |
| `POLICY-R-CHK-05` | `git diff --check` | Exit 0. | Pass before the implementation checkpoint, on the ledger-only follow-up, and after the non-mutating regression repair. | Closed. |
| `POLICY-R-CHK-06` | full `scripts/gate.ps1` | Exit 0 after the production-verdict regression and repository strict scan; `GATE PASS` present. | Pass twice for the category-level implementation, and again after the non-mutating regression repair in 490.5 seconds. Builds and axiom inventories complete, the production regression passes with shadow-matrix tracked-state checks, repository strict scan reports zero failures, and `GATE PASS` is present. | Closed. |
| `POLICY-R-CHK-07` | verify blocking CI configuration | Repository gate, strict claim scan, and the chosen strict design-decision disposition are blocking, not advisory. | Pass: CI separately runs `./scripts/gate.ps1`, `./scripts/claim_drift_scan.ps1 -Strict`, and base-relative `./scripts/design_decision_check.ps1 ... -Strict`; none has `continue-on-error`, and the latter two `if: always()` steps still fail the job on nonzero exit. | Closed. |
| `POLICY-R-CHK-08` | verify clean local/remote matching HEAD | After the final ledger commit and push, the worktree is clean and local/remote branch SHAs are identical. | Implementation checkpoint pass: local and remote both resolved to `09459b460445f9c1cebb3994dbc1cb8f7c6de0fb`. The ledger-only follow-up is mechanically rechecked and reported at final handoff. | Closed. |

The first native executable replay exposed a Windows stack overflow caused by
placing symbolic proof-witness modules in the executable import/link closure.
An exact-base detached probe passed. The final proof/runtime module split is
therefore part of the accepted candidate design, and both exact executable
commands pass after that split; no environment or stack override is required.

### W19 global/per-query composition-repair verification ledger

| Check | Result |
| --- | --- |
| Exact continuation checkpoint | Verified branch `codex/rmq-u2-positional-provenance` at `e7278f66d87bd9f90bc9ba71a7107f67cbaa45e1` with a clean worktree before editing; no replacement branch was created. |
| Focused composition build | Pass for `SuccinctFinalRAM`, `ReviewerReachability`, `SuccinctFinalModelAdequacy`, `SuccinctFinalSemanticProvenanceAdequacy`, `SuccinctRMQClassic`, `SuccinctRMQClassicProvenance`, `RMQ.Headlines.RMQ`, and `RMQPaper`. |
| `lake build RMQPaper`; full `lake build`; `lake build RMQExamples` | Pass. |
| Three primary axiom inventories | Headline, WordRAM, and broad inventories pass; the current query raw/occurrence theorems and the non-parameterized manifest packet report only the repository-standard axioms. |
| Both SuccinctClassic executables | Pass. Validator checks 498 windows across 43 inputs; cost harness agrees with reference semantics and retains exact canonical bound `328`. Both roots still import only `SuccinctRMQClassic`. |
| Phantom-validity/global-liveness scan | No retired `_of_valid` source-liveness wrapper or parameterized semantic packet remains. The only `SuccinctFinalSemanticProvenanceAdequacy` code hit is the proof-only module import itself. |
| Strict design-decision check | Pass across 28 changed files. |
| Strict claim-drift scan | Pass: policy version 8, 565 classified hits, 0 strict failures; spaced/unspaced `2^128` remains role-classified, while canonical activation misuse is strict in either ordinary word order. |
| `claim_drift_policy_regression.ps1` | Pass: `rg --pcre2` rejects five canonical-activation mutations (`uses`, `requires`, `has`, exponent-first, and spaced/unspaced forms) and accepts five truthful role-scoped fixtures (three negations, compatibility companion, proof-only sparse-local `N = 2^128` witness). It is now invoked by `scripts/gate.ps1`. |
| Prohibited-token and `native_decide`/`Lean.ofReduceBool` scans | No matches in live `RMQ` / `lakefile.toml` scope. |
| `git diff --check` | Pass. |

## Coordinator final disposition

Disposition date: 2026-07-14.

- Exact accepted U2 target:
  `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`.
- Fresh blind audit report: A04 at
  `f5c2ab03a064e56f90a17574041cd116568416d8`.
- Final verdict: **ACCEPTED**. The coordinator independently reconstructed the
  object-identity, physical-execution, occurrence-provenance, word-width, cost,
  and public-consumption chains, then accepted A04's independent REQ-01 through
  REQ-08 verdict. The inherited invariants and adversarial cases are closed by
  the same checked evidence summarized in A04.
- A04's sole P3 finding concerned three stale comments in
  `SuccinctFinalRAM.lean`; the adjacent integration change corrects the prose
  without changing definitions, theorem statements, payloads, traces, or cost.
- Historical open, candidate, and repair-required rows above remain as a record
  of the acceptance campaign. This final disposition supersedes them only for
  the exact accepted target.
- U3 is the next active roadmap node. It may improve the explained constant but
  must preserve U2's one-payload physical execution and provenance chain.
