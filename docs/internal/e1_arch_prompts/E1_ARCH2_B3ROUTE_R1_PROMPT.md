Make the title of this chat exactly: (E1-ARCH2-B3ROUTE-R1) Construct and decide the full historical bounded route

Worker identity:
- Handle: E1-ARCH2-B3ROUTE-R1
- Requested title: `(E1-ARCH2-B3ROUTE-R1) Construct and decide the full historical bounded route`
- Fresh or returning worker: FRESH governed architecture/proof worker; the accepted B3 source port is a predecessor and exact base, not a returning task.

Skill:
- Use $rmq-proof-sprint before starting and apply its completion gate.
- Workflow-governance ref: a154983ae465b25ae6d8118b56abfa95ddf5b409.
- Before substantive work, run `scripts/project_skill_preflight.ps1` against that exact ref with `rmq-proof-sprint` required and the RMQ skill names actually shown in this task's runtime catalog. Stop on any absent/stale checkout skill, missing role skill, or ancestry mismatch. Do not substitute another skill or continue best-effort.

Checkout contract:
- Task mode: WRITE.
- Exact base/target commit: c19061629ce8cf1e78992a99346170edd84b4971, the independently accepted B3 source-port/interface commit. It already contains governance a154983ae465b25ae6d8118b56abfa95ddf5b409, accepted B1 1727de15f2030bfb9296a9b31508bc00581aa33a, accepted PREHIST 50c5f8ccf7be83a56b90a6c29142ac32860f0a27, and the accepted validation-local 56-module historical source port.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md.
- Create branch exactly `codex/e1-arch2-b3-historical-route-r1` in the fresh worktree and report its absolute path.
- Require exactly two commits after the base. Commit 1 is the contract freeze and changes only `docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md`. Commit 2 is the implementation and final evidence; do not amend, squash, rewrite, or add a third commit.
- Final range may change only `RMQ/Validation/E1Architecture/B3HistoricalRoute/*.lean`, `scripts/e1_arch2_b3_historical_route_replay.ps1`, `docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md`, `docs/internal/DESIGN_DECISIONS.md`, and `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`. Every non-owned blob must equal the exact base. Do not edit Core, the accepted B1 modules, the accepted B3SourcePort modules, public roots, or current-route work.

Roadmap contract:
- Node/join: E1 architecture gate B3 historical full-word route, consuming accepted B1/PREHIST and the accepted source-port/interface predecessor; its result feeds the later A4 selector alongside independently accepted B2 and B4 route verdicts.
- Local owned rung: one complete, checked full B3 historical bounded-route PASS or one quantifier-matched formal universal FAIL over the exact frozen allowed domain.
- Roadmap-node closure condition: B3 closes only after coordinator reconstruction of this exact two-commit candidate. A4 and E1 remain open until B2, B3, and B4 are all accepted and the selector is separately adjudicated.
- Goal: Construct and decide the full historical route on the identical accepted B1 image, using one shape-independent fixed ROM and an explicit bounded target execution that stutter-simulates the accepted historical source.
- Required theorem/file/tool: `HistoricalPASS acceptedB1 pinned` with a concrete witness and checked receipt, or `HistoricalFAIL acceptedB1 pinned` plus `historicalFail_iff_not_historicalPass` over the identical domain; implement under `RMQ/Validation/E1Architecture/B3HistoricalRoute/` with committed matrix and replay.
- Write scope: `RMQ/Validation/E1Architecture/B3HistoricalRoute/*.lean`; `scripts/e1_arch2_b3_historical_route_replay.ps1`; `docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md`; `docs/internal/DESIGN_DECISIONS.md`; `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`.
- Lifecycle dependency order: accepted B1 and PREHIST precede the accepted B3 source port; this worker freezes the target and six port-deferred choices before implementation, constructs the bounded ROM/read/width/simulation chain, then produces committed replay evidence; coordinator audit follows worker completion; only a separately accepted B3 verdict may later feed A4. No decision depending on this task gates its own launch, and no B4/A4/integration/publication work is authorized here.
- Current-surface inventory: NOT_APPLICABLE; this task adds validation-local architecture evidence and may not edit a current public claim surface.
- Current-source-comment inventory: NOT_APPLICABLE; no governed source-comment repair is in scope.
- Dependency-surface inventory: NOT_APPLICABLE; this task consumes rather than restores, renames, splits, or migrates a public identity.
- Non-goals: Do not accept or modify B1, B2, B4, A4, public RMQ claims, main, CI, or E1 closure. Do not push, merge, publish, or clean other worktrees.
- Explicitly deferred work: A4 deterministic selection, B4 total-Nat route, any B2 successor, integration, publication, and public architecture synchronization are downstream and are not required for this B3 verdict itself.

Acceptance contract:
- Frozen acceptance IDs: `B3-HIST-01-EXACT-B1-OBJECT`, `B3-HIST-02-FIXED-ROM-LITERAL-PROVENANCE`, `B3-HIST-03-EXPLICIT-PHYSICAL-READ-LOWERING`, `B3-HIST-04-DYNAMIC-WIDTH-CLOSURE`, `B3-HIST-05-SOURCE-STUTTERING-SIMULATION`, `B3-HIST-06-TRACE-CATEGORY-ROM-CORRESPONDENCE`, `B3-HIST-07-PARAMETERIZED-AND-PINNED-RECEIPT`, `B3-HIST-08-EXACT-PQ-VERDICT`, `COMPLETE-B3-HIST-COMMITTED-EVIDENCE`; inherited `E1-ARCH2-03-BOUNDED-WORD-IMAGE`, `E1-ARCH2-05-HISTORICAL-ROUTE`, `E1-ARCH2-07-SOURCE-STATE-SIMULATION`, `E1-ARCH2-08-COST-CATEGORY-INTEGRITY`; `INV-STORE-IDENTITY`, `INV-VALUE-DEPENDENCY`, `INV-SEMANTIC-NONVACUITY`, `INV-TRACE-EXECUTION`, `INV-STORE-AGREEMENT`, `INV-READ-BACKING`, `INV-WORD-WIDTH`, `INV-ADDRESS-WIDTH`, `INV-INSTRUCTION-ATOMICITY`, `INV-PROGRAM-ACCOUNTING`, `INV-ORACLE-INDEPENDENCE`, `INV-VALIDATION-REACH`, `INV-ALL-SIZE`, `INV-PROOF-SEPARATION`, `INV-NO-SYNTHETIC`, `INV-CATEGORY-SEPARATION`, `INV-PUBLIC-COMPOSITION`, `INV-GLOBAL-PHYSICAL-MACHINE`, `INV-WIDTH-SCALING`, `INV-CERTIFICATE-ANTI-BYPASS`, and `ARCH-CONTRACT-NO-ASSUMED-CAPSTONE`.
- Before any implementation edit, create and commit the matrix from `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`. Under one strict raw-Git UTF-8 decoder, copy the inherited architecture requirement rows byte-for-byte from exact blob `9eb1625a6023eb36bd2ceefdcc44396eb768f3c6` and the B3 contract, exact predicates, mandatory mutation registry, and stop conditions from accepted PREHIST report blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f`. Add exact local rows for every construction leaf, the six downstream port choices, replay controls, and final receipt. Freeze all IDs, requirement cells, predicate text, registries, fixture inputs, chosen constants, and expected surfaces as PENDING before implementation.
- Preserve every frozen row byte-for-byte from freeze to final outside explicitly delimited evidence and status fields. Use a strict UTF-8 raw-Git comparison, reject missing/duplicate IDs, and include a mojibake negative control.
- Read and apply `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.

Exact accepted inputs and target:
- Accepted source-port matrix blob is `4f8b3c84fbac5d8ef766b5d3df1c289c097fbeb3`. Its exact ordered 56-module registry, 5,646-instruction program, twelve constructor tags, declaration/interface correspondence, pinned fixture, fixed branch families, source PCs 1/5/7, and symbolic downstream obligations are immutable inputs. Consume them; do not duplicate or edit them.
- Freeze concrete values before implementation for all six port-deferred choices: `pinnedROMPC`, `pinnedTargetBranchPC`, `pinnedTargetArithmeticPhase`, `pinnedTargetSubPhase`, `pinnedMainRunReadIndex`, and `pinnedProvenUnreadImageAddress`. Each choice needs an exact in-range/execution theorem and an anti-vacuity consumer. Do not choose a target constant because it makes a proof easy; derive and record why it witnesses the named mutation surface.
- Freeze the ambient route domain as a concrete proof-free `HistoricalRouteCandidate` with a single semantic ROM, width-indexed canonical encodings, fixed tag-to-phase lowering, and public endpoint initialization. Target phase/state/instruction/decode/step/run definitions belong to B3 and are not route-supplied oracle fields. The route type must be manifestly inhabited independently of correctness.
- `AllowedHistoricalCore` must use the exact accepted B1 package for every shape, exactly its `.image` and `.width`, one semantic ROM independent of width/shape/query/image contents, canonical width-specific encoding which decodes to that identical ROM, and executable inputs limited to encoded ROM, exact image, left, and right. There is no runtime shape, proof callback, expected result, source program, sibling data object, or host-program inspection.
- Target instructions must expand the frozen twelve historical constructors into explicit charged bounded microsteps. No new primitive, semantic helper callback, hidden recursion, `List.find?`, `Nat.log2`, shape projection, or theorem-only answer is allowed. If constant-immediate arithmetic cannot be lowered without adding a primitive or changing atomicity/cost, stop with the exact checked architecture obstruction.
- Use the exact endpoint guard and reference packet from PREHIST. `EndpointFits package left right` is `left < 2^package.width ∧ right < 2^package.width`. `ReferencePacket shape left right` is the independent high-level value for valid half-open ranges and `none` otherwise. The public endpoints are inputs; the conditional reference is proof-only and may not drive execution.
- `buildHistoricalReceipt` must be a constructor from one actual recursive run. Package/image/ROM/query/initial/fuel/final/physical trace/categories/ROM fetches/logical trace/output/source program/source store/source initial state are definitional projections of the exact objects and run. No proof field may supply an answer, trace, category list, fetch count, or source state.
- `ParameterizedComplete` quantifies every shape and every machine-representable endpoint pair, including valid, reversed, empty, and out-of-bounds cases, and produces fuel and one halted receipt whose output is `ReferencePacket`. It must also close explicit physical-read lowering, all reachable width facts, source stuttering simulation, and exact trace/category/ROM correspondence on that same run.
- `PinnedComplete` uses the accepted source-port fixture: values `[8,6,7,5,3,0,9,1,4,2,6,6]`, query `[0,12)`, independently expected `some 5`, package width `24`, shared-size cell mutation `12` to `4`, historical source PCs 1/5/7, and the exact live/empty/dead/sentinel expressions from `PinnedFixture.lean`. The pinned receipt comes from the same parameterized constructor and exact accepted B1 package.
- Freeze `P acceptedB1 pinned route := AllowedHistoricalCore acceptedB1 route ∧ ParameterizedComplete acceptedB1 route ∧ PinnedComplete acceptedB1 pinned route`. Freeze `Q acceptedB1 pinned := ∀ route : HistoricalRouteCandidate, AllowedHistoricalCore acceptedB1 route → ¬ (ParameterizedComplete acceptedB1 route ∧ PinnedComplete acceptedB1 pinned route)`. Then freeze `HistoricalPASS := ∃ route, P ...` and `HistoricalFAIL := Q ...`, and prove `HistoricalFAIL acceptedB1 pinned ↔ ¬ HistoricalPASS acceptedB1 pinned` using the identical objects, guards, and quantifiers.

Required exact consumers:
- `B3-HIST-01`: receipt package is definitionally/propositionally the accepted historical route alias; executed image and width are exactly its projections.
- `B3-HIST-02`: one parameter-free semantic ROM; canonical encode/decode round trip and injectivity; total fixed source-PC lowering; every immediate occurrence is fixed code or related to named executed charged derivation steps. Prove all six downstream freeze choices are consumed.
- `B3-HIST-03`: every source logical read lowers to explicit descriptor count/offset/span, word-length, payload, sentinel, and dead physical image reads. Retain loaded addresses, cells, multiplicity, and order in the receipt; never call `package.executor`.
- `B3-HIST-04`: prove initialization and one-step preservation of a complete reachable-state invariant. Every reachable register, PC, ROM/image address, operand, arithmetic intermediate, decoded value, branch target, and result fits the one package width; prove subtraction order/no-wrap and complete image/ROM capacity.
- `B3-HIST-05`: phase-indexed base/step/final stuttering simulation for every reachable step of the exact closed historical program, then compose with accepted source agreement and independent public semantics. Derive result equality; never assume it.
- `B3-HIST-06`: preserve occurrence positions and multiplicity in physical trace concatenation and logical projection. Derive exact target instruction categories and ROM fetch counts from the run. Keep 210, 33, 11886, payload bits, descriptor bits, fixed-cell reads, instructions, ROM fetches, Lean runtime, and proof time in distinct categories.
- `B3-HIST-07`: prove the parameterized all-shape/all-representable-query theorem and one complete pinned concrete receipt over the same route and package. Add an independent expected-type consumer which pins the public proposition and exact object chain.
- `B3-HIST-08`: produce exactly one checked verdict. PASS requires a concrete `HistoricalPASS` witness. FAIL requires `HistoricalFAIL` and the exact iff bridge. If neither closes, report INCOMPLETE unless a quantifier-matched formal obstruction genuinely forces coordinator architecture judgment.

Mutation and replay contract:
- Inherit the complete mandatory mutation table from PREHIST blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f`, IDs `MUT-HIST-01` through `MUT-HIST-12B`, without removal or weakening. The exact registry must include accepted-package/image substitution; invalid/operand/padding/branch/literal/source-topology ROM mutations; shape callbacks/immediates; every count/offset/span/word-length/payload/sentinel/dead read mutation; opaque logical read; dormant operand/register/PC/branch/dead-address/arithmetic width and subtraction mutations; final-equality bypass; trace permute/drop/duplicate/synthetic/membership mutations; 11886 category substitutions; output/category/fetch decorations; Q-premise strengthening/domain narrowing; decisive backing-value mutation; and the proven-unread-cell expected-accept control.
- For the decisive backing-value case, freeze the exact image address, changed bit/cell, executed read occurrence, and named decisive branch or output projection. Both local runs use the identical route, ROM, query, initial state, fuel, and evaluator; only the one image cell differs. This case deliberately omits exact-package identity so it isolates value dependency. The unread control must prove address absence from the run footprint before accepting unchanged output/trace.
- Commit an exact ordered unique registry with explicit expected verdict and exact failing theorem/diagnostic for every case, an unchanged production expected-accept control, exact ID-to-object mapping, verdict counts, restoration, and final clean-tree check.
- `REPLAY-EXACT-REGISTRY`: reject missing, duplicate, reordered, or unmapped IDs; verify exact verdict counts and selectors.
- `REPLAY-SELECTOR-NONVACUITY`: omission alone may select the full registry; explicit empty/whitespace, unknown, and multi-ID selectors reject. Exercise omitted-middle, duplicated-middle, one valid ID, and unknown ID controls.
- `REPLAY-SUBPROCESS-DEADLINE`: every external Lean/Lake/Git subprocess has a positive evidence-based deadline, timeout is failure, owned process trees are terminated, and cleanup/live-tree checks run in `finally`. Add a cheap root-plus-descendant sleeper self-test with at least ten seconds and prove both are absent.
- The full replay must operate on committed raw-Git blobs at exact HEAD, enforce the exact two-commit chronology and path scope, compare frozen row bytes, verify immutable source-port identities, run all semantic mutations and expected accepts, restore every transform, and end with clean index/worktree/untracked state.

Forbidden shortcuts:
- No prose substitute for proof; no declaration-name inventory as execution evidence.
- No input-dependent code cell, sibling data object, runtime shape or proof value, target verdict callback, source-program inspection, expected-answer oracle, opaque logical load, or semantic helper disguised as one instruction.
- No proof-supplied trace/output/category/fetch field, post-hoc decorative read, synthetic event, membership-only trace claim, or theorem which bypasses actual step/run evaluation.
- No `Nat`-only fit theorem in place of bounded reachable-state closure. Array bounds do not prove address width.
- No reuse of historical 11886 as a bounded instruction/fetch/category result and no reuse of current 210 or local 33 across categories.
- Do not infer route existence from the R4 proposition-shape probe, from the accepted source port, or from a successful pinned fixture alone.
- No universal FAIL from one failed encoding, timeout, open theorem, resource limit, large term, or one rejected implementation.
- Do not stage transcripts, archives, build products, scratch files, or unrelated changes.

Context:
- Read `AGENTS.md`, `docs/internal/RMQ_FINAL_ROADMAP.md`, accepted PREHIST report blob `be80468ef049c0c94c7d1a7b3c5f8f69ccfd453f`, accepted architecture matrix blob `9eb1625a6023eb36bd2ceefdcc44396eb768f3c6`, and accepted source-port matrix blob `4f8b3c84fbac5d8ef766b5d3df1c289c097fbeb3`.
- Read the accepted B1 package and exact B3SourcePort root, manifest, topology, correspondence, and pinned fixture as immutable consumers.
- Read only relevant design/workflow decisions and task-specific source modules.
- Read `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`; consult `KNOWN_FAILURE_MODES.md` only for applicable traps.

Completion:
- Work until the exact full B3 target closes or a valid quantifier-matched obstruction dossier forces coordinator architecture judgment. A green build, one receipt, or candid gap is only a checkpoint.
- PASS requires a concrete allowed route, all parameterized and pinned theorems, exact same-object run, source simulation, public composition, and committed replay evidence.
- FAIL requires the exact universal `HistoricalFAIL` over every construction allowed by the frozen domain and the checked iff bridge. Do not strengthen the premise or narrow the route type.
- If a local implementation or replay defect remains and another in-scope step is available, continue. If the exact unchanged twelve-constructor model forces a primitive/atomicity/cost choice, report OBSTRUCTED with the smallest checked implication and stop; do not edit Core or choose the architecture unilaterally.
- Exercise empty, singleton, size two, threshold-adjacent sizes, the pinned fixture, valid/reversed/empty/out-of-bounds queries, every reachable source constructor, live/empty/dead reads, and all route branches.
- Log the bounded-machine/ROM/lowering decisions in `DESIGN_DECISIONS.md` and replay/process decisions in `WORKFLOW_DESIGN_DECISIONS.md`.
- Stage only owned files and make the exact freeze then implementation commits.

Verification:
- Development-loop checks: build the narrowest new module and direct expected-type consumer first; run bounded replay startup, one exact positive selector, and one representative mutation before the full registry.
- Final-required checks: focused `lake build` of the B3 historical-route root and independent consumer; one terminal green full committed replay; strict frozen-row/source-identity/history checks; hygiene; native-decision scan; exact range/scope/non-owned identity; restoration; clean state; `git diff --check`; `git diff --check c19061629ce8cf1e78992a99346170edd84b4971..HEAD`; `powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base c19061629ce8cf1e78992a99346170edd84b4971`; `powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1`.
- Conditional checks: no broad `lake build` and no `scripts/gate.ps1` unless a unique contradiction appears which a narrower named component cannot resolve. If triggered, explain the exact acceptance row and do not duplicate a full replay owned by the aggregate.
- Use one heavy Lean/Lake process at a time. Record runtime, timeout rationale, exact tree, covered rows, and outcome. Never rerun an unchanged expensive command after timeout or terminal failure.
- Run the full replay exactly once on the unchanged clean committed candidate after startup/selectors/mutation pass. A precommit pass, skipped case, timeout, non-terminal receipt, dirty tree, or post-run edit is not final evidence.

Report:
- Begin with exactly one status line. For candidate completion the first two lines must be exactly `Status: CANDIDATE_COMPLETE` and `I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.`
- Report handle/title, exact branch/worktree/base/freeze/HEAD/tree/parents, changed paths, source-port input identities, and clean state.
- Name the exact definitions/theorems for route domain, allowed core, codec/ROM, bounded target machine, charged physical lowering, reachable width invariant, stuttering simulation, receipts, P/Q, PASS/FAIL bridge, verdict, and expected-type consumers; quote their checked proposition shapes and object-composition chains.
- Include proof digestion: conceptual meaning, plain-English meaning, live assumptions, downstream A4 consumer, and skeptical-reviewer questions.
- Report all six frozen downstream choices and why each is a real execution witness.
- Give exact command outcomes, replay registry/counts/selectors/deadline/restoration results, and the durable requirement-to-evidence matrix with anti-vacuity challenges and predicate pairs.
- State one of CANDIDATE_COMPLETE, OBSTRUCTED, BLOCKED, or INCOMPLETE. Request coordinator audit only; do not call the route accepted, select A4, merge, push, publish, or close E1.
