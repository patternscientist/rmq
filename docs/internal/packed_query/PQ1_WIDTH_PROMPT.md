Make the title of this chat exactly: (PQ1-W) Prove concrete metadata and allocation width

Worker identity:
- Handle: PQ1-W
- Fresh or returning worker: FRESH proof subagent on the lead's governed feature worktree with disjoint module ownership.

Skill:
- Use $rmq-proof-sprint before starting and apply its canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run scripts/project_skill_preflight.ps1 with this ref, rmq-proof-sprint required and the actual runtime project-skill catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 13d188582d3994a04f893ca0e21970c40c14b8cd
- Existing branch codex/fully-charged-packed-query-v1, worktree C:/Users/poin/.codex/worktrees/a84a/RMQ. Do not switch branches or create another worktree.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_WIDTH_REPORT.md
- You are not alone. Preserve other edits; do not stage or commit. Lead owns shared ledger writes and scoped commits.

Roadmap contract:
- Node/join: Fully charged packed query over the concrete Allocation.buildMemory; this leaf discharges actual stored-word and allocation-address width for that construction.
- Local owned rung: All 174 metadata words and all repacked body words fit the exact concrete wordWidth, as do allocated addresses and the first missing address; all valid endpoints fit too.
- Roadmap-node closure condition: Lead must additionally prove the fixed instruction program's entire execution, register/instruction widths, constant budget, semantic refinement and public acceptance. This leaf is not roadmap closure.
- Goal: Prove unconditional metadata_words_fit, buildMemory_words_fit, allocation addressability and valid-endpoint representability for the existing concrete builder.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Width.lean importing Allocation.lean; use the exact unchanged metadata, buildMemory and wordWidth definitions.
- Write scope: RMQ/Core/WordRAM/Packed/Width.lean; docs/internal/packed_query/PQ1_WIDTH_MATRIX.md; docs/internal/packed_query/PQ1_WIDTH_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead; do not write concurrently).
- Lifecycle dependency order: Inspect exact builder and source bounds, freeze matrix, prove conservative numeric envelopes and consume them in concrete fit/addressability theorems, verify, report; lead then consumes these facts in primitive canonical execution. No evidence-dependent decision gates this leaf.
- Non-goals: Changing metadata schema or width formula, final code/register width, whole-query correctness, public aliases, or unrelated source changes.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-W-METADATA, REQ-W-ALLOCATION, REQ-W-ENDPOINTS, CHK-W-LEAN, INV-STORE-IDENTITY, INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-PROOF-SEPARATION, INV-ALL-SIZE, INV-WIDTH-SCALING.
- REQ-W-METADATA: For every CartesianShape shape and every word in metadata shape, prove word < 2^wordWidth shape.size. Cover the actual 42 scalars, 23 four-field descriptors and eight five-field interior descriptors. No readiness, zero-count, size threshold or desired-fit premise.
- REQ-W-ALLOCATION: For every xs:List Int, every word in buildMemory xs is <2^wordWidth xs.length, and (buildMemory xs).length <2^wordWidth xs.length. Derive every allocated address and the first missing address fits from this same allocation. Do not substitute a sibling allocation or the old width.
- REQ-W-ENDPOINTS: Every valid mathematical endpoint pair l<r<=xs.length has both endpoints below 2^wordWidth xs.length. State invalid representable endpoint handling remains a program-guard obligation.
- CHK-W-LEAN: Narrow kernel checking of Width and direct typed consumers, including n=0/1 and nonzero symbolic long/sparse counts through the canonical shape quantifier. No native_decide or assumed widths.
- Freeze matrix from docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md with verbatim requirements and assigned inherited invariant text. Record exact propositions, same-object consumers and challenges; do not claim that metadata fit establishes reachable-register fit.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE govern any claimed mutation campaign; none is assigned beyond kernel consumers.

Forbidden shortcuts:
- No changing width to absorb a failed proof without lead review, uncounted metadata, assumed header fits, semantic answer field or trust shortcut. A polynomial envelope must be consumed by actual metadata fields.

Context:
- Read AGENTS.md, E1 roadmap, Allocation.lean and PQ1_SOURCE_INVENTORY.md. Ask memory_inventory for its new detailed width mapping (read-only scout).
- Suggested envelope from scout: w=oldWidth, Q=2^w; all fields <=64*Q^2 then <2^(32+8*w). oldBits=oldCount*w, newCount<=174+oldBits; metadata descriptors mostly below Q. Existing all-size bounds in ReviewerControllerProof include sparse count:2806, fringe/select counts:1621/1643, interior dead address:3161. Existing legacy-stride bounds:ReviewerWidth:130 and source discharge ControllerProof:2884. Interior entry widths <=7 BPW come from public InteriorDirectory Base/SparseLevelWidth; source join is private in ControllerInteriorStateProof:1042.
- All .olean/.ilean dependencies are copied into private .lake/build/lib/lean. Coordinate the single build slot with lead before running Lean. No aggregate gate for this leaf.

Completion:
- Continue until all assigned leaf rows close or a real blocker arises; consume each envelope in the concrete fit/address theorem. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded leaf only.

Verification:
- Narrow Lean checks and hygiene of owned files; lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 13d188582d3994a04f893ca0e21970c40c14b8cd..HEAD after integration.

Report:
- Exact theorem types, metadata coverage, complete matrix, branch/worktree/base, checks and proof digestion. No staging/commits; provide a proposed design entry for lead.
