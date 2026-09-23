Make the title of this chat exactly: (PQ1-U) Charge the metadata setup

Worker identity:
- Handle: PQ1-U
- Fresh or returning worker: RETURNING metadata_width proof subagent; current runtime catalog verified in PQ1-W report.

Skill:
- Use $rmq-proof-sprint and the canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with rmq-proof-sprint required and actual runtime RMQ catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 9e2720b991e203d22a2787abf66dbfb9888088fb
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ, without switching branch or creating another worktree.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_SETUP_REPORT.md
- You are not alone; preserve other work. No staging/commits, shared ledger writes or changes to existing modules.

Roadmap contract:
- Node/join: The uniform whole-query program must obtain all runtime geometry through charged metadata loads from the same allocation.
- Local owned rung: Fixed source metadataSetupBlock loads all174 fields from addresses0..173 into registers16..189, using register6 as address scratch. Prove exact canonical field values and ordered receipts, preservation of other registers, and actual fixed-budget primitive compilation.
- Roadmap-node closure condition: Lead still proves whole query and its arithmetic widths; setup closure only discharges the explicit initial metadata loads.
- Goal: Define one input-independent fixed source block, prove the exact source and compiled setup theorem, and compose with the canonical metadata prefix of shapeMemory/buildMemory. No size-generated code.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Setup.lean importing Allocation, Width, Structured and Compiler when emitted.
- Write scope: RMQ/Core/WordRAM/Packed/Setup.lean; docs/internal/packed_query/PQ1_SETUP_MATRIX.md; docs/internal/packed_query/PQ1_SETUP_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze matrix; implement finite const/load source, prove generic prefix loading, specialize174 and canonical allocation, consume generic compiler once available. Coordinate its interface directly with primitive_calculus.
- Non-goals: Query guard, metadata schema changes, full logical read/controller, or whole-query closure claims.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-U-SOURCE, REQ-U-ALLOCATION, REQ-U-FRAME, REQ-U-MACHINE, CHK-U-LEAN, INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-INSTRUCTION-ATOMICITY, INV-NO-SYNTHETIC, INV-PROOF-SEPARATION, INV-CATEGORY-SEPARATION.
- REQ-U-SOURCE: metadataSetupBlock is fixed finite syntax with exactly174 pairs of constant-address then raw-load instructions; address scratch6, destinations16+i for i<174. Its size is348. On any memory of length at least174 and running Data, source evaluation remains running, destination16+i equals the actual memory[i], final register6=173, and ordered receipts equal (List.range174).map(address, actual lookup). No host metadata injection.
- REQ-U-ALLOCATION: Prove shapeMemory/buildMemory prefix lookups equal the concrete metadata fields; consume this in the same setup evaluation to install every scalar/regular/interior field. Prove post-setup all-register fit from pre-setup fit using Width and the same wordWidth. No header-fit assumption in the canonical theorem.
- REQ-U-FRAME: Prove every register outside6 and16..189 is unchanged. Prove all source encoded operand fields fit every canonical wordWidth; dormant code and address immediates included.
- REQ-U-MACHINE: Consume Compiler actual run theorem for fixed syntax. Same run installs the fields, preserves frame, has exact ordered receipts and bounded primitive steps. Include an arbitrary hosted-segment consumer if Compiler supports it so lead can place setup behind guard. Do not stop at source semantics.
- CHK-U-LEAN: Narrow compiler/import checks and independent exact-type consumers for the full canonical source theorem and actual run, including empty/singleton allocations. No native_decide, omitted-field assumptions, desired-answer hypotheses, or broad gates.
- Freeze matrix using canonical template with verbatim requirements and assigned inherited invariant text. Quote exact propositions/object chains for closure.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply only if claiming a mutation campaign; none is assigned here.

Forbidden shortcuts:
- No batch-load instruction, preinitialized geometry, lookup callback, or metadata-shaped input registers. Each field is fetched by its own primitive raw load. Count348 source instructions; compiled budget comes from actual compiler theorem.

Context:
- Guard uses registers0..5. Bank16..189 is reserved as read-only after setup; later arithmetic source may use registers>=256. All initial registers except0..2 are0.
- General induction over pairs can prove source loading/frame without evaluating174 steps in kernel examples. Canonical shapeMemory is metadata ++ dense body and metadata_length=174.
- Whole-run intermediate width remains lead-owned; your post-setup register-fit theorem is an input to it.

Completion:
- Continue until all assigned rows close, including locally available Compiler consumer. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this exact bounded leaf.

Verification:
- Coordinate one Lean build slot with lead, numeric_span and primitive_calculus. Local .lake/build/lib/lean only.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 9e2720b991e203d22a2787abf66dbfb9888088fb..HEAD after integration.

Report:
- Exact source, register, allocation, run propositions; completed matrix; evidence command ledger; proof digestion and limits. No staging/commits.
