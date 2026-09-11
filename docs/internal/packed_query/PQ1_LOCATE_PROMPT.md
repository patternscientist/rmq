Make the title of this chat exactly: (PQ1-L) Compile counted descriptor selection

Worker identity:
- Handle: PQ1-L
- Fresh or returning worker: RETURNING metadata_width with verified current PQ1-U runtime catalog.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: b0af10d14121c7b11a7d3eb7cb1515c618a0da4b
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ; no branch/worktree changes.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_LOCATE_REPORT.md
- You are not alone; preserve others. No staging/commits or shared-ledger edits.

Roadmap contract:
- Node/join: The fixed logical-read program must compute old absolute bit location and exact presence/length from the charged174-field register bank.
- Local owned rung: Fixed finite descriptor dispatch and regular/interior scalar assembly, universally equal to a pure stored-field specification and canonically equal to reviewerLogicalSpan.
- Roadmap-node closure condition: Lead composes location with direct SpanAssembly reads and the complete RMQ controller/safety. This leaf closes location only.
- Goal: Define locateBlock base independent of n/shape/endpoints, compute correct logical presence/position/length from metadata registers, preserve inputs/bank/frame, and prove actual compiled run at a fixed budget. Consume LogicalSpan's canonical theorem when available.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Locate.lean, importing RegularLocate, InteriorLocate, Setup, Compiler and LogicalSpan once ready.
- Write scope: RMQ/Core/WordRAM/Packed/Locate.lean; append frame/static/consumer theorems only in RegularLocate.lean and InteriorLocate.lean (do not change definitions or existing theorem signatures); docs/internal/packed_query/PQ1_LOCATE_MATRIX.md; docs/internal/packed_query/PQ1_LOCATE_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze scalar interface and matrix, prove primitive descriptor-source helpers/frames, construct finite dispatch, prove generic stored-field spec, consume numeric_span's canonical LogicalSpan theorem, provide hosted/standalone primitive consumers. Work on source before the canonical dependency is ready.
- Non-goals: Changing allocation/metadata/width/compiler/ISA, performing physical body reads, whole control or final capstone claims.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-L-SOURCE, REQ-L-CANONICAL, REQ-L-FRAME, REQ-L-MACHINE, CHK-L-LEAN, INV-VALUE-DEPENDENCY, INV-ORACLE-INDEPENDENCE, INV-INSTRUCTION-ATOMICITY, INV-ALL-SIZE, INV-PROOF-SEPARATION.
- REQ-L-SOURCE: Inputs base=segment, base+1=index; outputs base+2=presence, base+3=old absolute bit position, base+4=exact logical length. Require base>=256 so input/scratch does not overlap metadata16..189. Use scratch only within base+5..base+48; child regular/interior blocks may start at base+32. Source must be one fixed finite value per register base, independent of runtime geometry. For each non20 segment<23 copy the four stored descriptor fields (metadata indices42+4*segment through+3) into regularLocateBlock inputs. Segment20 selects the first present interiorSpan among8 descriptors (indices134+5*tag) with BP width from scalar index16. Out-of-range segments/indices return absent and zero outputs. Prove source result equals this pure register-field specification and reads=[]. Static finite dispatch must not use a dynamic register-read oracle.
- REQ-L-CANONICAL: For every canonical shape, registers agreeing with all174 actual metadata fields, and arbitrary segment/index, source evaluation gives exactly reviewerLogicalSpan shape.size (longCount shape) (packedReviewerSparseCount shape) segment index. Consume the same source/evaluation as generic theorem. Expose a List Int setup-to-locate consumer using buildMemory_setup fields. No count-zero/readiness/minimum-size/one-component hypothesis. Coordinate descriptor equality/ceilDiv-chunkCount with numeric_span's LogicalSpan module.
- REQ-L-FRAME: Prove inputs, metadata bank and every register outside declared output/scratch footprint unchanged. Prove a concrete source-size bound and all encoded register/immediate fields bounded by constants plus base, independent of shape/endpoints; include all dormant dispatch branches. Appended helpers in RegularLocate/InteriorLocate may add frame theorems needed for composition, preserving all existing definitions.
- REQ-L-MACHINE: Actual arbitrary-hosted segment and standalone fixed-budget run produce exactly the same location result and no reads, with same frame and explicit fixed step bound. Derive adequate fuel from Compiler; no source-evaluator-only completion. This location proof does not itself establish arithmetic runtime-width safety.
- CHK-L-LEAN: Narrow checks and exact independent type consumers. Include non20/20/invalid/empty-sentinel stored-field cases and canonical arbitrary-shape source consumer. No native_decide or desired-result premises.
- Freeze matrix with verbatim assigned rows and inherited invariants. Exact proposition/object chain required for closure.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply only to claimed campaigns; none assigned.

Forbidden shortcuts:
- No primitive descriptor lookup, host-derived geometry injected in registers, free metadata loads, or count inferred from bit length. Using charged setup registers is allowed; any dependent new values must be computed by source actions.

Context:
- Root Scalar/RegularLocate/InteriorLocate are compiled at base b0af10d; child source theorems cover arbitrary Nat inputs mathematically and have sizes5/19/27. Source safety will be proved separately using primitive_calculus Safety.lean.
- numeric_span owns LogicalSpan.lean from the preflighted PQ1-LS prompt and should expose canonical descriptor geometry. Contact it early; do not edit its module.
- MetadataBank keeps scalar size/layout/counts; local regular descriptor handling must preserve empty sentinel presence (11/15/19) and ragged word length.
- A sequence of fixed conditionals or nested segment checks is fine; geometry/table content never changes code. Bigger fixed code is acceptable and explicitly accounted later.

Completion:
- Continue through canonical LogicalSpan and actual Compiler joins when locally available. No easier alternate endpoint. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded leaf.

Verification:
- Coordinate one Lean slot with root/numeric_span/primitive_calculus; local build tree only.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check b0af10d14121c7b11a7d3eb7cb1515c618a0da4b..HEAD after integration.

Report:
- Exact source/metadata/spec/primitive-run propositions, complete matrix and ledger, digest and live limits. No staging/commits.
