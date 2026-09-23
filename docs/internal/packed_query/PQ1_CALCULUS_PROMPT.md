Make the title of this chat exactly: (PQ1-C) Prove physical execution calculus

Worker identity:
- Handle: PQ1-C
- Fresh or returning worker: FRESH proof subagent in the lead's governed feature worktree, using disjoint file ownership.

Skill:
- Use $rmq-proof-sprint before starting; read canonical completion gate and relevant known failure modes.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run scripts/project_skill_preflight.ps1 with this ref and rmq-proof-sprint required, reporting your actual runtime RMQ skills.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 4639223bc8130b0ef752270b5cbdd74325abcd60
- Branch/worktree: use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ; do not create another worktree or switch the shared branch. The lead's additive Primitive.lean is the pinned interface for this task.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_CALCULUS_REPORT.md
- You are not alone. Do not revert or overwrite other edits. No commits or staging: the lead owns scoped commits and integration.

Roadmap contract:
- Node/join: Fully charged packed-query capstone; this leaf supplies actual primitive execution and read provenance calculus to its block proofs.
- Local owned rung: Kernel-checked generic execution composition, exact category partition, occurrence-indexed read backing and supplied-memory agreement for the concrete Primitive.lean evaluator.
- Roadmap-node closure condition: The lead additionally constructs and proves the all-size RMQ program, allocation, constant budget, width and public theorem, then passes blind audit. This task closes only the named calculus leaf.
- Goal: Prove all assigned generic evaluator facts and supply direct checked examples/consumers; do not stop after a subset.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Calculus.lean importing RMQ.Core.WordRAM.Packed.Primitive; theorem signatures are specified below against that exact evaluator.
- Write scope: RMQ/Core/WordRAM/Packed/Calculus.lean; docs/internal/packed_query/PQ1_CALCULUS_MATRIX.md; docs/internal/packed_query/PQ1_CALCULUS_REPORT.md; docs/internal/DESIGN_DECISIONS.md (coordinate one append-only entry with lead before writing; alternatively give exact proposed entry for lead to append).
- Lifecycle dependency order: Read the lead's concrete primitive interface, freeze this leaf's matrix, prove composition/provenance/accounting and direct consumers, validate the standalone module, report to lead; whole-query join and exact-commit audit follow. No output-dependent decision gates this proof leaf.
- Non-goals: Canonical RMQ program, shape semantics, allocation changes, public alias, unrelated cleanup, or claiming the complete capstone.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-C-COMPOSE, REQ-C-PARTITION, REQ-C-POSITION, REQ-C-AGREEMENT, CHK-C-LEAN, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-NO-SYNTHETIC, INV-STORE-AGREEMENT, INV-CATEGORY-SEPARATION.
- REQ-C-COMPOSE: Prove run_add: actual run at fuel a+b equals the run at a composed with the run at b from its final state, concatenating exact Transition lists; define RunsTo and prove reflexive, transitive, actual-step introduction, and fuel extension after halt.
- REQ-C-PARTITION: Prove Run.steps equals category-log length and the sum of the six category counts for every actual run. Prove steps<=fuel from execution. Preserve the exact instruction vocabulary; do not add semantic macro instructions.
- REQ-C-POSITION: For every transition at index k of an actual run, prove before equals the final state of run k, program[before.pc]?=some instruction, execute memory instruction before=(after,receipt), and any receipt is from a load with address=before.regs addrReg and reply=memory[address]?. Keep repeated equal receipts position-distinct. Include missing physical reads.
- REQ-C-AGREEMENT: If a second numeric memory agrees with the first at every address of the first run's actual read receipts, prove the full actual runs equal, including final state, transitions, categories and result. Derive from execution induction, not a legacy static-footprint theorem.
- CHK-C-LEAN: Elaborate the new module and small kernel-checked consumers for a successful load/halt, failed attempted load, two equal repeated read occurrences, and supplied-store agreement.
- Before proof edits create the matrix from docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md. Copy the above requirements and assigned inherited invariant text verbatim from completion gate. Every row names the downstream calculus/block consumer and exact proposition. Leaf completion is not whole-query completion.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE: no mutation harness is assigned; any claimed campaign must nevertheless have exact IDs, nonvacuous selection and owned child deadlines. Do not claim report-only mutations as closure.

Forbidden shortcuts:
- No sorry/admit/axiom/native_decide/unsafe or new trust primitives. No answer/reference semantics in the evaluator. No List.Mem-only claim for occurrence provenance. No theorem about a sibling evaluator.

Context:
- Read AGENTS.md, E1 roadmap section, Primitive.lean and relevant E1MachineCalculus proofs as reusable patterns. Do not edit Primitive.lean: request interface changes from lead.
- Parent owns all builds against the ordinary .lake tree. You may run lean only after coordinating the slot. Primitive.lean imports only Std; lead will provide a local .olean or approve direct narrow compilation, avoiding the huge RMQ import closure.

Completion:
- Continue until all leaf rows close or a real blocker arises. Return exact propositions, live assumptions and proof digestion. Full capstone remains lead-owned.
- Leaf candidate report begins Status: CANDIDATE_COMPLETE then I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required. This applies only to the explicitly bounded calculus leaf, not PQ1 roadmap closure.

Verification:
- Narrow Lean checks for Primitive and Calculus only; coordinate each heavy process with lead. Static hygiene and git diff --check for owned files.
- Lead will run scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and committed-range git diff --check 4639223bc8130b0ef752270b5cbdd74325abcd60..HEAD after integration; do not run aggregate gate for this leaf.

Report:
- Branch, worktree, base, owned changes, exact theorem types, direct consumers, complete matrix, verification and conceptual/plain-English/live-assumption/skeptical-reviewer digestion. No commit SHA until lead commits; explicitly mark integration pending.
