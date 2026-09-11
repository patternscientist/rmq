Make the title of this chat exactly: (PQ1-T) Prove structured assembly compilation

Worker identity:
- Handle: PQ1-T
- Fresh or returning worker: RETURNING primitive_calculus proof subagent, with current runtime catalog verified in its completed PQ1-C report.

Skill:
- Use $rmq-proof-sprint and its canonical completion gate before starting.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run scripts/project_skill_preflight.ps1 with the actual runtime catalog and rmq-proof-sprint required.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 9e2720b991e203d22a2787abf66dbfb9888088fb
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ. Do not switch branches or create another worktree.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_COMPILER_REPORT.md
- You are not alone. No staging/commits or shared-ledger edits; preserve other work. Lead owns Primitive/Structured interfaces; request changes rather than editing them.

Roadmap contract:
- Node/join: The fixed packed-query source will use Structured.Block; this leaf links that source to the exact existing primitive run and supplies a constant syntax-derived budget.
- Local owned rung: Generic compilation correctness for every Structured.Block, including halted/faulted early termination, exact reads, resolved forward branches, fixed finite repetition and static instruction-field width.
- Roadmap-node closure condition: Lead must build the actual uniform RMQ source, prove its specification refinement and runtime width, instantiate code/scratch counts and pass whole-query acceptance. Generic compilation is a necessary leaf, not the full target.
- Goal: Prove every block's actual compiled run agrees with the independent structured evaluator, preserving result registers/status, ordered receipts and a syntax-derived executed instruction bound.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Compiler.lean importing Structured.lean and its concrete Block.compileAt, Block.eval, Block.size, Action.instruction.
- Write scope: RMQ/Core/WordRAM/Packed/Compiler.lean; docs/internal/packed_query/PQ1_COMPILER_MATRIX.md; docs/internal/packed_query/PQ1_COMPILER_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Inspect fixed source/compiler definitions, freeze matrix, prove hosting/length and compilation by syntax induction with finite-repeat induction, consume in generic whole-program/width consumers, verify and report; lead's RMQ source consumes these facts next. No evidence-dependent decision gates this leaf.
- Non-goals: Changing the source language or compiler, constructing RMQ source, runtime register-width proof, or a public capstone alias.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-T-LENGTH, REQ-T-COMPILE, REQ-T-WIDTH, REQ-T-CONSUMER, CHK-T-LEAN, INV-TRACE-EXECUTION, INV-VALUE-DEPENDENCY, INV-NO-SYNTHETIC, INV-INSTRUCTION-ATOMICITY, INV-ADDRESS-WIDTH, INV-CATEGORY-SEPARATION.
- REQ-T-LENGTH: Prove (block.compileAt base).length=block.size for every block/base and reusable HostedAt composition over exact list segments. Fixed repetition expands every body at the correct offset.
- REQ-T-COMPILE: For any memory/program/block/base and initial State s with s.pc=base and block.compileAt base hosted there, prove there exists used<=block.size such that the actual run at used fuel has Data.ofState final=(block.eval memory (Data.ofState s)).final, reads equal that evaluator's ordered reads, actual steps=used, and if final.status=running then final.pc=base+block.size. Handle every constructor including count=0, empty branches, failed loads and early exit. Do not assert adequacy as a premise or compare to a source evaluator defined by running compiled code.
- REQ-T-WIDTH: Define a constructor-exhaustive recursive source-field fit predicate on actions, exit registers and branch conditions. If these fields fit and base+block.size<2^width, prove every emitted instruction's encoding fits width, including dormant branches and expanded repetitions. Keep this static code theorem distinct from runtime arithmetic safety.
- REQ-T-CONSUMER: Give a whole-program corollary for block.compileAt 0 followed by halt of an output register: its actual run with a fixed syntax-derived fuel budget yields the structured final result (or unchanged early halt/fault), with exact reads and steps bounded by the compiled length. No arbitrary adequate-fuel premise. Include direct consumers that exercise an overwritten operand, both branch arms, repeat count zero/nonzero, repeated physical receipts and missing-load termination.
- CHK-T-LEAN: Narrow kernel checks of Compiler and its consumers, full exact expected-type consumers for REQ-T-COMPILE/WIDTH/CONSUMER, plus hygiene and unchanged-interface checks.
- Freeze matrix from the proof acceptance template, copy these requirements and assigned inherited invariant text verbatim, and record exact conclusions, identities and anti-vacuity challenges. Finite consumers supplement universal proofs.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply to any claimed campaign. No replay campaign is assigned beyond kernel consumers.

Forbidden shortcuts:
- No semantic controller or query macro, trust shortcut, replayed reads, desired-result hypothesis, erased failed read, or unstated branch/PC width exception.

Context:
- Structured.lean compiled cleanly against the local cache. Its source Data has registers/status but no PC; compilation uses absolute PCs. Block.eval is independent compositional semantics using primitive scalar actions, and repeat is fixed syntax data expanded at compilation.
- Reuse Calculus.run_add, RunsTo, run_read_at and run_eq_of_agree. No changes to those modules are needed unless a precise interface gap is reported to lead.
- Lead works actual RMQ source and integration while metadata_width proves concrete headers/addresses. Coordinate every Lean check through the shared build slot. No full gate for this leaf.

Completion:
- Persist until all assigned generic compiler targets close. A length lemma or green partial compiler is not completion. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded compiler leaf only.

Verification:
- Local LEAN_PATH=.lake/build/lib/lean; narrow Lean with owned outputs. Coordinate builds and preserve logs on failures; do not repeat an unchanged timed-out process.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 9e2720b991e203d22a2787abf66dbfb9888088fb..HEAD after integration.

Report:
- Exact theorem propositions, composition/object chain, full matrix, branch/worktree/base, tests, live assumptions and proof digestion. No staging/commits; give proposed design entry to lead.
