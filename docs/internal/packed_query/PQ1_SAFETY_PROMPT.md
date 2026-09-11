Make the title of this chat exactly: (PQ1-QS) Preserve word safety through compilation

Worker identity:
- Handle: PQ1-QS
- Fresh or returning worker: RETURNING primitive_calculus with verified current PQ1-T runtime catalog.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 9e2720b991e203d22a2787abf66dbfb9888088fb
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ, no branch/worktree changes.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_SAFETY_REPORT.md
- You are not alone; preserve other work. No staging/commits or shared ledger/interface edits.

Roadmap contract:
- Node/join: The full query's scalar arithmetic invariants must imply actual primitive Instruction.Safe and prefix-state fit under the same wordWidth.
- Local owned rung: Generic source safety judgments and a compiler-preservation theorem for actual executed transitions and prefix states, including load/fault/early-exit/branches/fixed repetition.
- Roadmap-node closure condition: Lead derives the judgment for the concrete canonical query; this generic compiler theorem never replaces that canonical proof.
- Goal: Define an explicit constructor-based local source safety predicate, prove its operational preservation, and prove the actual hosted/standalone compiled run is safe with the same results/reads/budget as Compiler.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Safety.lean importing Compiler.
- Write scope: RMQ/Core/WordRAM/Packed/Safety.lean; docs/internal/packed_query/PQ1_SAFETY_MATRIX.md; docs/internal/packed_query/PQ1_SAFETY_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze exact safety semantics and acceptance matrix, prove action/local source rules, compose over syntax/actual trace, expose hosted and standalone consumers. Coordinate source interfaces early.
- Non-goals: Changing ISA/Compiler/Structured, proving canonical full-query safety, or hiding execution width in unproved capstone assumptions.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-QS-LOCAL, REQ-QS-COMPILER, REQ-QS-PREFIX, CHK-QS-LEAN, INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-INSTRUCTION-ATOMICITY, INV-TRACE-EXECUTION, INV-SEMANTIC-NONVACUITY, INV-PROOF-SEPARATION.
- REQ-QS-LOCAL: Define constructor-exhaustive source safety from actual scalar states and evaluated operations. Its local arithmetic obligations must explicitly bound result<2^width, require rhs<=lhs for subtraction, positive division/modulo divisor, and shift amount<width. Load success requires the actual returned numeric word to fit; missing loads may fault after their receipt. State data fit includes all registers and halted result. Sequence/conditional/repeat obligations must follow actual source evaluation, with finite repetition obligations for every visited iteration. Provide usable introduction/composition lemmas. Do not define the source predicate as the desired compiled-run conclusion or as True.
- REQ-QS-COMPILER: Given local source safety, block.FieldsFit width, initial state fit/PC and hosted block ending strictly below2^width, derive an actual primitive run at existentially produced used<=block.size with exact steps=used, same source data and reads, plus Instruction.Safe width t.before t.instruction for every actual transition occurrence. Actual loaded addresses come from fitting source registers; all source arithmetic conclusions must be consumed. Include jump/fallthrough PCs and stopped initial states. The theorem must constrain the same run as its value/trace/budget conclusions.
- REQ-QS-PREFIX: Derive State.Fits width for the initial state, every actual prefix state and final state of that hosted run; include prefix index0 and end. Supply a standalone compileAt0 fixed-size consumer and an appended-halt consumer if needed to avoid making the lead reconstruct adequacy. Dormant instruction fields remain separately covered by FieldsFit/compile_fits.
- CHK-QS-LEAN: Exact independent expected-type consumers and symbolic operations with boundary examples; a negative control must fail the safety hypothesis for underflow, zero divisor, excessive shift and overflowing result while a legal boundary operation succeeds. No native_decide, axioms or unchecked runtime callbacks. Negative controls can be kernel negation propositions; no mutation campaign assigned.
- Freeze matrix from canonical template with verbatim assigned rows and inherited invariant text. Evidence quotes exact object composition, not theorem names alone.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply only to claimed mutation campaigns.

Forbidden shortcuts:
- No widening width per input query, truncating oversized results to make existing Nat evaluation look fitting, changing ordinary subtraction semantics, static-operand-only width report, or assuming compiled-run safety as a premise.

Context:
- Compiler.compile_realizes/compile_correct/compile_run/compile_with_halt are now green. Reuse core helper lemmas via public interfaces; do not edit Compiler. If a private helper is essential, prove a focused local analogue and identify it.
- Scalar.lean natSubBlock and minBlock, RegularLocate19 and InteriorLocate27, SpanAssembly22, Setup348 provide future consumers. Lead will prove canonical inputs/intermediates; expose reusable arithmetic/local rules.
- Fixed code is bounded by wordWidth floor32+8*oldWidth, with final code size still to pin. Generic theorem may assume base+block.size<capacity and initial registers fit; final canonical theorem must discharge them.

Completion:
- Continue until the full local safety-to-actual-prefix target closes. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded leaf.

Verification:
- One Lean process at a time, coordinate with lead/numeric_span/metadata_width, local build tree only.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 9e2720b991e203d22a2787abf66dbfb9888088fb..HEAD after integration.

Report:
- Exact semantic safety definition and main propositions, command ledger and consumers, digest and remaining canonical obligations. No staging/commits.
