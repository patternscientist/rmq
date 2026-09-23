Make the title of this chat exactly: (PQ1-LW) Prove primitive loader word safety

Worker identity:
- Handle: PQ1-LW
- Fresh or returning worker: RETURNING primitive_calculus after PQ1-QS; current runtime catalog verified.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: b0af10d14121c7b11a7d3eb7cb1515c618a0da4b
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ; no branch/worktree changes.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_LOAD_SAFETY_REPORT.md
- You are not alone; preserve other work. No staging/commits, shared-ledger edits or existing module edits.

Roadmap contract:
- Node/join: Canonical query proof needs the actual metadata loader and numeric span reader to satisfy explicit source safety, including arithmetic results and failed-address arithmetic.
- Local owned rung: Unconditional reusable Block.Safe proofs for the fixed span routine on fitting numeric memory/representable geometry, and fixed metadata setup on fitting memory; then same-run actual prefix safety/value/receipt/budget consumers.
- Roadmap-node closure condition: Lead derives canonical location/whole-controller invariants and closes full capstone. This leaf closes two actual loader routines, not the entire query.
- Goal: Prove spanBlock_safe and metadataSetupBlock_safe, with complete arithmetic/address/result fit and actual compiler consumers, using your checked Safety.lean.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/LoadSafety.lean importing Safety, SpanAssembly, Setup, Width.
- Write scope: RMQ/Core/WordRAM/Packed/LoadSafety.lean; docs/internal/packed_query/PQ1_LOAD_SAFETY_MATRIX.md; docs/internal/packed_query/PQ1_LOAD_SAFETY_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze actual hypotheses and matrix; prove numeric crossing/contained intermediate bounds; derive source safety for every branch including faults/zero spans; derive setup safety and canonical instantiation; consume compiler and existing value/receipt theorems in same actual run.
- Non-goals: Changing ISA/source routines, assuming desired compiled safety, canonical whole-query arithmetic, or querying semantic answers.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-LW-SPAN, REQ-LW-SETUP, REQ-LW-RUN, CHK-LW-LEAN, INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-WIDTH-SCALING, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-PROOF-SEPARATION.
- REQ-LW-SPAN: For width>=2, arbitrary numeric memory whose every stored word is<2^width, and source Data.Fits width with registers base=width, base+1=position<2^width, base+2=len<width, prove (spanBlock base).Safe memory width data. Cover running/stopped data, len0, contained and crossing spans, missing first/second cells. Explicitly discharge subtraction non-underflow, positive divisors, both shift amounts<width, result fit and next-address fit. No successful-read premise. If a precise width>=2 edge is impossible, give the formal obstruction and tighten only the minimum constant; canonical wordWidth>=32 remains mandatory and unconditional.
- REQ-LW-SETUP: Prove metadataSetupBlock.Safe on arbitrary fitting numeric memory and fitting source Data, for a sufficient fixed minimum width (e.g.8 so0..173 fit). Include failed early loads/stopped states; canonical buildMemory/wordWidth theorem must discharge all memory/minimum hypotheses without readiness/presence assumptions. Every loaded word remains the actual raw reply.
- REQ-LW-RUN: For the same actual standalone/hosted span run as its value/receipt theorem, combine explicit source safety and static code/end-PC fit to obtain each executed Instruction.Safe and every prefix State.Fits, retaining actual result/status/ordered receipts/fixed budget. Provide analogous canonical metadata-run consumer retaining installed fields/receipts/budget. Static field/end-PC premises are allowed on generic hosted blocks but must be discharged for fixed base8192 spanBlock at canonical wordWidth and standalone metadata block when giving their canonical consumers.
- CHK-LW-LEAN: Narrow checks and exact expected types. Symbolic arbitrary-memory theorem, all-ones/crossing/missing boundary consumers, empty/singleton canonical setup. No native_decide or hidden assumptions on a read that is not actually available.
- Freeze matrix with verbatim assigned rows/inherited invariants; quote full propositions and same-run object chain for closure.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply only to claimed campaigns; none assigned.

Forbidden shortcuts:
- No double-physical-word concatenation, overflow truncation, full-width mask pretending to fit, blanket assumption that arithmetic results fit, or dropping failed second addresses from the safety argument.

Context:
- Span source masks a fragment before shifting. On crossing, offset>0, lowBits=width-offset<width, highBits=len-lowBits<width and value<2^len; on contained spans length<width makes1<<len fit. width>=2 and position<capacity bound position/width+1 belowcapacity whenever attempted. Zero spans bypass all reads/divisions.
- Setup is174 pairs; constants0..173 and raw loads only, so fitting memory supports every successful read and failures preserve registers. Source code register fields/PC are separate from source numeric safety but must be consumed by actual-run theorem.
- Root's physical reader will call spanBlock at base8256 (8192+64), while this contract asks a fixed base8192 example; supply either/both with exact declared base and prove it, or a bounded-base canonical corollary covering both. No runtime base computation is charged as free source.

Completion:
- Finish both routine safety proofs and same-run consumers. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded leaf.

Verification:
- Coordinate one Lean slot with lead/numeric_span/metadata_width; local tree only.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check b0af10d14121c7b11a7d3eb7cb1515c618a0da4b..HEAD after integration.

Report:
- Exact assumptions, intermediate bounds, source and primitive propositions, complete matrix/ledger, proof digestion and downstream limits. No staging/commits.
