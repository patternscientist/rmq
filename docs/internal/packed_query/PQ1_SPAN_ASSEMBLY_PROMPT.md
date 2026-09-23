Make the title of this chat exactly: (PQ1-SA) Compile the numeric span routine

Worker identity:
- Handle: PQ1-SA
- Fresh or returning worker: RETURNING numeric_span proof subagent with runtime catalog verified in its PQ1-S report.

Skill:
- Use $rmq-proof-sprint and the canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with rmq-proof-sprint required and actual runtime RMQ catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 9e2720b991e203d22a2787abf66dbfb9888088fb
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ, without switching branch or creating another worktree.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_SPAN_ASSEMBLY_REPORT.md
- You are not alone; preserve other work. No staging/commits, shared ledger writes or changes to Primitive/Structured/Span.

Roadmap contract:
- Node/join: The whole-query logical-read block must consume the previously proved numeric span routine through compiled scalar assembly.
- Local owned rung: A fixed Structured.Block implementing decodeSpanNat, with a universal source-evaluation theorem, exact attempted receipts, bounded fixed register footprint and composition through the generic compiler when available.
- Roadmap-node closure condition: Lead still proves canonical logical read/control, full width/budget and capstone; this leaf is the numeric-decoder-to-assembly join only.
- Goal: Define spanBlock base with concrete scalar instructions and prove its evaluation equals decodeSpanNat for all numeric memories and valid scalar geometry, including failure and zero spans; consume Compiler's theorem when it becomes available.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/SpanAssembly.lean importing Structured and Span, with a later Compiler consumer in the same owned file once that module is ready.
- Write scope: RMQ/Core/WordRAM/Packed/SpanAssembly.lean; docs/internal/packed_query/PQ1_SPAN_ASSEMBLY_MATRIX.md; docs/internal/packed_query/PQ1_SPAN_ASSEMBLY_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze local matrix and exact register contract, implement scalar source, prove source/decoder value and receipt equality plus frame, then consume generic compiler when available; lead then composes it with the canonical repacked-loader theorem. Compiler development proceeds independently and does not gate evidence-producing source proofs.
- Non-goals: Query guard, full RMQ source, metadata schema, redesigning the ISA, or claims that structured evaluation alone is primitive execution.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-SA-SOURCE, REQ-SA-RECEIPTS, REQ-SA-FRAME, REQ-SA-MACHINE, CHK-SA-LEAN, INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-INSTRUCTION-ATOMICITY, INV-NO-SYNTHETIC, INV-PROOF-SEPARATION, INV-CATEGORY-SEPARATION.
- REQ-SA-SOURCE: Define spanBlock base independent of width, position, len and memory. Input registers are base,base+1,base+2; output is base+3; scratch uses an explicitly bounded interval starting at base+4. For running source Data with those inputs, prove if decodeSpanNat width position len memory=some value then evaluation ends running with output value, and if it is none evaluation ends fault. Cover every positive width and len<=width mathematically; no successful-read premise. Use only Action scalar operations and Block branches/sequence. Make len<width the live canonical machine-safety domain if a power-of-two mask needs it, while keeping the value theorem honest about the mathematical source domain.
- REQ-SA-RECEIPTS: Define exact attempted receipts from the same numeric memory: none for zero span, first attempt for a nonzero span, second only if crossing and first succeeds. Prove source eval reads equals this ordered list for all cases, including missing first or second cells. Do not identify the full planned list with a short-circuited failed execution.
- REQ-SA-FRAME: Prove registers outside the declared input/output/scratch interval are unchanged, and source size/maximum static register ID are bounded by explicit constants independent of inputs and memory. Constant immediates and encoded program fields must be inventoried; static expansion may not depend on runtime width.
- REQ-SA-MACHINE: Once Compiler.lean is available, provide an actual primitive-run consumer of spanBlock that proves the same result/status and ordered receipts with a fixed instruction budget derived from spanBlock.size. Frame and all actual steps must refer to that same run. Coordinate required compiler theorem interfaces with primitive_calculus; do not stop at the source evaluator if this dependency is locally available.
- CHK-SA-LEAN: Narrow checks plus direct compiled consumers for zero, crossing, noncrossing, missing-first, missing-second and all-ones raw cells. No native_decide or desired-answer hypotheses in the canonical source implementation.
- Freeze matrix from the proof acceptance template with verbatim rows and assigned inherited invariant text; quote exact conclusions and consumer identities before closure.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply to any claimed campaign; only kernel consumers are assigned here.

Forbidden shortcuts:
- No action evaluating a whole decoder, no double-width concatenation, no phantom second attempt after first fails, no executable semantic answer/callback, no arbitrary fuel asserted adequate.

Context:
- The compiled branch language is fixed in Structured.lean. primitive_calculus owns Compiler.lean proving arbitrary-block compilation; communicate with it directly for the final consumer.
- Implementation suggestion: compute address=position/width, offset=position%width, load first, low=first>>offset. For contained spans compute mask power from 1<<len and remainder. For crossing read address+1, lowBits=width-offset, highBits=len-lowBits, mask second by 2^highBits, shift by lowBits, add to low. Full-width source masks are mathematical only; canonical len=oldWidth<wordWidth ensures actual intermediates fit later.
- Generic runtime safety of all canonical query registers remains lead-owned; expose enough intermediate identities to prove it. Do not claim static field bounds are runtime width proof.

Completion:
- Continue through the actual compiler consumer once available. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this exact bounded leaf.

Verification:
- Coordinate the one Lean build slot with lead, metadata_width and primitive_calculus. Use local .lake/build/lib/lean only; preserve logs for failure.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 9e2720b991e203d22a2787abf66dbfb9888088fb..HEAD after integration.

Report:
- Exact source/register/program definitions, theorem propositions and consumer chain, complete matrix, tests, branch/worktree/base, and proof digestion. No staging/commits.
