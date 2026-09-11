Make the title of this chat exactly: (PQ1-RW) Prove canonical physical-reader word safety

Worker identity:
- Handle: PQ1-RW
- Fresh or returning worker: RETURNING primitive_calculus after PQ1-LW, actual runtime catalog verified current.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 067b6ffd350aee08f1496335ce957895f0da3fcc
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ; no branch/worktree changes.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_READER_SAFETY_REPORT.md
- You are not alone; preserve all other work. No staging/commits/shared-ledger edits.

Roadmap contract:
- Node/join: Every rank/select/interior/fringe call in the full query must use a reader proved safe at the same fixed wordWidth and counted allocation.
- Local owned rung: Canonical metadata-driven location, physical bit-position setup, raw span decoding and packet/length return all satisfy explicit scalar safety; the actual reader run retains exact semantic value, ordered reads, fixed budget and every-prefix width.
- Roadmap-node closure condition: Lead proves remaining controller arithmetic and joins complete query. This leaf closes the complete reader, not the entire query.
- Goal: Prove logicalReadBlock_safe canonically with no readiness/success/geometry-safety hypothesis, then combine it with logicalReaderRun_correct and Safety's compiler theorem on the same1069-step actual run.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/ReaderSafety.lean; optional reusable RMQ/Core/WordRAM/Packed/ScalarSafety.lean. Import completed LoadSafety, PhysicalRead, Locate, Width, Safety.
- Write scope: RMQ/Core/WordRAM/Packed/ReaderSafety.lean; RMQ/Core/WordRAM/Packed/ScalarSafety.lean; docs/internal/packed_query/PQ1_READER_SAFETY_MATRIX.md; docs/internal/packed_query/PQ1_READER_SAFETY_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze matrix; prove generic min/guarded-subtraction safety and descriptor numeric envelopes; prove actual locator branch safety from canonical metadata; prove shifted span inputs and decoded packet increment safe; derive whole reader Safe/FieldsFit; consume compiler and existing exact value/receipt theorem; instantiate charged setup and List Int. All source/geometry/value producers are checked before this join, and no output-dependent decision gates evidence collection.
- Non-goals: Changing source routines/metadata/wordWidth/ISA; remaining rank/select/interior/fringe scalar safety; weakening the final canonical reader theorem to a supplied-safety interface.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-RW-LOCATE, REQ-RW-READER, REQ-RW-RUN, CHK-RW-LEAN, INV-WORD-WIDTH, INV-ADDRESS-WIDTH, INV-WIDTH-SCALING, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-STORE-IDENTITY, INV-ALL-SIZE, INV-PROOF-SEPARATION.
- REQ-RW-LOCATE: Derive (locateBlock8192).Safe from MetadataMatches shape regs and Data.Fits(wordWidth shape.size), for every segment/index in the input registers and every source status. Discharge regular/interior arithmetic, guards, subtraction non-underflow and positive divisors from the actual metadata. Cover all23 segments, every interior component, invalid huge representable indices, empty sentinels and absent words. Do not assume the desired location arithmetic bounds or source safety as hypotheses of the canonical theorem.
- REQ-RW-READER: Prove logicalReadBlock.Safe on shapeMemory with fitting input Data and canonical MetadataMatches only. All shifted bit addresses, multiplication/addition intermediates, span widths, raw returned cells and value+1 packet fit the same wordWidth. In particular zero-length sentinels may have positions beyond nominal memory bounds and must be handled honestly; absent logical words perform no physical load. Reuse spanBlock_safe, but derive every geometry premise from canonical location. A stronger arbitrary fitting-memory theorem is welcome but not a replacement for unconditional canonical instantiation.
- REQ-RW-RUN: Prove FieldsFit for the actual fixed reader, including both dormant arms and resolved PCs, and derive actual Instruction.Safe for every indexed transition plus State.Fits for every fuel prefix on the same logicalReaderRun as logicalReaderRun_correct. Preserve exact packet, actual length, ordered readerReceipts, fixed1069 budget and caller frame. Give a List Int consumer starting from the charged metadata setup with fitting initialState, discharging metadata/value/width premises using existing setup proofs. No canonical source safety, read success, readiness, minimum size or rare-count-zero premise may remain.
- CHK-RW-LEAN: Narrow artifacts and independently spelled expected types; empty/singleton, absent segment, dead interior, empty sentinel and canonical crossing consumers or symbolic cases. Hygiene and whitespace checks; preserve the standard trust footprint. Every failed path that is claimed must retain the actual attempted address and fault status.
- Freeze all assigned rows and inherited invariants verbatim, quoting full checked propositions and same-memory/program/run composition for evidence.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply to any claimed campaign; none assigned here.

Forbidden shortcuts:
- No assumed arithmetic-safety certificate for the canonical reader, unbounded shift justification, full-physical-word packet increment, semantic address callback in source, hidden code-field exclusion or replacement of actual read occurrences by membership-only observations.
- Do not stop at regular location or a prefix helper; continue through complete reader safety and exact actual-run join.

Context:
- Metadata envelope is64*Q^2 with Q=2^oldWidth, and wordWidth=32+8*oldWidth. All174 fields satisfy this envelope. Guarded valid indices are below descriptor counts, so conservative product envelopes can cover intermediates without proving sharp per-table arithmetic. For example a cubic envelope in64*Q^2 fits the chosen capacity with room; prove exact bounds used.
- Positive BP width and interior chunk counts follow canonical descriptors. Generic scalar location functions intentionally permit malformed metadata; only the canonical theorem must discharge those hypotheses.
- PhysicalRead uses locateBlock8192 then five prefix actions, spanBlock8256 and three suffix actions. Reader output8194 packet,8195 length; writes8194..8270. size1068, appended-halt1069. logicalReadBlock_correct/ReaderWrites/logicalReaderRun_correct already check at the exact base.
- Source fits need all arithmetic operations; compiler FieldsFit/strict-end-PC/initial-state fit remain distinct premises until fixed-instance proofs discharge them. The raw span output fits2^logicalLength; its strict separation from wordWidth justifies packet+1, whereas raw physical cells are never tagged.
- Final whole queryBudget is the closed837572-instruction source-size expression; this reader leaf has the exact small fixed budget above. No native Lean runtime claim.

Completion:
- Report Status: CANDIDATE_COMPLETE only after all local rows close, with I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

Verification:
- Coordinate one Lean process with root/numeric_span/metadata_width. Use narrow checks and abstraction boundaries; do not repeat a whole-evaluator simplification after an unexplained timeout.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 067b6ffd350aee08f1496335ce957895f0da3fcc..HEAD after integration. No staging/commits.

Report:
- Complete numeric-bound/source-safe/static-field/actual-run propositions, all assumptions and discharged canonical inputs, frozen matrix evidence, source hashes, proof digestion and proposed design rationale.
