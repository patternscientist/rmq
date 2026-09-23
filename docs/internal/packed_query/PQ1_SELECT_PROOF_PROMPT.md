Make the title of this chat exactly: (PQ1-SEL) Prove all scalar select routes

Worker identity:
- Handle: PQ1-SEL
- Fresh or returning worker: RETURNING metadata_width after PQ1-L, actual runtime catalog verified current.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: b0af10d14121c7b11a7d3eb7cb1515c618a0da4b
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ; shared worker continuation, no branch/worktree changes.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_SELECT_PROOF_REPORT.md
- You are not alone; preserve other edits. No staging/commits/shared-ledger edits.

Roadmap contract:
- Node/join: Both initial endpoint selects in the full primitive RMQ query must consume the same canonical allocation, with dense, long-exception and sparse-exception paths proved.
- Local owned rung: Prove every SelectSource routine semantically correct, with ordered raw reads, register frames, fixed primitive budget and canonical all-size consumers. Reader correctness is already derived; rank proofs are an independent producer feeding this leaf's final join.
- Roadmap-node closure condition: Lead joins full query/LCA and canonical scalar word safety; this leaf closes select semantics and actual primitive budget, not whole-query safety or capstone.
- Goal: Prove selectCloseBlock reader agrees with packedSelectCloseLeaf on every canonical shape/index, consuming actual concrete reader/rank proofs and retaining exact ordered raw reads.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/SelectProof.lean and checked SelectSource.lean, ReadInterface.lean, RankProof.lean.
- Write scope: RMQ/Core/WordRAM/Packed/SelectProof.lean; RMQ/Core/WordRAM/Packed/SelectSource.lean; docs/internal/packed_query/PQ1_SELECT_PROOF_MATRIX.md; docs/internal/packed_query/PQ1_SELECT_PROOF_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze requirements; prove select-entry and chunked word-select first using stable ReaderCorrect/ReaderWrites; derive dense/long/sparse/whole select from those and rank proofs produced independently by numeric_span; instantiate actual reader and canonical metadata; consume Compiler. The source and reader contracts are already fixed and checked in the shared tree. Rank correctness is not a precondition for the independent entry/select-word proofs; the final canonical join must wait for and consume the checked rank producer. No output-dependent choice gates evidence collection.
- Non-goals: Changing ISA or physical reader; full LCA/query source; asserting numeric instruction safety without proof. Full machine-width safety is a later join and is not a semantic/budget hypothesis.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-SEL-WORD, REQ-SEL-ENTRY, REQ-SEL-WHOLE, REQ-SEL-RUN, CHK-SEL-LEAN, INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-ALL-SIZE, INV-PROOF-SEPARATION, INV-INSTRUCTION-ATOMICITY.
- REQ-SEL-WORD: Prove selectWordBlock returns the Option Nat packet for the exact bpChunkedWordSelectTraceResultAtSegmentsWithStore on segment21/22, false target, metadata chunk width, arbitrary input word and occurrence; actual raw receipts equal logicalTraceReads of that trace and the trace satisfies ReadOnlyTrace. Cover empty/ragged words, the intentional one-chunk zero-length fold, all eight guarded copies, early success and unsuccessful full traversal. The implementation's absent select-table reply uses default0 and still returns a present selected offset, matching the existing supplied-store protocol.
- REQ-SEL-ENTRY: Prove selectEntryBlock performs all four logical reads before checking presence and returns the exact four decoded fields/presence of packedSelectEntryRead, with exact ordered receipts and caller/metadata frames. Cover missing fields at each position and present zero fields without conflating presence and value. Static register/segment hypotheses on generic parameterized blocks are allowed but must be discharged for bases560/590, indices514/515 and segments1/5 used by selectCloseBlock.
- REQ-SEL-WHOLE: Prove denseSelectBlock and selectCloseBlock agree with packedDenseTwoWordSelectRead and packedSelectCloseLeaf respectively, for every canonical shape and query index. Include out-of-range rejection, both dense words, nonzero long/sparse exceptions and all seed-presence branches. The final canonical theorem consumes logicalReadBlock_correct and checked RankProof theorems; do not leave desired select correctness, rare-count-zero, successful-read, readiness or minimum-size assumptions in it. Preserve source ABI and repair any precise source defect within ownership.
- REQ-SEL-RUN: Expose WritesOnly and frame theorems sufficient for the LCA/full-query caller, preserving all independent banks and metadata through every call. Derive uniform source size formulas and actual compiled standalone/hosted or halt-appended consumers with exact result packet, exact ordered raw receipts and syntax-derived constant primitive instruction budget. All fields concern the same evaluation/run on the same memory; no select/rank/chunk macro charge replaces primitive instructions.
- CHK-SEL-LEAN: Narrow Lean and independently spelled expected-type consumers, empty/one-word/ragged/missing/exception branches. Hygiene and whitespace checks; no native_decide, proof callbacks, semantic answer precomputation or full-machine width claim from unbounded scalar semantics alone.
- Freeze all rows and inherited invariant wording verbatim; quote exact propositions and object-composition chains for closure, not only theorem names.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply to any claimed campaign; no campaign assigned.

Forbidden shortcuts:
- Do not stop at word-select or a conditional whole-select helper. Those are intermediate checkpoints; the final canonical all-size select theorem and actual-run consumer must close before CANDIDATE_COMPLETE.
- Do not alter reader/rank source or proofs owned by other workers. Communicate required interface lemmas to numeric_span/root.

Context:
- SelectSource.lean was authored by root and passed a clean Lean check. It statically inlines reader/rank blocks. Input close index512, result packet513; selectWord400..411; dense640..659; entries560..570 and590..600. See docstrings for full banks.
- Root's logicalReadBlock_correct shape : ReaderCorrect shape (shapeMemory shape) logicalReadBlock is checked; logicalReadBlock_writesOnly and actual reader run consumer are being finalized. ReaderCorrect includes status, packet, actual length, exact readerReceipts and ReaderFrame.
- numeric_span owns RankProof/RankSource/ChunkArithmetic append proofs. Coordinate API names; complete your independent word-select and entry proofs while its whole-rank join proceeds.
- The reference lives in RMQ/Core/SuccinctFinal/RAM/PackedCellProbe/ReadProgram.lean; select leaf2133, record-free entry357/dense479/select608. Supplied-store chunk-select is ChargedRankSelectTrace.lean322/351. Option result encoding is0/pos+1.

Completion:
- Report Status: CANDIDATE_COMPLETE only when every assigned local row closes, and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

Verification:
- Coordinate the single Lean slot with root/numeric_span/primitive_calculus. Narrow local module checks, not broad Lake builds.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check b0af10d14121c7b11a7d3eb7cb1515c618a0da4b..HEAD after integration. No staging/commits.

Report:
- Full source/value/ordered-read/frame/actual-run propositions, exact budgets, hypotheses, matrix evidence, proof digestion, source hashes/HEAD, design proposal and remaining whole-query joins.
