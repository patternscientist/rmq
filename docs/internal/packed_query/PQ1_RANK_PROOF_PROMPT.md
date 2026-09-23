Make the title of this chat exactly: (PQ1-R) Prove the compiled rank routines

Worker identity:
- Handle: PQ1-R
- Fresh or returning worker: RETURNING numeric_span after PQ1-LS, actual runtime catalog verified current.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with required rmq-proof-sprint and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: b0af10d14121c7b11a7d3eb7cb1515c618a0da4b
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ, shared-worker continuation. Do not change branches/worktrees.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_RANK_PROOF_REPORT.md
- You are not alone; preserve all other work. No staging/commits or shared-ledger edits.

Roadmap contract:
- Node/join: The full select and LCA controller must consume compiled rank correctness, including long/sparse flag rank and BP close rank on the same counted allocation.
- Local owned rung: Complete value, ordered raw-read, frame and actual compiled fixed-budget proofs for rankWordBlock, rankBlock and each metadata-configured rank wrapper.
- Roadmap-node closure condition: Lead instantiates the proved concrete reader, derives all arithmetic safety and joins full select/LCA/query. This rank leaf does not close the whole capstone.
- Goal: Prove rank source execution agrees with the existing charged logical rank interpreter and derive same-execution primitive value/receipt/fixed-cost corollaries, for arbitrary canonical shape and position including empty and sentinel cases.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/RankProof.lean importing RankSource, ReadInterface and existing E1RankBridge/ReadProgram; RankSource source ABI is fixed.
- Write scope: RMQ/Core/WordRAM/Packed/RankProof.lean; RMQ/Core/WordRAM/Packed/RankSource.lean; RMQ/Core/WordRAM/Packed/ChunkArithmetic.lean (append frame/static/proof lemmas only); docs/internal/packed_query/PQ1_RANK_PROOF_MATRIX.md; docs/internal/packed_query/PQ1_RANK_PROOF_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Frozen source/reader interfaces already supplied in this shared tree, without dependency on concrete reader correctness; freeze matrix; prove generic frames and one chunk iteration; prove bounded eight-copy fold; join whole rank and canonical wrappers; use generic Compiler for exact actual runs. Root independently proves concrete ReaderCorrect in PhysicalRead. Every producer precedes its consumer, and no output-dependent decision gates evidence collection.
- Non-goals: Full select/LCA source, concrete physical reader changes, blanket assumptions of compiled rank correctness, or closing the whole-query safety row. Numeric instruction safety is a subsequent separate join; semantic values/receipts and actual primitive budget must close here.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-R-FOLD, REQ-R-WHOLE, REQ-R-FRAME, REQ-R-RUN, CHK-R-LEAN, INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY, INV-TRACE-EXECUTION, INV-READ-BACKING, INV-ALL-SIZE, INV-PROOF-SEPARATION, INV-INSTRUCTION-ATOMICITY.
- REQ-R-FOLD: Under ReaderCorrect shape memory reader and ReaderWrites reader, prove the fixed rankWordBlock returns exactly bpChunkedWordRankTraceResultAtSegmentWithStore at segment21, chunk width from canonical metadata, target encoded as0/1, on arbitrary input bits and limit. Actual ordered receipts equal logicalTraceReads of that old trace, and prove ReadOnlyTrace for that trace so no primitive/synthetic event is discarded. Cover zero limit, ragged words, zero-count boundary behavior and all up-to-eight chunks. No hypothesis that the eight-copy loop already matches the specification.
- REQ-R-WHOLE: Prove rankBlock agrees with WordRAM.packedRankRead for all supplied numeric geometry and canonical metadata, on every position, without successful-read hypotheses. All three seed reads occur before presence guards, and the missing-seed branch returns0 after those reads. Derive canonical rankCloseBlock, rankLongBlock and rankSparseBlock exact values/ordered receipts for every shape and position on the same memory, with canonical metadata bank and reader hypotheses only. No empty-size, rare-count-zero, single-word or readiness premise.
- REQ-R-FRAME: Expose sufficient source frame and WritesOnly theorems so rank preserves metadata, caller inputs outside declared output/scratch/reader banks, and any independent select/LCA bank. Prove metadata survives each read/iteration, rather than assuming it for successive calls. Preserve fixed input/output ABI from RankSource; if a semantic defect requires source correction, show the precise defect and repair inside ownership.
- REQ-R-RUN: Use the generic compiler theorem on these exact source blocks to obtain actual hosted/standalone or appended-halt execution results, ordered raw receipts and uniform primitive instruction budgets from the proved source size. No cost charged as a rank/chunk/domain macro. Each canonical wrapper needs a typed actual-run consumer; static-width safety is explicitly a later join, not an assumption used to obtain value or budget.
- CHK-R-LEAN: Narrow module and independently spelled expected-type consumers, plus empty/ragged/missing-seed boundaries. Hygiene and whitespace checks; no native_decide, semantic callback in program, or claimed full-machine safety without proof.
- Freeze verbatim rows and inherited invariants, quote full propositions and same-object composition in evidence. Replays are only required for a campaign claimed as evidence; no campaign assigned.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply to any claimed campaign; none assigned here.

Forbidden shortcuts:
- Do not replace the source loop with the old rank function, a unit-cost domain instruction or a proof-carried answer. Reader is a compile-time Block inlined into code; its semantic proof interface cannot be evaluated by the machine.
- Do not change frozen acceptance to a helper-only endpoint. Continue until every assigned rank routine and actual-run consumer closes or a precise formal obstruction is established.

Context:
- Root-owned ReadInterface now includes ReaderCorrect = running/value packet/actual length/exact readerReceipts/ReaderFrame; ReaderWrites is an independent syntactic frame obligation. readerReceipts uses reviewerLogicalSpan and spanAttemptReceipts. logicalTraceReads flatMaps old read occurrences; separately required ReadOnlyTrace rules out erasing other events.
- RankSource inputs rankWord256..259,out260; whole352..359,out360; reader8192/8193 ->8194/8195, local scratch through8270. Metadata16..189, chunk width34. rankWord size501+8*reader.size; whole551+11*reader.size. See RankSource for exact banks.
- ChunkArithmetic already proves chunkSlotBlock and chunkRankBlock source output and actual wrapper, and equality to bpWordRankChunkSlotAt/bpChunkRankOfEntry. Use Frame.Block.eval_frame for preserved registers; you own append lemmas there only through ChunkArithmetic, not Frame. E1RankBridge supplies numeric/list chunk conversion and accumulator trace lemmas.

Completion:
- Report Status: CANDIDATE_COMPLETE only when every local row closes, with I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

Verification:
- Coordinate the single Lean slot with root, metadata_width and primitive_calculus. Use local cache and narrow targets, not broad Lake builds.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and final integrated diff checks. No staging/commits.
- Lead runs git diff --check b0af10d14121c7b11a7d3eb7cb1515c618a0da4b..HEAD after integration.

Report:
- Exact source/value/trace/frame/run propositions, budgets, assumptions, matrix evidence, proof digestion, conceptual changes and remaining whole-query joins. State exact HEAD/source hashes and no staging/commits.
