Make the title of this chat exactly: (PQ1-S) Prove numeric repacked span decoding

Worker identity:
- Handle: PQ1-S
- Fresh or returning worker: FRESH proof subagent with disjoint ownership in the governed lead worktree.

Skill:
- Use $rmq-proof-sprint before starting; read canonical completion gate and relevant failure modes.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run scripts/project_skill_preflight.ps1 against this ref with rmq-proof-sprint required and your actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 4639223bc8130b0ef752270b5cbdd74325abcd60
- Use existing branch codex/fully-charged-packed-query-v1 and worktree C:/Users/poin/.codex/worktrees/a84a/RMQ. Do not create another worktree or switch the shared branch.
- DensePacking.lean is a lead-owned, compiled additive interface. Do not modify it without agreement.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_SPAN_REPORT.md
- You are not alone; do not revert or overwrite other changes. No staging/commits; the lead owns integration.

Roadmap contract:
- Node/join: fullyChargedPackedQueryCapstone_holds consumes this numeric old-cell loader through actual primitive execution on the repacked allocation.
- Local owned rung: Universal numeric one/two-cell span decoder and old-cell identity for the exact new dense-repacking definition, preserving absent and zero-length behavior.
- Roadmap-node closure condition: Lead must still prove primitive execution, complete RMQ control, same-allocation space/width/cost and public acceptance; this leaf alone is not the milestone.
- Goal: Prove numeric span decoding and the repacked old-cell equality, including conditional physical plans and malformed/absent reads, without a semantic executable callback.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/Span.lean; signatures below may be elaboration-adjusted without weakening conclusions.
- Write scope: RMQ/Core/WordRAM/Packed/Span.lean; docs/internal/packed_query/PQ1_SPAN_MATRIX.md; docs/internal/packed_query/PQ1_SPAN_REPORT.md; docs/internal/DESIGN_DECISIONS.md (supply a proposed append to lead rather than concurrent writing).
- Lifecycle dependency order: Read compiled DensePacking, freeze leaf matrix, define numeric decoder and prove universal list/numeric refinement, prove exact repack loader and direct consumers, report; lead compiles it to primitive instructions and joins whole query later. No evidence-dependent choice gates this leaf.
- Non-goals: Primitive machine execution, canonical metadata schema, whole-query budget, public claims, or unrelated refactors.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-S-SPAN, REQ-S-REPACK, REQ-S-PLAN, CHK-S-LEAN, INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY, INV-READ-BACKING, INV-PROOF-SEPARATION, INV-NO-SYNTHETIC, INV-CATEGORY-SEPARATION.
- REQ-S-SPAN: Define spanPlan width position len as zero addresses for len=0, one for a contained nonempty span, two consecutive addresses for a crossing. Define decodeSpanNat on List Nat only, using each planned numeric cell and scalar shift/division/remainder/mask arithmetic. For positive width, uniform full-width bit cells, len<=width and position+len<=cells.length*width, prove decoding their numeric map returns some(bitsToNatLE(cells.flatten.drop position |>.take len)). Include the zero-length endpoint at the end of memory. Missing required physical cells return none.
- REQ-S-REPACK: Define loadOldCellNat headerCount width oldWidth oldCount memory index with only numeric scalars/memory. Guard index<oldCount, read span headerCount*width+index*oldWidth of length oldWidth. For every numeric header list fitting width, every old bit-cell list uniformly oldWidth, and 0<oldWidth<=width, prove loadOldCellNat headers.length width oldWidth old.length (repackWords headers width old) index = (old[index]?).map bitsToNatLE for every index. No shape, old-memory oracle, proof field or desired reply may enter the executable loader.
- REQ-S-PLAN: Prove the plan length<=2, exact read backing and preservation of missing/zero-length cases at this functional read layer. State clearly that primitive instruction execution is the lead's later consumer, not established by a pure decoder theorem.
- CHK-S-LEAN: Elaborate Span.lean and kernel-checked concrete consumers for noncrossing, crossing, final padded cell, zero-length end, absent required physical read, absent old-cell index and all-ones raw cell without +1 overflow.
- Freeze matrix from docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md and copy these requirements plus assigned inherited invariant text verbatim before proof edits. Exact theorem statements/objects/direct consumers and anti-vacuity challenges are required.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE remain applicable to any claimed campaign; none is assigned beyond the kernel examples. Do not claim report-only mutations.

Forbidden shortcuts:
- No trust shortcuts, semantic callbacks, full-cell +1 tag, host answer, uncharged primitive execution claim, or widening old cells without repacking.

Context:
- Read AGENTS.md and E1 roadmap. Existing DensePacking has denseCells_flatten, denseCells_cell_length, uniform_flatten_slice, span_from_two_cells, repackWords and complete generic capacity bound.
- E1RankBridge has bitsToNatLE_drop and bitsToNatLE_take; E1FringeBridge has bitsToNatLE_append. Existing ReviewerProbe is a specification/proof pattern, not the new numeric machine.
- Existing .olean/.ilean artifacts were copied independently from RC6 into local .lake/build/lib/lean; use only this local library path. One heavy Lean process at a time: request the build slot from lead before checking.

Completion:
- Continue until all leaf requirements close or a real external blocker occurs. Proposed local lemmas must be consumed in loadOldCellNat_repacked before submission.
- Report begins Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required. This declaration is only for the bounded span leaf.

Verification:
- Narrow standalone Lean elaboration against local copied cache; coordinate build slot. Hygiene and working diff check on owned files.
- Lead owns final scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 4639223bc8130b0ef752270b5cbdd74325abcd60..HEAD after integration; no full gate for this leaf.

Report:
- Exact declarations/propositions, evidence matrix, branch/worktree/base, test outcomes, and proof digestion: conceptual change, plain English, assumptions and skeptical questions. No commit yet; lead integrates.
