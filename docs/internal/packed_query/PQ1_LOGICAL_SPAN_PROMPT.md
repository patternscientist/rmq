Make the title of this chat exactly: (PQ1-LS) Recover every logical word from packed spans

Worker identity:
- Handle: PQ1-LS
- Fresh or returning worker: RETURNING numeric_span proof subagent; runtime catalog current from PQ1-SA.

Skill:
- Use $rmq-proof-sprint and canonical completion gate.
- Workflow-governance ref: 4639223bc8130b0ef752270b5cbdd74325abcd60.
- Run project_skill_preflight.ps1 with rmq-proof-sprint required and actual runtime catalog.

Checkout contract:
- Task mode: WRITE
- Exact base/target commit: 9e2720b991e203d22a2787abf66dbfb9888088fb
- Use existing codex/fully-charged-packed-query-v1 at C:/Users/poin/.codex/worktrees/a84a/RMQ without changing branches or worktrees.
- Durable completion artifact: mode=WORKER_REPORT; path=docs/internal/packed_query/PQ1_LOGICAL_SPAN_REPORT.md
- You are not alone; preserve all others' work. No staging/commits or shared-ledger edits.

Roadmap contract:
- Node/join: The fixed metadata-driven location and span assembly must return the exact legacy logical word on the new counted allocation, covering every segment and index.
- Local owned rung: A universal numeric span geometry and same-allocation canonical logical-read refinement, preserving both numeric value and actual bit length, including empty sentinels and absent words.
- Roadmap-node closure condition: Lead proves metadata-source assembly equals this geometry, compiles the full controller and closes widths/cost. This leaf closes canonical geometry/bit decoding only.
- Goal: Define reviewerLogicalSpan, prove its descriptor/old-plan correspondence, and prove direct span decoding from shapeMemory agrees with every canonical logical-store reply as a (value,length) option.
- Required theorem/file/tool: RMQ/Core/WordRAM/Packed/LogicalSpan.lean importing RegularLocate, Span, Allocation and the existing reviewer correctness modules. RegularLocate.NumericSpan is fixed, fields position/length; no edits to that module.
- Write scope: RMQ/Core/WordRAM/Packed/LogicalSpan.lean; docs/internal/packed_query/PQ1_LOGICAL_SPAN_MATRIX.md; docs/internal/packed_query/PQ1_LOGICAL_SPAN_REPORT.md; docs/internal/DESIGN_DECISIONS.md (propose append to lead).
- Lifecycle dependency order: Freeze definitions/matrix, derive regular/interior old geometry, prove arbitrary valid repacked bit-span recovery, prove all canonical logical words/value/length including absence; report actual universal consumers. Communicate the reviewerLogicalSpan interface early.
- Non-goals: Primitive source blocks, new allocation/schema, full RMQ control, final machine-width or capstone claim.
- Current-surface inventory: NOT_APPLICABLE.
- Current-source-comment inventory: NOT_APPLICABLE.
- Dependency-surface inventory: NOT_APPLICABLE.

Acceptance contract:
- Frozen acceptance IDs: REQ-LS-GEOMETRY, REQ-LS-RECOVERY, REQ-LS-CANONICAL, CHK-LS-LEAN, INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY, INV-PROOF-SEPARATION, INV-READ-BACKING, INV-ALL-SIZE.
- REQ-LS-GEOMETRY: reviewerLogicalSpan (n lc sc segment index : Nat) : Option NumericSpan is a proof-free scalar geometry specification. For segment20 use the existing interior classifier and its closed bit address/read width. For every other segment<23 use regularDescriptor's four fields (base,bits,stride,count) through regularSpan; outside23 return none. Prove this span produces the old packedReviewerLogicalPlan via old-width spanPlan and old decode expression, for every n/counts/segment/index, with exact value and logical length on canonical memory. Prove each present span length<=oldWidth and handle zero-width positions without a false end-of-memory premise.
- REQ-LS-RECOVERY: Prove universal direct bit-span recovery from repackWords headers W old for positive W, len<=W and position+len<=old.flatten.length (or len=0), not just aligned old cells. The decoded result is bitsToNatLE ((old.flatten.drop position).take len), using decodeSpanNat W (headers.length*W+position) len on that same memory. Numeric physical cells remain raw and no double-width runtime concatenation appears.
- REQ-LS-CANONICAL: Define directLogicalReadNat n lc sc memory segment index using reviewerLogicalSpan; for some span, decodeSpanNat (wordWidth n) (metadataWordCount*wordWidth n+span.position) span.length memory and return (decoded,span.length), otherwise none. For every canonical shape and every segment/index, prove it equals the canonical global ReadStore reply mapped to (bitsToNatLE bits,bits.length), and consequently the existing packedReviewerLogicalRead reply under a request with those segment/index fields. No successful-read, readiness, count-zero, one-macro, one-word-entry, or minimum-size hypothesis. Expose descriptor equations the lead's source assembler can consume.
- CHK-LS-LEAN: Narrow checks, exact-type consumer over every canonical segment/index, empty/singleton and dead-interior/empty-sentinel typed consumers. Do not use fixtures as universal evidence or native_decide.
- Freeze matrix with verbatim rows and assigned inherited invariants from completion gate. Evidence quotes exact propositions and concrete object-composition chain.
- REPLAY-EXACT-REGISTRY, REPLAY-SELECTOR-NONVACUITY, REPLAY-SUBPROCESS-DEADLINE apply only to a claimed campaign; none is assigned.

Forbidden shortcuts:
- No semantic store or desired answer enters directLogicalReadNat. No proof-valued runtime data. Do not identify old physical probe occurrences with new physical occurrences: direct repacked spans have their own addresses. Preserve logical request order when later composed; physical trace is generated by SpanAssembly.

Context:
- Prior plan considered recovering two old cells before decoding a logical span. The now-checked direct span assembly makes that intermediate unnecessary: lead selects direct repacked spans, preserving the same old absolute bit geometry and canonical logical value/length. Lead records this decision. Your old-cell recovery remains useful but is not relabeled as the new theorem.
- RegularLocate.regularSpan computes some(base+index*stride,min stride(bits-index*stride)) iff index<count. RegularLocate's generic19-instruction source is green. Lead owns fixed descriptor selection and InteriorLocate source.
- Metadata contains42scalars, regular descriptors at42+4*segment, interior at134+5*tag. Empty logical sentinels in11/15/19 are present with zero bits; respect separate count.
- Existing ReviewerControllerProof has per-source canonical read equalities, complete logicalRead equality and successful plan-fetch theorem; ReviewerProbe has probePlan_decode; ReviewerInteriorRead has component classifier soundness and read-width bounds. Reuse them to avoid re-proving payload theory.

Completion:
- Continue until every assigned row closes, with no easier alternate endpoint. Report Status: CANDIDATE_COMPLETE and I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required, for this bounded leaf.

Verification:
- Coordinate one Lean process with lead/metadata_width/primitive_calculus; local build tree only.
- Lead owns scripts/design_decision_check.ps1 -Strict -Base 4639223bc8130b0ef752270b5cbdd74325abcd60 and git diff --check 9e2720b991e203d22a2787abf66dbfb9888088fb..HEAD after integration.

Report:
- Exact definitions, complete theorem propositions, branch/base/worktree, evidence ledger, proof digestion and limitations. No staging/commits.
