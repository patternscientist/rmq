# R1 A07 Blocking-Finding Repair Worklog

Worker: R1

Branch: `codex/r1-a07-blocker-repairs-r1-restart`

Worktree: `C:\Users\poin\.codex\worktrees\81a9\RMQ`

Exact base: `1a825f3a940f0ff59084b69b25ba0c318569f33f`

Workflow-governance ref: `cdb134b5b62b9d4030cf12c583c4836f8c0f95e4`

## Governed preflight

The required `rmq-proof-sprint` role skill was read together with
`references/COMPLETION_GATE.md` and the relevant known-failure modes. The
governed preflight ran before substantive work:

```text
powershell -ExecutionPolicy Bypass -File scripts\project_skill_preflight.ps1
  -GovernanceRef cdb134b5b62b9d4030cf12c583c4836f8c0f95e4
  -RequiredSkills rmq-proof-sprint
  -RuntimeProjectSkills rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
Exit 0: SKILL-PREFLIGHT: PASS
checkout = 1a825f3a940f0ff59084b69b25ba0c318569f33f
expected/checkout/working/runtime skills =
  rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
```

## R1-R1 continuation: governed preflight and frozen repair contract

Worker: R1-R1

Requested title: `(R1-R1) Close the A07 repair acceptance gaps`

Continuation base: `6155d48dde13dfc8e4b3da108b4b81e258300b86`

The continuation began on the required branch
`codex/r1-a07-blocker-repairs-r1-restart` with a clean worktree and exact HEAD
`6155d48dde13dfc8e4b3da108b4b81e258300b86`. The governing skill and its
completion gate were re-read, including the occurrence-information-preservation
rule and the W18 regression in `KNOWN_FAILURE_MODES.md`. Before substantive
repair work, the governed preflight was rerun:

```text
powershell -ExecutionPolicy Bypass -File scripts/project_skill_preflight.ps1
  -GovernanceRef cdb134b5b62b9d4030cf12c583c4836f8c0f95e4
  -RequiredSkills rmq-proof-sprint
  -RuntimeProjectSkills rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
Exit 0: SKILL-PREFLIGHT: PASS
checkout = 6155d48dde13dfc8e4b3da108b4b81e258300b86
expected/checkout/working/runtime skills =
  rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
```

Named target: strengthen the existing public same-block occurrence theorem in
place so that destructuring its proposition retains one identical local
occurrence across the whole-query producer, exact `.canonicalClose 1 1`
invocation, component trace, and charged same-block subtrace; make that theorem
a load-bearing field of the existing manifest packet; then repair the remaining
evidence-tier, current-prose, validator-attestation, and committed-ledger gaps.

Downstream consumer: the existing
`ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` packet, which is
the first conjunct of `RMQ.Headlines.listIntSuccinctRMQPaperMainTheorem`. No
sibling packet or unused wrapper is acceptable.

Hard obligation: the strengthened conclusion itself, rather than witness
choices erased inside its proof, must expose the actual third instruction,
folded pre-state, local position, global offset, exact invocation, and both
component occurrences. The current validator facts at global positions `0`
and `15` and instruction positions `0` and `1` must remain nonvacuous and must
be rerun after the final transitive Lean change.

Forbidden shortcuts: a hidden receipt-local existential, `List.Mem`, equal
event values, or two unrelated existentials do not establish occurrence
identity; command or executable evidence is not kernel evidence; pre-change
validation cannot certify a changed consumer; no passing R1-A/B/D/E theorem or
public identity may be weakened. The replay IDs remain `NOT_APPLICABLE` because
this continuation introduces no mutation replay harness.

Valid stop conditions remain exact target closure, a checked obstruction on
the frozen proposition, a genuine external blocker, or an explicit coordinator
redirect. A helper theorem, build, executable run, or commit is only a
checkpoint.

### Frozen R1-R1 requirement-to-evidence matrix

These rows are frozen before the first R1-R1 implementation or public-prose
edit. Only evidence, status, and an explicitly approved amendment may change.

| ID | Exact frozen requirement | Intended exact evidence | Consumer / identity chain | Anti-vacuity challenge | Evidence obtained | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `REQ-R1R1-C-IDENTITY` | "Strengthen the existing theorem proposition in place. Expose enough checked data to identify the same occurrence across all layers" and make the exact proposition let a downstream consumer recover "one indexed whole-query event, its instruction/folded pre-state/local position/invocation, and the same charged same-block subtrace event"; strengthen the existing manifest/public consumer so it consumes this proposition. | The existing `concreteBPNativeSuccinctRMQSingleton_sameBlockFringeChunk_indexed_occurrence_receipt` conclusion retains a shared `globalPos`/`localPos` and concludes `ProducesEventAt ... globalPos 2 (.lcaClose ...) reviewerSingletonBeforeLCAState localPos`, exact `InvokesReviewerRead ... (.canonicalClose 1 1)`, the global-offset equality, and both invocation/component and charged-same-block `getElem?` facts at that same `localPos`. The existing manifest structure has a field with this exact strengthened proposition, initialized by this theorem. | valid `[7]`, `[0,1)` -> whole-query instruction `2` and folded prefix state -> exact `.canonicalClose 1 1` -> invocation component trace at shared `localPos` -> charged same-block decoded trace at the same `localPos` -> manifest packet -> headline paper-main-theorem conjunct. | Destructure only the theorem conclusion and attempt to choose the receipt/component local positions independently. Closure requires the shared explicit `ProducesEventAt` and same `localPos` facts to make that impossible; proof-body witness choice or an unused wrapper fails. | Commit `233b6ca` strengthens the named theorem in place. Its checked conclusion shares `globalPos`, `localPos`, and `preState`; identifies `preState` with evaluation of `concreteBPNativeSuccinctRMQWholeQueryProgram.take 2`; concludes `ProducesEventAt` for instruction `2`, the literal `.lcaClose` instruction, and that `localPos`; states the prefix-trace-length offset equality; concludes `InvokesReviewerRead ... (.canonicalClose 1 1)`; and gives the invocation component, LCA component, and charged decoded same-block `getElem?` facts at the same local position. `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy.same_block_fringe_chunk_occurrence_retains_exact_identity` has this exact proposition and its constructor consumes the theorem; the packet remains the first paper-main-theorem conjunct. Focused builds exited 0 (reachability 41.034 s; semantic consumer 5.516 s). | Closed |
| `REQ-R1R1-F-TIER-LABELS` | Apply the matrices' evidence-tier convention consistently: B2 `REQ-B4-07`/`REQ-B4-08` and B6 `REQ-B6-06` are attested documentation/audit/prose-review evidence, while genuine theorem rows remain kernel-checked. Inspect neighboring non-kernel rows left as bare `Closed`. | The three named status cells, and any neighboring artifact-only row discovered by the scoped audit, visibly say `Closed (attested: <correct tier>)`; theorem-backed rows retain bare `Closed`. | Matrix row -> coordinator evidence reconstruction. | Relabeling every row indiscriminately or leaving a prose/audit artifact visually indistinguishable from a proposition fails. | B2 REQ-B4-07 is `Closed (attested: documentation artifact evidence)`, B2 REQ-B4-08 is `Closed (attested: audit and documentation artifact evidence)`, and B6 REQ-B6-06 is `Closed (attested: prose-review evidence)`. The convention now explicitly includes documentation/audit artifacts. Scoped inspection found no other neighboring artifact-only bare row: mixed B4-01 and public B3-10 have Lean proposition evidence; B6-03/04 and inherited neighbors are theorem-backed. | Closed |
| `REQ-R1R1-G-FINAL-EXECUTABLE` | Preserve the nonvacuous validator fixture at global positions `0` and `15`, actual producing program positions `0` and `1`, the actual folded state for the second instruction, successful equal reads, distinct positions, and neighboring indexed checks; run the executable after the last transitive change and again on the final clean candidate commit if later edits touched its inputs. | Source review preserves the literal fixture and `lake exe rmq_succinct_classic_validate` exits `0` after the final transitive Lean change and on the final committed tree. | `RMQ/Validation/SuccinctClassic.lean` -> compiled validator executable. | A module build, pre-change run, dynamic trace search, or comparison of an event with itself fails. | The validator source remains unchanged at the nonvacuous literals: global positions `0`/`15`, instruction positions `0`/`1`, actual folded second-instruction state, first trace length `15`, local-event/global-event equalities, successful equal reads, and distinctness. After the last transitive Lean change, `lake exe rmq_succinct_classic_validate` exited 0 in 7.011 s and validated 498 windows; that dirty diff was committed unchanged as `233b6ca`. The final committed-tree result is deliberately a response-only attestation run after the commit containing this ledger. | Closure determined by exact-HEAD response attestation |
| `REQ-R1R1-PUBLIC-FIXTURE-SYNC` | Update current prose from singleton positions `0`/`12` to `0`/`15`, name instruction positions `0`/`1` where useful, correct current `docs/ADD_PROVENANCE.md` so segment `21` is live and fresh rejected segment is `23`, search current docs for displaced claims, and update the stale gate comment from physical-payload/76 topology to live 207 topology without changing behavior. | `README.md`, `docs/ADD_PROVENANCE.md`, and `scripts/gate.ps1` contain the live facts; scoped current-doc search finds no unclassified current-facing stale literal/segment claim; frozen history is left intact. | Current public/provenance prose and gate commentary -> reviewer interpretation; gate executable behavior unchanged. | Rewriting historical snapshots or changing the gate command sequence fails; leaving another current-facing `0`/`12` or rejected-segment-21 statement fails. | `README.md` and current `docs/ADD_PROVENANCE.md` now say global positions `0`/`15` and producing instructions `0`/`1`; ADD provenance records 22 live physical sources, live counted segment `21`, and rejected fresh segment `23`. Scoped search leaves old values only in frozen audit/matrix/decision history or the verbatim R1-R1 requirement. The `scripts/gate.ps1` comment names canonical reviewer-payload/readWord-only/derived-207 topology; no command changed. Claim drift exited 0 with 745 hits and zero strict failures; topology lint passed 83/49. | Closed |
| `COMPLETE-R1R1-COMMITTED-EVIDENCE` | Correct the contradiction where committed hygiene is marked Closed while final-command rows remain Pending; add an exact-candidate result section; distinguish pre-repair scheduling evidence from commands run after the last relevant change; no row may remain Pending when `CANDIDATE_COMPLETE` is claimed. | Durable ledger records the semantic/Lean commit certified by each result, identifies final post-commit attestation as response-only when necessarily later than the ledger commit, contains no `Pending` final rows at candidate report time, and the final response names exact SHA, exit, duration, and clean state for every required command. | Frozen matrix -> committed worklog -> exact final worker response -> coordinator re-audit. | Backdating a command to a later commit, calling response-only evidence committed, or marking an unrun row Closed fails. | The material repair is committed as `233b6ca`; the frozen contract is `012862e`; the authorized comment-only workflow rationale is committed as `f6ce2d2`. The governed preflight at `92aec45` passed, and the strict decision check against `6155d48` then exited 0 in 3.1 s on `f6ce2d2`. This ledger intentionally does not backdate the final exact-HEAD checks or aggregate gate: those are run after the ledger commit and reported with the exact candidate SHA as response-only attestation. The original 6155 results below remain scheduling/cache evidence only. | Closure determined by exact-HEAD response attestation |
| `INV-R1-ABDE-PRESERVATION` | Preserve all passing R1-A, R1-B, R1-D, and R1-E theorem behavior, the half-open leftmost `List Int` semantics, and the frozen public identities. | Focused/direct-consumer builds plus both durable axiom scripts elaborate the unchanged answer-dependency and distinct-instruction propositions; public builds and claim/topology checks remain green; no renamed/deleted identity or cost/payload/execution change appears in the exact-base diff. | R1-A inventories, R1-B `.value ≠`, R1-D receipts, R1-E public surfaces -> existing capstone. | Weakening R1-C by changing a shared base receipt, altering R1-B/D types, or moving the route/payload/cost object fails. | The repair changes only the R1-C theorem conclusion and adds its exact manifest field; the R1-B answer-dependency module and R1-D repeated-read theorem types are untouched. Focused semantic builds, `lake build RMQPaper RMQExamples` (exit 0, 25.102 s), the post-change validator (exit 0, 7.011 s), and `lake build RMQ` before commit (exit 0, 6.907 s) preserve the direct consumers. Final axiom inventories and documentary checks are assigned to the exact-HEAD response attestation. | Closure determined by exact-HEAD response attestation |
| `INV-CATEGORY-SEPARATION` | Preserve the distinctions among payload bits, proof-only data, modeled ticks, traces, physical allocation, and Lean runtime; do not call process/executable evidence kernel evidence. | R1-C closure is a checked proposition consumed by the manifest; validator and command rows are labeled executable/attested; documentation makes no new payload/allocation or runtime claim. | Theorem packet and evidence matrices -> public claim interpretation. | Using the validator `#guard` or gate transcript as proof of occurrence identity fails. | The shared occurrence identity is a kernel-checked proposition and a mandatory manifest field. Validator results, matrix audits, prose review, command transcripts, and the eventual gate are explicitly labeled attested evidence; no payload, allocation, cost, or runtime theorem changed. | Closed |
| `DEFER-R1R1-COORDINATOR-REAUDIT` | Coordinator exact-commit re-audit and any integration are explicitly deferred until after this worker reports a candidate. | Final report names the exact candidate and makes no acceptance, integration, publication, push, or merge-readiness claim. | Worker candidate -> coordinator-owned re-audit. | Worker self-acceptance fails. | Explicitly deferred and non-blocking. | Deferred |

Parallelization check: the join is one strengthened theorem type consumed by
one shared manifest structure. The theorem signature, constructor, inventories,
matrix evidence, and validator invalidation are causally ordered and share the
same public interface, so no independent write leaf would shorten the critical
path. This continuation proceeds single-threaded.

## Frozen target and stop conditions

Named target: repair every blocking finding from the external blind A07 audit
on the Option B charged route, now including the independently reproduced
validator regression R1-G, without changing E1-owned modules or weakening the
frozen charged-route contract.

Downstream join: coordinator reconsideration of the Option B charged-route
milestone. The same accepted public `List Int` query, public payload, logical
store, whole-query global trace, and derived literal `207` must remain the
objects composed by the capstone.

Hard obligations:

- a valid ordinary-list whole-query supplied-store witness whose returned
  `Option Nat` `.value` changes when one consumed segment-21 table cell alone
  changes;
- a valid singleton same-block whole-query segment-21 occurrence retaining
  global and local positions, producing instruction position, folded pre-state,
  exact invocation, and same-block component subtrace;
- repeated equal reads tied to two explicit, distinct producing instruction
  positions;
- durable axiom inventory, executable fixture, public prose, matrix-tier, and
  final unchanged-tree gate evidence.

Forbidden shortcuts: full-`TraceResult` inequality is not answer-value
dependency; component membership is not a whole-query occurrence receipt;
distinct trace positions are not distinct instruction positions; count-only or
vacuous replay evidence is not applicable; no frozen identity may be weakened,
renamed, or deleted.

Valid stop conditions are exactly target closure, a kernel-checked obstruction
or precise counterexample matching the frozen target, a genuine external
blocker, or an explicit coordinator redirect. A commit or green build is only a
checkpoint.

## Frozen requirement-to-evidence matrix

Prompt requirements and coordinator-assigned IDs below are frozen before the
first implementation edit. Only evidence, outcome, and status may change.

| ID | Exact frozen requirement | Intended exact evidence | Consumer / object chain | Anti-vacuity challenge | Evidence obtained | Status |
| --- | --- | --- | --- | --- | --- | --- |
| `R1-A` | "Update both requests to the live name. Then ADD durable inventory entries for the surfaces introduced by the recent campaign rungs that have none: the same-block charged fold, the same-block occurrence/liveness witnesses, and the corruption witnesses. Verify by running both scripts to exit 0 and recording the axiom sets." Coordinator amendment after freeze: "`scripts/axiom_check.lean` has TWO independent defects"; repair the stale identifier and its unavailable `RMQ.Core.GenericSelectBPCompat` import by either adding the module to the build closure or importing modules the library actually builds; also load-check `scripts/wordram_axiom_check.lean`; both scripts must actually load and exit 0. | Both scripts request `_sum_le_207`; `axiom_check.lean` imports only built/available modules (or the closure is deliberately expanded with rationale); each inventories the charged same-block fold/value/cost or trace surfaces, actual same-block occurrence/liveness theorem, corruption/value-dependency theorem, and strengthened repeated-read theorem; both Lean invocations load and exit 0 with recorded axiom sets. | Trust inventory -> `scripts/gate.ps1` fatal WordRAM step -> Option B candidate. | A green library with an unknown inventory constant or an unavailable import fails; declaration-name-only coverage that omits new surfaces fails; file text without successful load/exit is not evidence. | Commit `f315f9c`: both stale requests now name `_sum_le_207`; both scripts durably inventory the charged same-block cost/value/substitution/trace/store/no-synthetic surfaces, component and route liveness witnesses, and the same-block returned-close corruption theorem. The non-weakening closure choice adds `RMQUnionFind` and `RMQ.Core.GenericSelectBPCompat` to `RMQ.lean`, preserving all pre-existing UnionFind and BP-compat inventory rows instead of deleting them. `lake build RMQ` exit 0 (253 jobs); WordRAM inventory exit 0 in 78.430 s; broad inventory exit 0 in 151.142 s with 2,465 output lines. New entries report only `propext`, `Classical.choice`, and/or `Quot.sound` where nonempty; no `sorryAx` or `Lean.ofReduceBool`. Final-surface additions inventory the instruction-indexed C/D theorems plus `concreteBPNativeSuccinctRMQSingletonAnswerDependency_canonical_consumed` and `_value_ne`. The focused script initially exposed its missing explicit AnswerValueDependency import (exit 1, 115.173 s, exactly two unknown constants, no forbidden axioms); after the import repair it exited 0 in 105.951 s (796 lines). The broad script exited 0 in 203.662 s (2,478 lines). Both final-surface runs reported zero errors, zero `sorryAx`, zero `Lean.ofReduceBool`, and only `[]`, `[propext]`, `[propext, Quot.sound]`, or `[propext, Classical.choice, Quot.sound]`. | Closed |
| `R1-G` | "Recompute the correct positions from the actual post-campaign singleton trace and update the fixture so it checks the true positions, keeping the property it is meant to test — two DISTINCT global positions carrying the same successful read, arising from two distinct producing instruction occurrences. Do not weaken the fixture to a tautology, do not delete it, and do not make it position-agnostic; a concrete regression fixture with correct literals is the point. While you are there, verify the neighbouring checks in that file that also index trace positions and correct any that the campaign invalidated." | Concrete singleton validator uses post-campaign numeric global positions, confirms the same successful `readWord`, confirms distinct global positions, and checks the matching concrete producing instruction positions are distinct; neighbouring indexed fixtures reviewed; executable exits 0. | `RMQ/Validation/SuccinctClassic.lean` -> `rmq_succinct_classic_validate`. | Searching the trace dynamically, comparing a position with itself, or checking only event equality fails. | The fixture checks literal global positions `0` and `15`, confirms the same successful read at both, and checks literal program positions `0` and `1` are distinct `.selectClose` instructions. It also evaluates those actual two instructions at their folded states, checks their local event `0` against the respective global events, and pins the first instruction trace length to `15`, so the executable evidence ties the two reads to the two producer occurrences rather than merely inspecting unrelated program slots. Neighbouring physical index `7` remains valid; no other stale hard-coded logical trace index exists. The executable exits 0 in 98.683 s over 498 windows and reports the live principled bound 207; the strengthened compiled fixture builds successfully. | Closed |
| `INV-B4-VALUE-DEPENDENCY` | Inherited INV-VALUE-DEPENDENCY: "returned values and routing decisions depend on actual charged reads"; evidence conclusions "about the returned value, decisive state/route, or a refinement chain", with "evidence quantification and validity domain" matched and recorded. | Checked existential over `xs : List Int`, `left`, `right`, canonical store and a store differing at exactly one consumed segment-21 address: `ValidRange xs left right`, consumed indexed read, agreement elsewhere, and whole-query `WithStore(...).value != WithStore(corrupt...).value`. | Same `Cartesian.shape xs` -> accepted global read store -> accepted whole-query supplied-store evaluator -> `.value`; optional physical transfer only after logical projection closes. | Accepted predicate P is whole-query answer inequality on a valid query under one-cell corruption. Rejected Q is enclosing `TraceResult` inequality caused by its trace. Component-local close inequality alone also fails. | `concreteBPNativeSuccinctRMQSingletonAnswerDependency_value_ne` exhibits `xs = [7]`, `ValidRange xs 0 1`, the canonical LE1 word at segment `21`, index `3`, an indexed successful whole-query read of that exact cell, a supplied store returning LE4 there and agreeing at every other address, canonical `.value = some 0`, corrupt `.value = none`, and whole-query `.value ≠`. The initially recommended `(21,7)` LE21→LE18 route was rejected after exhaustive evaluation of all 32 five-bit replacements at that cell left the singleton answer `some 0`; the successful checked witness instead uses consumed `(21,3)`, LE1→LE4. The proof reduces the charged dense select structurally and derives consumption from ordered-footprint locality, not from record inequality or a component-only witness. | Closed |
| `REQ-B6-04` | "Provenance must cover the ACTUAL emitted same-block events (producing instruction + occurrence position), not merely assert segment membership; deleting the same-block case from the regenerated induction must break adequacy. The W19 witness must be a same-block query, not the existing cross-block one." | One checked valid singleton `List Int` whole-query witness with an indexed successful segment-21 read and `ReviewerReadOccurrenceReceipt`, plus explicit equality tying the receipt's invocation component trace to the charged same-block LCA subtrace. | singleton `ValidRange` -> third whole-query `lcaClose` instruction -> folded pre-state with equal closes -> `.canonicalClose` invocation -> same-block component trace -> global offset -> receipt/source/counting. | Accepted P is an actual successful closed-valid occurrence for leaf `.canonicalClose` with same-block invocation. Rejected Q is component `List.Mem` or source-level liveness reached by select/rank/cross-block. | R1-R1 strengthens the same named theorem without changing the witness object: the conclusion now exposes a shared folded `preState` and `localPos`, actual `ProducesEventAt` at program position `2`, the prefix/global offset equality, exact `.canonicalClose 1 1` invocation, and the invocation, LCA, and charged same-block trace events at that same local index. The existing manifest packet consumes this exact proposition in `same_block_fringe_chunk_occurrence_retains_exact_identity`, so the paper-main-theorem conjunct retains rather than erases the occurrence identity. | Closed |
| `REQ-B4-03` | "including B2's explicitly deferred item: occurrence granularity for REPEATED EQUAL fringe/table reads (distinct receipts for repeated equal reads, matching `repeated_equal_read_occurrences_have_distinct_receipts`). Extend the checked provenance packet(s) consumed by the paper chain rather than creating sibling packets." The two positions "must arise from two distinct program-instruction occurrences". | Public witness theorems expose `instrPos1`, `instrPos2`, their exact `ProducesEventAt`/receipt evidence, and `instrPos1 != instrPos2`, while retaining both distinct indexed global reads and complete receipts. | Singleton two select-close instructions at program positions 0 and 1 -> same component local event -> two composed global positions -> existing manifest packet fields. | `firstPos != secondPos` with existentially hidden instruction positions fails. Unrelated instruction positions not tied to the two receipts fail. | `ReviewerReadOccurrenceReceiptAtInstruction` makes the instruction position an explicit parameter while retaining the full receipt. The public fringe/select `..._repeated_equal_read_distinct_instruction_receipts` theorems expose both global positions, `instrPos1`, `instrPos2`, both disequalities, and both strong receipts. The proofs instantiate the actual select instructions at program positions `0` and `1`. The existing fields of `ConcreteBPNativeSuccinctRMQReviewerManifestSemanticAdequacy` now consume these stronger propositions and its constructor is regenerated. | Closed |
| `R1-E` | Correct all false target statements listed by A07; add explicit payload-bit scope text: "the theorem proves exact equality of flattened payload BIT CONTENTS with the public payload; empty sentinel cells and per-cell padding are not payload bits and are not charged by it" and do not claim an allocated-cell bound; note that topology lint checks identifier topology and not prose numeric values. | `RMQPaper.lean`, `README.md`, `docs/FAMILY_SUMMARY.md`, `RMQ/Headlines/RMQ.lean`, and `docs/PAPER_MODEL_ADEQUACY.md` state 207; select/rank/fringe/interior = 35/11/37/30; 22 sources and logical segments 0..22 with shared BP role; fresh rejected segment 23 and live segment 21; exact flattened-bit scope; lint limitation. | Public paper/root/docs -> claim drift and topology checks -> reviewer-facing model. | No allocated-cell claim; no stale 76/13/4/4, 20-source, through-20, or fresh-21 current-route prose survives in assigned surfaces. | The assigned public surfaces now state the live `207` route and `2*35 + (2*11 + 2*37 + 30) + 11` algebra; 22 physical sources over logical segments `0..22` with segments `0`/`19` sharing BP; live counted segment `21`; rejected fresh segment `23`. README and model adequacy scope the space result to exact flattened payload-bit contents, expressly excluding sentinel cells and per-cell padding and making no allocated-cell claim. Both document that topology lint checks identifier topology, not prose numerals. Development claim drift exited 0 with 743 hits and zero strict failures; `RMQPaper`/`RMQExamples` built successfully. | Closed |
| `REQ-B6-07` | "library green at EVERY commit"; "no dead sources"; parallel-then-swap. Complete the omitted post-freeze implementation commits `194c4e6`, `285c43e`, and `b77f385`. | Matrix evidence lists all governed implementation commits and distinguishes the historical per-commit command ledger as attested process evidence; this repair branch records `lake build RMQ` at every new commit. | Git history/worklogs -> B6 process row. | Missing governed commits or presenting process attestation as kernel evidence fails. | The B6 matrix lists all seven governed implementation commits, including `194c4e6`, `285c43e`, and `b77f385`, and labels the historical Git/build ledger as attested process evidence. This repair branch's material checkpoints are `5884489`, `f315f9c`, `9a341fa`, `85e9e45`, `faf2ebf`, and `d826e84`; `lake build RMQ` was green before every commit, with the exact development results recorded below. No dead replacement module or alternate public identity was introduced. | Closed |
| `REQ-B6-05` | Mark coordinator-confirmed: "the coordinator verified that the route literal genuinely did not move and that the authorization to move it went unused." | Matrix evidence records the supplied coordinator confirmation while retaining the checked `rfl` derivation and branch cap. | component algebra -> route literal 207 -> public consumers. | Confirmation alone cannot replace the checked derived equality; an asserted numeral fails. | B6 matrix now records both the checked `rfl` derivation from the MAX branch algebra and the supplied coordinator confirmation that the new `rankCost + 37` same-block branch is genuinely absorbed, the route literal remained `207`, and authorization to move it was unused. | Closed |
| `R1-F` | "In both matrices, relabel rows whose evidence is an attested command outcome rather than a checked proposition so they are visually distinct from kernel-checked rows (for example a status of `Closed (attested)` with the evidence tier named)." Apply this to every row enumerated by A07 and repair REQ-B6-05/07/08 honestly. | Enumerated process/verification rows use a distinct `Closed (attested: <tier>)` status or equivalent explicit evidence-tier label; semantic kernel rows remain visually distinct; B6-08 points to durable inventories after R1-A. | Acceptance matrices -> coordinator reconstruction. | Executable, artifact, Git-history, and process evidence must not be labeled as kernel propositions. | Both matrices define an explicit evidence-tier convention and label every A07-enumerated process, command, artifact, or executable row `Closed (attested: <tier>)`, while kernel propositions retain bare `Closed`. B6-07 lists all seven governed commits, including `194c4e6`, `285c43e`, and `b77f385`; B6-08 cites the durable broad and WordRAM inventories; B6-05 carries the coordinator-confirmed disposition. No frozen requirement, scope, consumer, or anti-vacuity cell was narrowed or removed. | Closed |
| `COMPLETE-COMMITTED-HYGIENE` | "CANDIDATE_COMPLETE requires all R1-A through R1-F rows closed on one committed unchanged final tree"; R1-G is added at the same priority as R1-A; no forbidden constructs; `lake build RMQ` green at every commit; final gate required once on the unchanged final tree. | One committed HEAD, clean tree, exact-base range diff clean, hygiene scans clean, all required commands exit 0 with durations, and final aggregate gate passes while holding `Global\RMQHeavyVerification`. | Every row above -> exact candidate commit -> coordinator audit. | Dirty or post-verification source changes, skipped validator/gate, or a green narrow build with an open semantic row fails. | The response-only final attestation for prior candidate `6155d48` recorded a clean tree and one passing aggregate gate, but the subsequent fresh-blind audit found the R1-C proposition/consumer, tier labels, current prose, and durable-ledger gaps now addressed by R1-R1. This row is therefore reopened until the R1-R1 final response attests the new exact committed candidate; the old results below remain scheduling/cache evidence only. | Reopened by R1-R1 exact-commit audit |
| `INV-STORE-IDENTITY` | "the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient". | R1-B uses the canonical accepted global store and changes exactly one segment-21 word/cell; same source/table object remains counted by the public payload chain. | reviewer payload -> global logical store segment 21 -> whole-query execution. | A separately built component table with no equality to the canonical store fails. | The final answer theorem executes the accepted canonical global store for `Cartesian.shape [7]` and changes only its live segment-21 fringe-table cell `(21,3)`; the existing reviewer source/region/erasure chain identifies that same segment-21 table with the counted public payload component. No sibling store or table is introduced. | Closed |
| `INV-SEMANTIC-NONVACUITY` | Semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction. | R1-C uses existing `HasClosedValidOccurrence`/receipt relations on the actual whole-query run, with full guard and occurrence data. | Valid ordinary query -> actual emitted global occurrence -> actual component local occurrence. | A `True` predicate, source enumeration, or compatible component membership fails. | The same-block witness constructs `ProducesEventAt` for the actual third whole-query instruction on `ValidRange [7] 0 1`, then derives both ordinary and instruction-indexed receipts through the existing operational provenance relation. The answer witness derives exact consumption from the evaluator's ordered footprint. No defined-true, enumeration-only, or component-membership substitute is used. | Closed |
| `INV-TRACE-EXECUTION` | "traces and footprints are derived from the execution they describe". | All new occurrence facts are obtained from `ProducesEventAt`/`global_getElem`, never a hand-written trace. | accepted program fold -> instruction trace -> composed global trace. | Synthetic or separately constructed trace fails. | All R1-C/D global `getElem?` facts are obtained from actual program-prefix composition and `ProducesEventAt.global_getElem`; R1-B's consumed address is extracted from the accepted supplied-store execution's own ordered footprint and converted to indexed `getElem?`. No trace is hand-written or replayed. | Closed |
| `INV-STORE-AGREEMENT` | "supplied-store agreement determines result, cost, and the relevant trace". | R1-B corruption store agrees with canonical store everywhere except the named consumed address; evaluator difference is derived by reduction/refinement of the actual supplied-store evaluator. | canonical store / one-cell variant -> same evaluator. | Replacing an unconsumed address or changing multiple regions without an agreement theorem fails. | `concreteBPNativeSuccinctRMQSingletonAnswerDependencyStore_agree_elsewhere` proves pointwise equality with the canonical global store at every address except `(21,3)`. Ordered-footprint store parametricity is used contrapositively: absence of that address would force identical full executions, contradicting the exact `some 0`/`none` answers. | Closed |
| `INV-READ-BACKING` | "every successful read is backed positionally by the counted store". | R1-B/C exhibit the successful segment-21 occurrence and reuse the existing receipt/source/counting chain. | indexed event -> source -> region -> counted payload. | `List.Mem` without position or source/counting receipt fails. | R1-B supplies the indexed successful canonical segment-21 read and `_matchesReadStore` pins its LE1 word; R1-C's complete receipt additionally carries source, region, producer path, and `source.Counted` for an actual same-block segment-21 occurrence. Both reuse the accepted counted fringe-table source. | Closed |
| `INV-PROOF-SEPARATION` | "proof-only fields never carry answers or uncharged routing information". | New answer inequality is about evaluator `.value` under supplied-store mutation; no proof packet computes the answer. | store reads -> chunk decode/fold -> close -> whole-query answer. | An answer injected after reads or obtained first from reference semantics fails. | The answer is computed by the actual supplied-store evaluator. The corrupt dense-select proof follows decoded table reads through the rank folds to the missing-second-word branch; proof receipts only certify provenance and never carry or inject the answer. | Closed |
| `INV-NO-SYNTHETIC` | "synthetic events, decorative rereads, and post-hoc replay do not support the execution claim". | The changed segment-21 entry is an actual consumed read whose decoded result changes the whole-query answer. | accepted read event -> returned answer. | A trace-only disagreement or unread-cell mutation fails. | The decisive `(21,3)` read is proved present in the accepted execution and its LE1→LE4 result changes the whole answer. Existing route no-synthetic theorems remain consumed by the capstone; neither decorative rereads nor post-hoc replay supports the new conclusion. | Closed |
| `INV-CATEGORY-SEPARATION` | Payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct. | Kernel theorems close semantic rows; executable validator is labeled executable evidence; matrix/history commands are attested; payload scope explicitly excludes cell padding/sentinels. | theorem and artifact evidence tiers remain explicit. | Presenting `#guard` or process logs as theorem evidence fails. | Kernel theorems close the semantic rows; the singleton validator remains explicitly executable/attested evidence; process and command rows are labeled attested in both matrices; public space prose is restricted to flattened payload-bit contents and expressly excludes sentinel/padding allocation claims. | Closed |
| `INV-PUBLIC-COMPOSITION` | A theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. | No accepted object changes; additive R1 theorems and corrected prose point to the existing canonical payload/execution and `ValidRange` domain. | public builder/payload -> canonical store -> accepted execution -> answer/cost/provenance. | Sibling payload/store or guarded/unguarded mismatch fails. | All repairs are additive theorems or evidence strengthening over the existing canonical payload, global store, accepted whole-query evaluator, and `ValidRange` domain. The accepted route, public identities, cost algebra, and payload are unchanged; the RMQ root imports the new proof module so downstream builds consume the same construction. | Closed |
| `DEFER-COORDINATOR-AUDIT` | "Explicitly deferred work: coordinator exact-commit audit and integration after this worker reports CANDIDATE_COMPLETE." | Report exact candidate commit and frozen matrix; make no acceptance, integration, merge, or push claim. | Candidate -> coordinator-owned audit/integration. | Worker self-acceptance fails. | Explicitly deferred and non-blocking. | Deferred |

The replay acceptance IDs `REPLAY-EXACT-REGISTRY`,
`REPLAY-SELECTOR-NONVACUITY`, and `REPLAY-SUBPROCESS-DEADLINE` are
`NOT_APPLICABLE`: this repair does not use a mutation replay harness and will
not claim count-only or vacuous replay evidence.

## Verification coverage plan and command ledger

All commands operate on this worktree only. Commands expected to exceed five
minutes acquire `Global\RMQHeavyVerification` and release it in `finally`.
Only one heavy Lean/Lake process runs at a time.

| Command | Role | Paths / rows covered | Distinct failure mode | Expected runtime and timeout | Prior `6155d48` response attestation / R1-R1 classification |
| --- | --- | --- | --- | --- | --- |
| `lake build RMQ` | Development loop and required at every commit | All Lean changes; all semantic rows | Elaboration/import regression | A07 comparable 462 s cold; mutex; timeout >= 20 min | Response-only at exact `6155d48`: exit 0, 0.513 s. Scheduling/cache evidence only after R1-R1 changes. |
| focused touched-module build(s) | Development loop | R1-B/C/D | Local theorem/type error before broad build | Expected < 10 min; mutex if projected > 5 min | Pre-6155 development evidence only: R1-B 0.700 s, R1-C 33.155 s, R1-D consumer 14.141 s. Invalidated for changed R1-C; R1-R1 replacements are recorded below. |
| `lake build RMQPaper RMQExamples` | Final required | R1-E/public consumers | Narrow paper/example import or statement drift | A07 comparable 109 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 0.570 s. Scheduling/cache evidence only. |
| `lake env lean scripts/wordram_axiom_check.lean` | R1-A development + final required | R1-A, B6 inventories | Unknown declaration or new trust dependency | A07 reached failure in 106 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 99.812 s, 796 lines, no error/forbidden axiom. Must rerun after the theorem-type repair. |
| `lake env lean scripts/axiom_check.lean` | R1-A development + final required | R1-A, broad trust inventory | Unknown declaration or unexpected axiom | Expected several minutes; mutex if needed; timeout 15 min | Response-only at exact `6155d48`: exit 0, 180.465 s, 2,478 lines, no error/forbidden axiom. Must rerun after the theorem-type repair. |
| `lake env lean scripts/headline_axiom_check.lean` | Final required | Public headline trust surface | Public theorem trust drift | A07 comparable 46 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 40.525 s. Scheduling/cache evidence; not separately required by R1-R1. |
| `lake exe rmq_succinct_classic_validate` | R1-G development + final required | R1-G and neighbouring fixtures | Stale concrete trace indices or differential validation failure | Base scout comparable 128 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 6.732 s. Invalidated for R1-R1 final certification; post-change replacement recorded below. |
| `lake exe rmq_succinct_classic_cost_harness` | Final required | 207 and charged-route behavior | Derived-literal or route-cost executable regression | A07 comparable 74 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 43.042 s. R1-R1 changes only proof/manifest/docs and cannot affect execution or cost, so no independent rerun is conditionally required; the aggregate gate remains required. |
| `scripts/claim_drift_scan.ps1` | Final required | R1-E/F | Claim vocabulary/numeric drift in configured surfaces | A07 comparable 24 s; timeout 5 min | Response-only at exact `6155d48`: exit 0, 5.012 s, 743 hits/0 strict failures. Invalidated by R1-R1 prose changes. |
| `scripts/paper_topology_lint.ps1` | Final required | R1-E | Identifier topology and documentary resolution (explicitly not prose-number validation) | A07 comparable 91 s; timeout 10 min | Response-only at exact `6155d48`: exit 0, 95.479 s, 83/49 identifiers. Invalidated by R1-R1 current-prose changes. |
| `scripts/design_decision_check.ps1 -Strict -Base 1a825f3...` | Final required | DD/worklog discipline | Missing nontrivial design rationale | Expected < 1 min; timeout 5 min | Response-only at exact `6155d48`: exit 0, 1.073 s. Invalidated by R1-R1 design/gate-comment changes. |
| hygiene `rg` scans | Development + final required | COMPLETE-COMMITTED-HYGIENE | Forbidden trust/runtime constructs | Expected < 1 min | Response-only at exact `6155d48`: both exit 0, 0.083/0.082 s, zero hits. Invalidated by R1-R1 Lean changes. |
| `git diff --check` and `git diff --check 1a825f3...HEAD` | Development + final required post-commit | COMPLETE-COMMITTED-HYGIENE | Working-tree or committed whitespace defects | Expected < 1 min | Response-only at exact `6155d48`: both exit 0, 0.125/0.130 s. R1-R1 requires new worktree and `6155d48..HEAD` range checks. |
| `scripts/gate.ps1` | Final aggregate, required once on unchanged final tree | Entire repair campaign | Cross-surface integration and fatal inventory omission | A07 stopped at 135 s; prompt allows >45 min; mutex; timeout 75 min | Response-only at exact `6155d48`: exit 0, 1,825.409 s, mutex acquired/released. Scheduling evidence only; one new final gate is mandatory after R1-R1 freezes. |

### R1-R1 continuation command ledger and current stop point

The frozen-contract commit is `012862e`; the material theorem/public repair is
`233b6ca`; and the authorized comment-only workflow decision is `f6ce2d2`.
Results below were run on the dirty diff that was committed unchanged as
`233b6ca`, unless a row says otherwise. They certify that semantic commit, not a
later worklog commit. Final post-commit results necessarily live in the worker
response; they must name the exact later candidate SHA and are not represented
here as already-committed evidence.

| Command | Evidence role | Certified tree/diff | Exit | Seconds | Result / transitive classification |
| --- | --- | --- | ---: | ---: | --- |
| `lake build RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall` | Development, exact strengthened theorem | R1-R1 Lean diff later committed as `233b6ca` | 0 | 41.034 | Shared pre-state/local-position/producer/invocation/component proposition elaborated. |
| `lake build RMQ.Core.SuccinctFinalSemanticProvenanceAdequacy` | Development, direct mandatory consumer | Same `233b6ca` Lean diff | 0 | 5.516 | Existing manifest field and constructor consume the exact strengthened proposition. |
| `lake exe rmq_succinct_classic_validate` | Required post-transitive-change executable | Same `233b6ca` Lean diff; validator source unchanged | 0 | 7.011 | 498 windows passed; fixture remains global `0`/`15`, instructions `0`/`1`. Final exact-HEAD response attestation still required. |
| `lake build RMQPaper RMQExamples` | Development direct public consumers | Same `233b6ca` Lean/public diff | 0 | 25.102 | Headline paper-main theorem and examples consume the amended manifest type. |
| `powershell ... scripts/claim_drift_scan.ps1` | Development current-prose scan | Same `233b6ca` public diff | 0 | 14.954 | 745 hits, zero strict failures. |
| `powershell ... scripts/paper_topology_lint.ps1` | Development documentary topology | Same `233b6ca` public diff | 0 | 108.114 | PASS, 83 broad and 49 paper identifiers. |
| `powershell ... scripts/design_decision_check.ps1 -Strict -Base 1a825f3...` | Required design/workflow discipline | Same material diff before `233b6ca` | 1 | 2.265 | Exact blocker: required `scripts/gate.ps1` comment edit is classified workflow-sensitive; strict mode requires `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, which is outside the R1-R1 write scope. No semantic or documentation assertion failed. |
| `powershell ... scripts/design_decision_check.ps1 -Strict -Base 6155d48...` | Authorized workflow-repair check | Exact committed `f6ce2d2` | 0 | 3.1 | Checked 10 changed files after `WDD-20260718-004` recorded that the gate edit is comment-only and changes no command, ordering, semantics, or behavior. |
| Forbidden-construct scan | Development hygiene | Same material diff | 0 | not separately timed | Zero hits under `RMQ`/`lakefile.toml`. |
| `native_decide` / `Lean.ofReduceBool` scan | Development trust hygiene | Same material diff | 0 | not separately timed | Zero hits under `RMQ`. |
| `git diff --check` | Development whitespace | Same material diff | 0 | 0.7 wall | Clean. |
| `lake build RMQ` | Required before material commit | Same material diff | 0 | 6.907 | Root green before `233b6ca`; only inherited warnings. |
| `lake exe rmq_succinct_classic_cost_harness` | Conditional | Not rerun independently | n/a | n/a | Correctly skipped: changed definitions are proof theorem/manifest fields plus prose/comment only; no evaluator, cost, route, validator, payload, or store definition changed. The mandatory final aggregate gate would still exercise its integrated coverage. |

The former write-scope blocker is resolved by the user's narrow authorization
and committed `WDD-20260718-004`; the required strict check against `6155d48`
passes. The final axiom inventories, clean-HEAD validator,
claim/topology/design checks, committed-range checks, and the one mutex-held
aggregate gate remain deliberately unrun until the commit containing this
ledger freezes the exact candidate. They must not be inferred from the prior
`6155d48` results.

### Exact-candidate result boundary

The candidate is the clean commit containing this section. Its exact SHA cannot
be embedded in its own contents; the worker response supplies that SHA after
the commit is created. No source, proof, documentation, matrix, script, or
ledger edit is permitted after the final battery starts. Every final command is
therefore an exact-HEAD, response-only attestation, with command, exit code,
duration, tree identity, and clean-state checks reported outside this committed
file. This is an evidence-tier boundary, not a claim that an unrun command has
already passed.

Any source/theorem/executable edit invalidates transitive Lean checks. A
docs/matrix-only edit invalidates claim/design/topology/diff checks but not an
already checked unchanged Lean object. The final aggregate gate is run at most
once on an unchanged candidate tree unless it does not complete; a late failure
is repaired through its smallest component before one final certification run.

## Parallelization check

The join theorem is the accepted whole-query route plus its reviewer-facing
evidence. Three independent read-only inventories were delegated: R1-B value
dependency; R1-C/D/G provenance and validator positions; R1-A/E/F trust and
document/matrix drift. During implementation, disjoint workers owned the new
R1-B module and the eight R1-E/F document/matrix files; R1 owned the receipt
theorems, worklog, integration, verification, and commits.

## Milestone ledger

Every checkpoint records tree identity, exact command, exit code, duration,
process disposition, and the reason for any rerun.

| Milestone | Tree / diff | Command | Exit | Seconds | Process and rerun disposition |
| --- | --- | --- | ---: | ---: | --- |
| Frozen matrix baseline | HEAD `1a825f3a940f0ff59084b69b25ba0c318569f33f`; only untracked `R1_WORKLOG.md` | mutex-held `lake build RMQ` | 1 | 0.197 | Sandboxed launcher could not reach GitHub; process ended. This was an environment failure before Lean/build work. |
| Frozen matrix baseline | Same Lean tree; only untracked `R1_WORKLOG.md` | approved-access, mutex-held `lake build RMQ` | 0 | 695.834 | Material rerun condition: approved toolchain/cache network access. Single owned process; 238 jobs; build completed successfully. |
| Frozen matrix amendment recheck | Same Lean tree; worklog records the coordinator's second R1-A defect | sandboxed `lake build RMQ` | 1 | 0.066 | Launcher network failure; process ended before build work. |
| Frozen matrix amendment recheck | Same Lean tree; amended untracked worklog only | approved-access `lake build RMQ` | 0 | 0.332 | Material rerun condition: approved toolchain access. Cached build completed successfully; the worklog is not an RMQ build input. |
| R1-A first WordRAM run | R1-A script diff before namespace correction | `lake env lean scripts/wordram_axiom_check.lean` | 1 | 82.067 | Script loaded and printed inventory, then exposed five incorrectly qualified new declarations. |
| R1-A WordRAM diagnostic | Same diff | error-filtered WordRAM inventory | 1 | 74.681 | Identified the five declarations under `ConcreteCompactBPCloseLCADirectory`; process ended. |
| R1-A WordRAM repaired | Corrected exact declaration namespaces | `lake env lean scripts/wordram_axiom_check.lean` | 0 | 78.430 | Full inventory loaded and completed; only allowed standard axioms reported. |
| R1-A broad first load | Before closure repair | mutex-held `lake env lean scripts/axiom_check.lean` | 1 | 0.405 | Immediate missing `RMQUnionFind` module proved the fresh-build closure defect. |
| R1-A closure build 1 | Added `RMQUnionFind` root | mutex-held `lake build RMQ` | 0 | 30.466 | Built 250 jobs including the standalone UnionFind root. |
| R1-A broad declaration diagnostic | UnionFind closure present | full then error-filtered `axiom_check.lean` | 1 | 138.194 / 134.986 | Full load reached two BP-compat-only declarations; filtered run named them. This justified preserving the BP-compat barrel in the RMQ closure. |
| R1-A closure build 2 | Added `RMQ.Core.GenericSelectBPCompat` root | `lake build RMQ` | 0 | 4.881 | Built 253 jobs including both closure roots. |
| R1-A broad repaired | Final R1-A tree `f315f9c` | `lake env lean scripts/axiom_check.lean` | 0 | 151.142 | Full 2,465-line inventory completed; only allowed standard axioms. |
| R1-G first validation | Correct numeric/provenance literals; stale success-message prose remained | `lake exe rmq_succinct_classic_validate` | 0 | 121.152 | All 498 windows passed; output exposed the neighbouring stale 76 success message. |
| R1-G repaired validation | Correct literals and live 207 success message | `lake exe rmq_succinct_classic_validate` | 0 | 98.683 | All 498 windows and structural checks passed. |
| R1-G per-commit build | Same Lean tree; validator file is outside RMQ root | `lake build RMQ` | 0 | 0.347 | Required cached per-commit RMQ build green. |
| R1-G instruction-link build attempt | Strengthened fixture evaluates instruction positions `0` and `1` and relates their local event `0` to global positions `0` and `15` | sandboxed `lake build RMQ.Validation.SuccinctClassic` | 1 | 0.216 | Environment-only toolchain download failure before compilation; no Lean process survived. |
| R1-G instruction-link build | Same strengthened fixture | approved-access `lake build RMQ.Validation.SuccinctClassic` | 0 | 248.063 | Material rerun condition: approved pinned-toolchain access. The compiled guards passed; one build process, no duplicate retry. |
| R1-C/D receipt build | Added instruction-indexed receipts, same-block singleton occurrence, and stronger repeated-read witnesses | `lake build RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall` | 0 | 33.155 | Actual program-prefix composition elaborated; no whole-trace kernel evaluation. |
| R1-D consumed-packet build | Strengthened the existing manifest packet fields and regenerated its constructor | `lake build RMQ.Core.SuccinctFinalSemanticProvenanceAdequacy` | 0 | 14.141 | Paper-consumed packet closes the distinct-instruction clause; no sibling packet. |
| R1-C/D per-commit build | Final R1-C/D Lean checkpoint | `lake build RMQ` | 0 | 16.308 | Required 253-job library build green before commit. |
| R1-B stale diagnostic cleanup | Obsolete elaboration of an earlier debug/search version of `AnswerValueDependency.lean` | exact PID audit, then terminate only `1088 -> 22472 -> 20796` | 0 | n/a | The process chain had run since 20:03 and was no longer testing the current file. A concurrent `b7-charged-level` build was identified by command line and left untouched. |
| R1-B focused final | Final answer-level theorem, one-cell agreement, exact values, and indexed consumption | `lake build RMQ.Core.SuccinctFinal.RAM.AnswerValueDependency` | 0 | 0.700 | Clean focused rerun after stale-chain removal; no warning introduced by the new module. |
| R1-B root hook | Same proof imported by `RMQ.lean` | `lake build RMQ` | 0 | 3.700 | Required per-commit root build green; only inherited replay warnings. |
| R1-B trust probe | Final whole-query `.value ≠` theorem | `#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQSingletonAnswerDependency_value_ne` | 0 | not separately timed | Exact set: `propext`, `Classical.choice`, `Quot.sound`; no `sorryAx` or `Lean.ofReduceBool`. The theorem is also entered durably in both required inventory scripts for their final load checks. |
| R1 final-surface WordRAM inventory diagnostic | Added R1-B/C/D entries but focused script lacked the new module import | `lake env lean scripts/wordram_axiom_check.lean` | 1 | 115.173 | Material finding: exactly two unknown AnswerValueDependency constants; 792 lines, zero `sorryAx`, zero `Lean.ofReduceBool`. Added an explicit module import to make the focused inventory self-contained. |
| R1 final-surface WordRAM inventory | Import-corrected focused inventory | `lake env lean scripts/wordram_axiom_check.lean` | 0 | 105.951 | 796 lines; zero errors/`sorryAx`/`Lean.ofReduceBool`; unique sets only `[]`, `[propext]`, `[propext, Quot.sound]`, `[propext, Classical.choice, Quot.sound]`. |
| R1 final-surface broad inventory | Same completed theorem surface | `lake env lean scripts/axiom_check.lean` | 0 | 203.662 | 2,478 lines; zero errors/`sorryAx`/`Lean.ofReduceBool`; the same four allowed unique axiom sets. |
| R1 all-surface library build | Completed R1-A through R1-G source, script, and documentation tree before material commit | `lake build RMQ` | 0 | 0.866 | Cached 254-job root build; only inherited warnings. |
| R1 public consumers | Same completed public/documentation tree | `lake build RMQPaper RMQExamples` | 0 | 0.671 | Both public consumers built successfully from cache; the earlier uncached build of the same public changes also exited 0 in 77.781 s. |
| R1 claim drift development check | Same completed documentation/matrix tree | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1` | 0 | 5.285 | Reviewed 743 configured hits with zero strict failures. |
| R1 topology development attempt | Same tree | sandboxed `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | 1 | 139.087 | Environment-only Lake download failure while the lint elaborated its generated checker; seven output lines, no topology finding. |
| R1 topology development check | Same tree | approved-access `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | 0 | 126.034 | Material rerun condition: pinned-toolchain/cache access. PASS with 83 broad documentary identifiers and 49 paper identifiers resolved. |
| R1 strict design check | Same completed branch diff against exact base | `powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 1a825f3a940f0ff59084b69b25ba0c318569f33f` | 0 | 1.136 | Checked all 16 changed files in the exact-base range. |
| R1 hygiene development check | Same completed source tree | both required `rg` scans | 0 | 1.7 | Zero forbidden construct/import hits and zero `native_decide`/`Lean.ofReduceBool` hits under `RMQ`. |

## R1-R2: live A07 public-claim synchronization

Worker: R1-R2
Requested title: `(R1-R2) Synchronize every live A07 public claim`
Exact base: `06a8e3c67700672696da776b92fe8315a38363a2` (first parent
`3a2b47261ba6a15829a3160a7fce352b62c88380`; governance parent
`255e400134a4e151e3183cd7a24c99ec7cd3e9af`).

### Frozen source facts and pre-edit inventory

The live facts are reconstructed from source rather than the prior audit:

- `ReviewerPhysical.lean` defines exactly 22 `ReviewerSource` constructors and
  maps logical segments `0..22`; segments `0` and `19` both map to
  `.sharedBPCode`, segment `21` maps to `.fringeChunkTable`, and only
  `23` and above are absent.
- `SuccinctFinalRAM.lean` defines the accepted algebra with select `35`, rank
  `11`, endpoint fringe `37`, and interior `30`, and proves the named
  whole-query cost equals `207`.
- `Validation/SuccinctClassic.lean` checks the singleton equal read at global
  positions `0` and `15`, from program instructions `0` and `1`.

Before editing, strict claim scan exited 1 in 5.8 s with 31 unapproved live
matches: retired `76`/`142` cost language in `README.md`, `artifact/README.md`,
`docs/WORD_RAM_REVIEW_PACKET.md`, `docs/PUBLICATION_STRATEGY.md`,
`docs/PAPER_THEOREM_MAP.md`, `docs/digests/PROJECT_DIGESTION_CURRENT.md`,
`docs/TRUST_AUDIT_PACKET.md`, `docs/PAPER_RELATED_WORK.md`,
`docs/PAPER_MAIN_THEOREM.md`, `docs/RELATED_WORK_AND_LIMITATIONS.md`, and
`docs/internal/RMQ_FINAL_ROADMAP.md`; retired 20-source language in
`artifact/CLAIMS.md`, `artifact/README.md`, `docs/WHAT_IS_PROVED.md`,
`docs/PAPER_MAIN_THEOREM.md`, and `docs/PAPER_THEOREM_MAP.md`; retired fresh
segment-21 language in `artifact/CLAIMS.md`, `artifact/README.md`, and
`docs/PAPER_THEOREM_MAP.md`; and retired global positions `0`/`12` in
`artifact/CLAIMS.md`. `README.md` also contained a scanner-sensitive single
line that mentioned fresh `23` and live `21` together. The full live-current
inventory additionally checked `docs/ROADMAP.md`; no dated digest, audit,
matrix, earlier decision body, or prior worklog is to be rewritten.

### Frozen R1-R2 requirement-to-evidence matrix

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-R1R2-CURRENT-SURFACE-SYNC` | "Synchronize every live current public/documentation surface to the exact already-checked R1-R1 facts and make strict drift enforcement pass without altering historical records." | Local public surface | Every declared current surface is reread against the source facts; strict scan has zero live failures. | Source definitions -> current prose -> strict scanner/topology lint -> coordinator audit. | Search stale cost/source/fresh/position literals across every declared public surface; pre-edit scan found 31 failures. | All 14 current prose surfaces plus README/artifact surfaces reread; development strict scan exits 0 with 805 hits and zero strict failures. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-CURRENT-COST-207` | "every live surface must use current modeled bound `207` and, where algebra is shown, exactly `2*35 + (2*11 + 2*37 + 30) + 11 = 207`. Do not confuse this modeled charged-trace/cost certificate with Lean runtime or measured performance." | Local public surface | `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 207`; source algebra has select 35, rank 11, fringe 37, interior 30. | Accepted algebra -> list/public paper prose -> claim scan. | Replace neither `76` nor `142` blindly: retain no retired numeral in a current surface and preserve the model/runtime distinction sentence. | Current surfaces use 207 and exact algebra where shown; modeled charged-trace language remains explicitly separate from Lean runtime and measured performance. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-CURRENT-SOURCES-22` | "every live surface must state 22 physical reviewer sources over logical segments `0..22`, with logical segments `0` and `19` sharing the BP source. Do not describe this as 23 physical sources." | Local public surface | `ReviewerSource` has 22 constructors; `concreteBPNativeSuccinctRMQReviewerSegmentSource?` maps 0/19 to `.sharedBPCode` and 21/22 to table sources. | Physical source/list and segment map -> public manifest prose -> claim scan. | Search 20-source, 20-constructor, and segment-range prose; five live 20-source failures found. | Live manifest prose now names 22 physical sources, logical `0..22`, and the shared 0/19 BP source. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-FRESH-SEGMENT-23` | "segment `21` is live; rejected fresh segment `23` is outside the manifest. Do not globally replace every historical occurrence of 21." | Local public surface | Segment map has `21 => some .fringeChunkTable` and `_ + 23 => none`; fresh mutation is segment 23. | Source map/mutation -> current provenance prose -> claim scan. | Search fresh/rejected segment 21; three stale live failures plus one scanner-sensitive mixed README line found. | Live prose distinguishes live fringe-table segment 21 from rejected fresh segment 23; history is unchanged. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-TRACE-POSITIONS-0-15` | "the current singleton repeated-read fixture uses global positions `0` and `15`, produced by instruction positions `0` and `1`. Preserve the distinction between global trace position and program-instruction position." | Local public surface | `singletonRepeatedEqualReadPositionsOK` checks trace 0/15; `singletonRepeatedEqualReadInstructionPositionsOK` checks program 0/1. | Validator fixture -> artifact/current provenance prose -> claim scan. | Search 0/12 wording and require both coordinate systems in replacement prose; one stale live failure found. | Current artifact prose states global 0/15 and producing instructions 0/1 as distinct coordinate systems. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-CLAIM-POLICY-ENFORCEMENT` | "final `scripts/claim_drift_scan.ps1 -Strict` must reject no live current surface. The governed `r1r1-3a2b472-*` regressions and current-value controls are inherited from the exact base and must remain unchanged." | Verification | Production strict scanner exits 0; no policy/regression file changes. | Current prose -> production scanner -> inherited regression controls. | Pre-edit production strict scan exited 1 with 31 failures; policy files are out of scope. | Development production scan exits 0 with 805 classified hits and zero strict failures; no policy/regression path changed. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REQ-R1R2-HISTORICAL-PRESERVATION` | "do not edit dated `docs/DIGESTION_LOG.md` entries, dated digests, audit reports, old matrices, prior worklogs, or earlier design-decision bodies merely because they record once-current facts." | Inherited | Final changed-path set contains only declared scope; diff shows only new decision entries, not earlier decision bodies. | Frozen history -> unchanged Git paths/lines -> coordinator audit. | Do not use history/policy allowances to hide current claims; exact path search classifies those survivors as historical. | Diff scope contains only authorized current documentation plus appended decision/worklog evidence; historical survivor search was classified rather than rewritten. | Closed; exact-HEAD range evidence is recorded in the worker response. |
| `REQ-R1R2-DIGESTION-EVIDENCE` | "make the R1 worklog non-Pending and include all four required parts: conceptual change, plain-English meaning, live assumptions, and the strongest skeptical next question." | Durable ledger | Committed R1-R2 matrix and digestion section contain all four parts; no R1-R2 row says Pending at candidate report time. | Worklog -> final response -> coordinator audit. | A clean scan without a source-backed ledger does not close this row. | Matrix and digestion below contain all four required parts and no R1-R2 row is Pending. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `COMPLETE-R1R2-COMMITTED-EVIDENCE` | "committed branch plus an updated `docs/internal/R1_WORKLOG.md` requirement-to-evidence ledger." | Durable ledger | One clean committed candidate records source facts, exact checks, range/path evidence, and response-only final attestation boundary. | Matrix -> commit -> exact final response -> coordinator audit. | A docs commit before rereading each current surface or before final range checks fails. | This ledger records source facts, pre-commit verification, and the response-only exact-HEAD attestation boundary. | Closed; final candidate SHA and exact-HEAD check results are response evidence, not retroactively claimed as committed. |
| `INV-R1R1-SEMANTIC-PRESERVATION` | "the exact Lean, validator, script, theorem, import, and executable tree inherited from first parent `3a2b472...` must remain byte-for-byte unchanged." | Inherited | Final name-only range contains documentation/decision/worklog paths only; no Lean, script, policy, template, skill, or gate path. | First-parent checked tree -> doc-only range -> final path audit. | Compare changed-path set to declared scope; any code/script identity is a stop condition. | Current diff has 17 declared Markdown/decision/worklog paths only; no Lean, script, policy, template, skill, or gate path. | Closed; exact-HEAD range evidence is recorded in the worker response. |
| `INV-CATEGORY-SEPARATION` | "keep payload bits, proof-only data, modeled ticks, trace events/positions, physical sources/cells, allocated storage, Lean runtime, and measured performance categorically distinct." | Inherited | Current prose labels 207 as modeled charged-trace/cost, identifies trace versus instruction positions, and makes no allocation/runtime claim. | Source/model facts -> public prose -> claim scan. | Reject wording that calls 207 Lean runtime, treats 22 logical segments as 23 physical sources, or conflates 0/15 with instructions. | Repaired prose retains the model/runtime, physical/logical source, and global/program-position distinctions. | Closed; exact-HEAD attestation is recorded in the worker response. |
| `REPLAY-EXACT-REGISTRY` | NOT_APPLICABLE because this task does not change a mutation runner. | Deferred non-blocking | No mutation-runner file is changed. | Scope audit. | Inventing replay evidence is forbidden. | Not applicable by frozen scope. | Not applicable |
| `REPLAY-SELECTOR-NONVACUITY` | NOT_APPLICABLE because this task does not change a mutation runner. | Deferred non-blocking | No selector/mutation runner is changed. | Scope audit. | Inventing replay evidence is forbidden. | Not applicable by frozen scope. | Not applicable |
| `REPLAY-SUBPROCESS-DEADLINE` | NOT_APPLICABLE because no new child-process harness is in scope. | Deferred non-blocking | No harness/process implementation is changed. | Scope audit. | Inventing replay evidence is forbidden. | Not applicable by frozen scope. | Not applicable |
| `CHK-R1R2-STRICT` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | Final required | Exit 0 and zero strict failures. | Live prose/policy boundary. | Scanner is a tripwire; source reread remains separately required. | Pre-edit exit 1, 31 failures; development rerun exits 0 in 13.1 s with 805 hits and zero strict failures. | Closed; final exact-HEAD rerun is response-only attestation. |
| `CHK-R1R2-TOPOLOGY` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\paper_topology_lint.ps1` | Final required | Exit 0 with current documentary identifier resolution. | Current public documents -> production topology verdict. | Claim scan cannot establish identifier resolution. | After missing fresh-worktree artifacts were built by focused public targets, exits 0 in 82.8 s with 83 broad and 49 paper identifiers resolved. | Closed; final exact-HEAD rerun is response-only attestation. |
| `CHK-R1R2-DESIGN` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base 06a8e3c67700672696da776b92fe8315a38363a2` | Final required | Exit 0 after DD/WDD entries. | Decision/workflow ledgers -> strict checker. | Omitting either required minimal entry fails. | Development check exits 0 in 1.2 s over 17 changed files. | Closed; final exact-HEAD rerun is response-only attestation. |
| `CHK-R1R2-DIFF-PATHS` | `git diff --check`; `git diff --check 06a8e3c67700672696da776b92fe8315a38363a2..HEAD`; changed-path scope audit; clean exact HEAD. | Final required | Both checks exit 0; all changed paths are declared docs/decision/worklog paths. | Committed doc-only candidate -> coordinator audit. | A clean worktree alone cannot certify committed whitespace or scope. | Development scope audit identifies 17 declared paths; final committed range check remains response-only attestation. | Closed; exact-HEAD rerun is response-only attestation. |

Verification plan: targeted stale-literal searches and source inspection are the
development loop; strict scan, topology lint, strict decision check, and both
diff checks are final-required. No source, theorem, checker, or executable is
in scope, so root builds, validators, axiom inventories, cost harness, and the
aggregate gate are deliberately not duplicated; first parent `3a2b472` already
has their exact-tree attestation, while this rung's new risk is live prose and
policy classification.

### R1-R2 proof digestion and final-attestation boundary

Conceptual change: synchronize only live current descriptions to the accepted
R1-R1 route facts; no Lean proposition, source, policy, template, script, or
executable changes.

Plain-English meaning: reviewers now see the same 207-cost/readWord-only route,
22-physical-source manifest, segment-23 rejection, and 0/15 fixture that the
existing checked objects and validator already establish.

Live assumptions: `ReviewerPhysical.lean` remains the source for physical
source/segment facts, `SuccinctFinalRAM.lean` for the modeled 207 certificate,
and `Validation/SuccinctClassic.lean` for the concrete fixture. The result is a
modeled charged-trace statement, not Lean runtime, measured performance,
allocated-cell accounting, or a changed roadmap acceptance decision.

Strongest skeptical next question: does every reader-facing document preserve
the distinction between the 22 physical sources and 23 logical segment roles,
between global trace positions and instruction positions, and between current
prose and frozen historical evidence? The production strict scan, topology
lint, source reread, and final range audit address that question; coordinator
exact-commit re-audit remains required.

The development checks above certify the uncommitted semantic document content.
The final response supplies the exact-HEAD command attestations after the
ledger commit; it must not be read as claiming that those later runs were
already recorded in this commit.

## R1-R3: close every live readWord-only A07 surface

Worker: R1-R3
Requested title: `(R1-R3) Close every live readWord-only A07 surface`
Exact base: `a835720ddae8816727febb16c636eee4a5f57076` (rejected R1-R2
candidate parent `48147cbc67c6c01c4abcf2565f9b981adb5eacb8`; workflow-governance
parent `be1239a353a8f067b50d7d1bd8c4c10413a33100`).
Branch: `codex/r1-a07-readword-surface-sync-r3`.

The exact-base and both-parent objects were fetched and verified before the
branch was created. The governed preflight passed with governance
`be1239a353a8f067b50d7d1bd8c4c10413a33100`, required skill
`rmq-proof-sprint`, and runtime project skills `rmq-audit-prompt`,
`rmq-coordinator`, and `rmq-proof-sprint`.

### R1-R2 exhaustive-closure correction

The R1-R2 statements that "all 14 current prose surfaces plus
README/artifact surfaces" were reread and that reviewers consequently saw the
readWord-only route were not an exhaustive current-surface result. They closed
the four then-targeted cost/source/freshness/fixture facts, but they did not
derive the inventory from `currentFactSurfacePathRegex` and left weaker
three-constructor or read-or-primitive wording on four registered current
surfaces. The R1-R2 four-fact evidence remains inherited; its exhaustive
current-surface and readWord-only impression is superseded by the R1-R3 matrix
and the exact 18-path registry below. This correction appends evidence rather
than rewriting the earlier R1-R2 record.

### Frozen source proposition and definition cases

The load-bearing source proposition is universal over the exact trace consumed
by cost and adequacy:

```lean
theorem
    concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    forall event,
      event ∈
          (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
            shape left right).trace ->
        event.isReadWord
```

The required public reader-facing identity is
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`, an
abbreviation of that exact theorem. The older
`...EventReadWordOrWordRankOrWordSelect` alias is only weaker compatibility
evidence and cannot serve as the current route signature.

The definition-level compatibility cases remain distinct from execution:

```lean
def WordRAM.TraceEvent.nonSyntheticWeight : TraceEvent -> Nat
  | readWord _ _ _ => 1
  | wordRank _ _ _ => 1
  | wordSelect _ _ _ => 1
  | syntheticCostOnlyPrimitive => 0
```

Thus the definition is not readWord-only; the accepted canonical trace object
is readWord-only.

### Closed policy-derived current-surface inventory (pre-edit freeze)

This list is derived by applying the exact
`docs/internal/CLAIM_DRIFT_POLICY.json` field
`currentFactSurfacePathRegex` to every tracked path at
`a835720ddae8816727febb16c636eee4a5f57076`. Each path was reread against the
source proposition and compatibility definition, not merely searched for a
scanner hit.

| Registered current path | Pre-edit source-directed disposition |
| --- | --- |
| `README.md` | **Repair authorized by coordinator amendment.** The headline execution-story row presented the accepted route as read-or-primitive; the current-signature row promoted the weaker three-constructor alias; and the overview repeated read-or-primitive wording. |
| `artifact/CLAIMS.md` | **Repair.** The execution-story claim used read-or-primitive wording and the charged-trace row used the weaker three-constructor alias as the current signature. |
| `artifact/README.md` | Preserve. It already says every accepted emitted event is a payload read and keeps cost/model scope separate. |
| `docs/FAMILY_SUMMARY.md` | **Repair.** The opening certificate paragraph says the canonical trace proves only one-of-three, and the execution-story paragraph presents the accepted final query as read-or-primitive. Preserve the exact four `nonSyntheticWeight` cases while separating the stronger execution fact. |
| `docs/PAPER_CLAIM_CORRESPONDENCE.md` | **Repair.** The current charged-trace row cites and states only the weaker three-constructor signature. |
| `docs/PAPER_MAIN_THEOREM.md` | Preserve. It already says every actual emitted event is `readWord` on the canonical trace. |
| `docs/PAPER_MODEL_ADEQUACY.md` | Preserve as the independently source-checked semantic reference. It names the exact source/headline identities, universal readWord-only fact, and compatibility-only `wordRank`/`wordSelect` constructors. |
| `docs/PAPER_RELATED_WORK.md` | Preserve. Its current cost/model boundary is accurate and it makes no weaker current event-vocabulary claim. |
| `docs/PAPER_THEOREM_MAP.md` | Preserve. It explicitly says every emitted canonical event is `readWord` and separates certificate weighting. |
| `docs/PUBLICATION_STRATEGY.md` | Preserve. It states current `207` trace/certificate accounting without presenting a weaker constructor vocabulary as current. |
| `docs/RELATED_WORK_AND_LIMITATIONS.md` | Preserve. It accurately scopes `207` and makes no misleading event-vocabulary claim. |
| `docs/ROADMAP.md` | Preserve. Its current paragraph classifies actual emitted events as `readWord`; later word-rank/select material is explicit historical/component chronology. |
| `docs/TRUST_AUDIT_PACKET.md` | Preserve. The capstone says only genuine `readWord` events. Its certificate sentence states true constructor cases without claiming those are exhaustive definition cases. |
| `docs/WHAT_IS_PROVED.md` | Preserve. It states the current readWord-only fact and labels the older three-constructor public identity compatibility-named. |
| `docs/WORD_RAM_REVIEW_PACKET.md` | Preserve. It says the canonical trace emits only `readWord` and lists that fact before certificate equalities. |
| `docs/digests/PROJECT_DIGESTION_CURRENT.md` | Preserve. It says every emitted event is a payload-word read. Its certificate description is a true non-exclusive subset of the definition cases. |
| `docs/internal/CLAIM_DRIFT_POLICY.md` | Preserve byte-for-byte. It explicitly states the route is readWord-only and `wordRank`/`wordSelect` are compatibility-only constructors never emitted by this route. |
| `docs/internal/RMQ_FINAL_ROADMAP.md` | Preserve. Its current U3 paragraph says each emitted event is `readWord`; historical status remains explicit. |

The repaired claim paths plus this worklog are within the amended scope.
`docs/internal/DESIGN_DECISIONS.md` remains conditional: it will change only if
the strict design checker requires a minimal substantive public-claim entry.
No policy, script, Lean, roadmap, matrix, historical, gate, skill, template, or
workflow-decision edit is authorized.

### Frozen R1-R3 requirement-to-evidence matrix

These requirements and IDs are frozen before the first R1-R3 claim edit. Only
evidence, status, and an explicitly approved contract amendment may change.

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-R1R3-READWORD-ONLY-SURFACE` | "repair these exact rejected-candidate statements and any semantically equivalent current statement found by the closed inventory"; `artifact/CLAIMS.md`: replace “Every actual emitted event is readWord, wordRank, or wordSelect” with the universal readWord-only route fact and cite `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`; `docs/PAPER_CLAIM_CORRESPONDENCE.md`: the current charged-trace row must cite the readWord-only headline/source theorem, not present the weaker three-constructor disjunction as the current route signature; `docs/FAMILY_SUMMARY.md`: preserve the definition-level fact that `nonSyntheticWeight` assigns one to `readWord`, `wordRank`, and `wordSelect`, but state separately and explicitly that the accepted canonical trace emits only `readWord`; `wordRank` and `wordSelect` remain compatibility constructors and are never emitted on this route. Coordinator amendment: "This authorization covers all current-route wording in README, not only the first line that triggered the stop. In particular, inspect and repair the headline execution-story/current-signature rows around the current base's lines 71 and 78 and the overview wording around lines 207-208 wherever they present the accepted canonical route as allowing bounded word primitives rather than stating the stronger checked readWord-only fact." | Local current public surface | For every `shape left right event`, membership in the exact `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right` trace implies `event.isReadWord`; every repaired surface names the public alias and does not substitute the weaker compatibility theorem. | Source theorem -> exact headline abbreviation -> README/artifact/paper/family current consumer -> topology/claim scanner -> coordinator exact-commit audit. | Reorder the three constructors, put the compatibility theorem before the strong theorem, or state only a singleton fixture. All must remain visibly weaker than the universal exact-object source proposition and must not survive as the current signature. | Pre-edit inventory found four repair paths and no additional out-of-scope path. | Open until edits and final checks |
| `REQ-R1R3-CLOSED-INVENTORY` | "enumerate all tracked paths matched by `currentFactSurfacePathRegex`, reread each one, and record a per-path disposition in the worklog. ‘No scanner hit’ is insufficient evidence that a path was semantically current." | Local current-surface registry | Exact base registry contains the 18 paths listed above; each has a source-directed repair/preserve disposition and final reread. | Policy JSON regex -> exact-base tracked paths -> per-path semantic reread -> durable worklog -> coordinator reconstruction. | Look for an unregistered current-looking tracked document and for a registered file with no regex hit but misleading sentence composition. The registered README weakness was found despite the prior green strict scan; all repository Markdown remains an adversarial search domain. | Exact 18-path pre-edit inventory frozen above. | Open until post-edit per-path reread |
| `REQ-R1R3-CURRENT-COMPATIBILITY-ACCURACY` | "do not falsely claim that the `nonSyntheticWeight` definition itself is readWord-only. It gives weight one to all three genuine constructors and zero to `syntheticCostOnlyPrimitive`; the current canonical execution is the object that is readWord-only." | Definition/execution category boundary | Quote all four definition cases and separately quote the universal theorem over the exact canonical trace object. | `WordRAM.TraceEvent.nonSyntheticWeight` -> certificate sum theorems; exact trace -> readWord-only theorem -> public prose. | Conflate the weight definition with actual trace emission, or globally delete accurate `wordRank`/`wordSelect` compatibility vocabulary. The source cases above reject both moves. | Exact cases and object distinction frozen above. | Open until final prose reread |
| `REQ-R1R3-POLICY-INHERITANCE` | "preserve the governance policy and both named regression suites byte-for-byte relative to governance commit `be1239a353a8f067b50d7d1bd8c4c10413a33100`. The base already contains passing exact-candidate fixtures for the three rejected phrases and the current controls. If policy or regression code appears to need modification, stop for coordinator scope rather than editing it." | Inherited governance | Exact Git byte comparison for `docs/internal/CLAIM_DRIFT_POLICY.json`, `scripts/claim_drift_policy_regression.ps1`, and `scripts/paper_topology_lint_regression.ps1` against governance; no changed policy/script path. | Governance commit -> unchanged production policy/regressions -> strict production scanner/topology verdict. | Attempt to make prose pass by altering an allowance, mutation fixture, or scanner. Scope audit and byte comparison must reject it. | No policy/script edit planned or authorized. | Open until byte-identity check |
| `REQ-R1R3-WORKLOG-TRUTH` | "correct the R1-R2 worklog's false exhaustive-closure impression, add the R1-R3 matrix and four-part digestion, distinguish inherited evidence from exact-candidate checks, and do not mark final checks Closed before they run successfully on the committed candidate." | Durable evidence ledger | Appended R1-R2 correction; complete R1-R3 matrix; conceptual/plain-English/assumptions/skeptical-question digestion; final commands remain open until their exact committed-candidate runs. | Source facts and inherited R1-R2 evidence -> R1-R3 candidate checks -> worklog -> final response -> coordinator audit. | Backdate a post-commit check, call inherited first-parent semantic evidence new, or leave the prior exhaustive impression uncorrected. The ledger must visibly reject each. | Correction, source facts, inventory, and frozen matrix appended before claim edits. | Open until digestion and candidate checks |
| `COMPLETE-R1R3-COMMITTED-EVIDENCE` | "Durable disposition for material work: committed updates plus the R1-R3 evidence matrix and proof digestion in `docs/internal/R1_WORKLOG.md`." "Work until all frozen R1-R3 rows close on one clean committed candidate or a valid obstruction forces coordinator review." | Candidate completeness | One clean committed candidate contains all authorized repairs, completed evidence rows, inventory, digestion, and committed-candidate check results without staging unrelated artifacts. | Matrix -> authorized docs -> commit -> committed-candidate checks -> clean tree -> coordinator exact-commit audit request. | A green scanner, a commit, or a candid caveat with any registered stale surface still present fails. | None yet; this pre-edit freeze is not candidate evidence. | Open |
| `INV-R1R2-FOUR-FACT-PRESERVATION` | "retain current cost `207` with algebra `2*35 + (2*11 + 2*37 + 30) + 11`; 22 physical sources over logical segments 0..22 with segments 0 and 19 sharing BP; live segment 21 and rejected fresh segment 23; global trace positions 0 and 15 produced by instruction positions 0 and 1." | Inherited public facts | Final current-surface reread and diff preserve each literal/category fact; no changed source. | Accepted R1-R2 facts -> unchanged source -> repaired prose -> claim scanner and diff audit. | Accidentally change a numeral, call 23 physical sources, swap live/fresh segments, or collapse global/program positions. Targeted searches must find none. | Pre-edit source/reference reread confirms all four facts. | Open until final reread |
| `INV-R1R1-SEMANTIC-PRESERVATION` | "no Lean, theorem, definition, validator, executable, payload, store, trace, receipt, or public identity change is authorized." | Inherited semantic tree | Exact changed-path authorization contains documentation/worklog only; Lean and executable tree remains byte-identical to base. | Accepted R1-R1/R1-R2 source tree -> doc-only diff -> same theorem/public identities. | Any `RMQ/`, `RMQExamples/`, script, policy, or executable path in the candidate range fails. | No semantic path changed before freeze. | Open until final scope audit |
| `INV-HISTORICAL-PRESERVATION` | "do not rewrite dated digests, audit reports, frozen matrices, prior worklogs outside the current R1 section, or earlier design-decision bodies. Historical weaker vocabulary may remain only where its historical role is explicit and accurate." | Inherited history | Final changed paths contain only amended scope; R1-R2 is corrected by an appended R1-R3 note; no historical occurrence is rewritten to make searches green. | Frozen history -> unchanged paths/bodies -> current-only synchronization. | Global removal of `wordRank`/`wordSelect` or editing dated history fails. | No historical path/body change planned. | Open until final path/diff audit |
| `INV-CATEGORY-SEPARATION` | "keep payload bits, proof-only data, modeled ticks, trace events and positions, instruction positions, physical sources and logical roles, allocated cells, Lean runtime, and measured performance distinct." | Inherited model/public categories | Final prose and worklog retain exact distinctions and change only current event-vocabulary wording. | Source categories -> current prose -> source-directed reread -> coordinator audit. | Treat weight as cost definition, call modeled ticks runtime, identify 22 sources with 23 roles, or identify trace positions with instructions. Each must be absent. | Pre-edit inventory identified no new category error beyond event-vocabulary weakening. | Open until final reread |
| `CHK-R1R3-STRICT-CLAIMS` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | Final required | Exit 0 on the committed candidate with zero strict failures. | Repaired current prose -> unchanged production scanner/policy -> strict verdict. | Exact policy mutations are a lower bound; production green does not replace the 18-path reread. | Not run on candidate. | Open |
| `CHK-R1R3-TOPOLOGY` | `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\paper_topology_lint.ps1` | Final required | Exit 0 on the committed candidate with documentary public identities resolved. | Repaired source/public alias text -> generated broad/paper checks -> production topology verdict. | A true theorem name in adjacent prose but a dead/current-misclassified alias in a claim row must fail independent review even if a lexical scan passes. | Not run on candidate. | Open |
| `CHK-R1R3-DIFF` | `git diff --check`; `git diff --check a835720ddae8816727febb16c636eee4a5f57076..HEAD`; exact changed-path authorization; exact governance-policy byte-identity check; final clean-tree and HEAD checks. | Final required | Every command exits 0 on the committed candidate; changed paths are a subset of the amended scope; policy/regressions equal governance. | Authorized docs/worklog commit -> committed range -> clean exact HEAD -> coordinator audit. | A clean worktree without a committed-range whitespace/scope check fails. | Not run on candidate. | Open |

Explicitly deferred and non-blocking: integration, coordinator acceptance,
broader submission freeze, A1/V1 launch, and roadmap-node closure. The worker
will request coordinator exact-commit audit and will not claim acceptance,
integration, push, merge readiness, or roadmap closure.

`REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, and
`REPLAY-SUBPROCESS-DEADLINE` are `NOT_APPLICABLE`: this task creates or changes
no replay harness and will not claim a replay campaign.

### R1-R3 verification coverage plan and command ledger

No Lean/build command is planned: this is a documentation-only repair over an
unchanged checked source/public-identity tree. `lake build RMQ.Headlines` is
conditional only if topology lint demonstrates missing or stale build artifacts.
No root build, aggregate gate, validator, cost harness, axiom inventory, or
policy-regression suite is proportionate or authorized absent a unique changed-
path trigger.

| Command | Role and covered rows | Unique failure mode | Tree/runtime/timeout plan | Outcome |
| --- | --- | --- | --- | --- |
| Source-directed `rg` plus manual per-path reread for `readWord`, `wordRank`, `wordSelect`, `nonSyntheticWeight`, both theorem identities, paraphrases, reordered constructors, compatibility-before-current ordering, and unregistered current-looking Markdown | Development and final semantic audit; `REQ-R1R3-READWORD-ONLY-SURFACE`, `REQ-R1R3-CLOSED-INVENTORY`, `REQ-R1R3-CURRENT-COMPATIBILITY-ACCURACY`, inherited invariants | Misleading composition outside strict scanner regex | Dirty development tree, then final committed candidate; expected seconds; timeout 2 min | Pre-edit inventory complete; post-edit run pending |
| `git diff --check` | Development and final; `CHK-R1R3-DIFF` | Working-tree whitespace errors | After edits; expected <5 s; timeout 1 min | Pending |
| `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1 -Strict` | Final; `CHK-R1R3-STRICT-CLAIMS`, policy and vocabulary rows | Production strict claim classification/allowance failure | Committed candidate; prior comparable R1-R2 ~13 s; timeout 2 min | Pending |
| `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\paper_topology_lint.ps1` | Final; `CHK-R1R3-TOPOLOGY`, public identity rows | Dead or misclassified documentary identity | Committed candidate; prior comparable R1-R2 ~83 s with artifacts; timeout 5 min | Pending |
| `powershell -NoProfile -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1 -Strict -Base a835720ddae8816727febb16c636eee4a5f57076` | Final; worklog/decision discipline | A substantive public-claim change requiring a decision entry | Committed candidate; prior comparable ~1 s; timeout 1 min | Pending; add minimal DD entry only if required |
| `git diff --check a835720ddae8816727febb16c636eee4a5f57076..HEAD`, changed-path authorization, governance policy/regression byte identity, exact HEAD, and clean-tree checks | Final; `REQ-R1R3-POLICY-INHERITANCE`, `COMPLETE-R1R3-COMMITTED-EVIDENCE`, inherited invariants, `CHK-R1R3-DIFF` | Committed whitespace, scope expansion, policy drift, dirty post-commit state | Final committed candidate; expected seconds; timeout 2 min | Pending |

### R1-R3 adversarial reread outcomes

- **Reordered three-constructor current wording:** a PCRE intersection search
  for lines containing `readWord`, `wordRank`, and `wordSelect` found only the
  repaired current statements (which say rank/select are compatibility
  constructors never emitted), the exact definition-level cases, explicitly
  compatibility-named theorem inventories, frozen matrices, dated history,
  policy/enforcement data, and this frozen contract. No unqualified reordered
  current-route disjunction remains.
- **Definition/execution conflation:** the four `nonSyntheticWeight` branches
  were reread directly. `docs/FAMILY_SUMMARY.md` now lists all four definition
  cases before separately stating the universal readWord-only execution fact.
  Other registered surfaces either give the current execution fact, give a
  true non-exclusive subset of the weight cases, or explicitly describe the
  certificate equality for the no-synthetic trace; none says the definition is
  readWord-only.
- **Compatibility theorem before stronger theorem:** README, artifact claims,
  paper correspondence, and the family summary now call the generic
  read-or-primitive/three-constructor results weaker support where they remain
  visible, and name
  `succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` as the current
  signature on the same trace object. The follow-up search found two additional
  paper-correspondence inventory rows and they were repaired in the same pass.
- **Unregistered current-looking tracked document:** repository-wide Markdown
  search found the old read-or-primitive wording in `docs/DIGESTION_LOG.md`.
  Direct context reread shows it is inside an explicitly dated 2026-07-01
  large-regime historical entry with the then-live size premise and alias, so
  `INV-HISTORICAL-PRESERVATION` requires leaving it unchanged. Other survivors
  are likewise dated history, frozen acceptance matrices, design rationale,
  policy/enforcement data, or explicit compatibility descriptions; no
  unregistered live/current repair target was found.

The development production strict scan exited 0 with 814 classified hits and
zero strict failures. `git diff --check` exited 0. The initial strict design
check correctly exited 1 because public-claim files changed without a new
decision entry; after appending `DD-20260719-002`, the same strict command
exited 0 in 2.6 seconds over six changed files. A development byte comparison
of the policy JSON and both named regression suites against governance
`be1239a...` passed. These are development results on the dirty material tree,
not final committed-candidate attestations.

### R1-R3 proof digestion and final-attestation boundary

Conceptual change: the public vocabulary identity is synchronized to the
already-checked universal theorem on the exact canonical whole-query trace.
The weaker read-or-primitive and three-constructor propositions remain only as
explicit compatibility/supporting evidence; no theorem or definition changes.

Plain-English meaning: on the accepted route, every charged trace entry is an
actual payload-word read. The model still defines historical `wordRank` and
`wordSelect` event constructors and gives them certificate weight one, but the
current canonical query never emits them.

Live assumptions: the claim is about
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right`
and its modeled trace for arbitrary shapes/endpoints. It preserves the charged-
trace boundary: controller operations remain uncharged; `207` is not Lean
runtime or measured performance; payload bits, physical words/cells, proof
data, sources/roles, and occurrence coordinate systems remain distinct.

Downstream consumers: the exact source theorem is exposed by
`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` and is
now the current identity in README, artifact claims, paper correspondence, and
the family summary. The unchanged cost, adequacy, supplied-store, and paper
capstones consume the same trace object.

Strongest skeptical next question: can any registered or plausible
current-looking document still lead a reader to treat the compatibility
three-constructor theorem as the accepted route signature, or to infer that
`nonSyntheticWeight` itself excludes rank/select? The exact 18-path reread,
repository-wide adversarial searches, production strict scan, topology lint,
and coordinator exact-commit reconstruction are the required answer.

Decision record: `DD-20260719-002` records the substantive public-claim choice
required by the strict checker. No workflow/process decision changed, so no
`WORKFLOW_DESIGN_DECISIONS.md` entry is authorized or needed.

The first commit will freeze the repaired material tree and this evidence
boundary. Final-required commands must run on a committed candidate. Any later
evidence-only commit will preserve the material claim files and will receive
its own exact-HEAD response attestation; results are not backdated into this
ledger.
