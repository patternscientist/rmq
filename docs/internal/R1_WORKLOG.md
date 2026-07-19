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
| `R1-A` | "Update both requests to the live name. Then ADD durable inventory entries for the surfaces introduced by the recent campaign rungs that have none: the same-block charged fold, the same-block occurrence/liveness witnesses, and the corruption witnesses. Verify by running both scripts to exit 0 and recording the axiom sets." Coordinator amendment after freeze: "`scripts/axiom_check.lean` has TWO independent defects"; repair the stale identifier and its unavailable `RMQ.Core.GenericSelectBPCompat` import by either adding the module to the build closure or importing modules the library actually builds; also load-check `scripts/wordram_axiom_check.lean`; both scripts must actually load and exit 0. | Both scripts request `_sum_le_207`; `axiom_check.lean` imports only built/available modules (or the closure is deliberately expanded with rationale); each inventories the charged same-block fold/value/cost or trace surfaces, actual same-block occurrence/liveness theorem, corruption/value-dependency theorem, and strengthened repeated-read theorem; both Lean invocations load and exit 0 with recorded axiom sets. | Trust inventory -> `scripts/gate.ps1` fatal WordRAM step -> Option B candidate. | A green library with an unknown inventory constant or an unavailable import fails; declaration-name-only coverage that omits new surfaces fails; file text without successful load/exit is not evidence. | Pending. | Open |
| `R1-G` | "Recompute the correct positions from the actual post-campaign singleton trace and update the fixture so it checks the true positions, keeping the property it is meant to test — two DISTINCT global positions carrying the same successful read, arising from two distinct producing instruction occurrences. Do not weaken the fixture to a tautology, do not delete it, and do not make it position-agnostic; a concrete regression fixture with correct literals is the point. While you are there, verify the neighbouring checks in that file that also index trace positions and correct any that the campaign invalidated." | Concrete singleton validator uses post-campaign numeric global positions, confirms the same successful `readWord`, confirms distinct global positions, and checks the matching concrete producing instruction positions are distinct; neighbouring indexed fixtures reviewed; executable exits 0. | `RMQ/Validation/SuccinctClassic.lean` -> `rmq_succinct_classic_validate`. | Searching the trace dynamically, comparing a position with itself, or checking only event equality fails. | Pending. | Open |
| `INV-B4-VALUE-DEPENDENCY` | Inherited INV-VALUE-DEPENDENCY: "returned values and routing decisions depend on actual charged reads"; evidence conclusions "about the returned value, decisive state/route, or a refinement chain", with "evidence quantification and validity domain" matched and recorded. | Checked existential over `xs : List Int`, `left`, `right`, canonical store and a store differing at exactly one consumed segment-21 address: `ValidRange xs left right`, consumed indexed read, agreement elsewhere, and whole-query `WithStore(...).value != WithStore(corrupt...).value`. | Same `Cartesian.shape xs` -> accepted global read store -> accepted whole-query supplied-store evaluator -> `.value`; optional physical transfer only after logical projection closes. | Accepted predicate P is whole-query answer inequality on a valid query under one-cell corruption. Rejected Q is enclosing `TraceResult` inequality caused by its trace. Component-local close inequality alone also fails. | Pending. | Open |
| `REQ-B6-04` | "Provenance must cover the ACTUAL emitted same-block events (producing instruction + occurrence position), not merely assert segment membership; deleting the same-block case from the regenerated induction must break adequacy. The W19 witness must be a same-block query, not the existing cross-block one." | One checked valid singleton `List Int` whole-query witness with an indexed successful segment-21 read and `ReviewerReadOccurrenceReceipt`, plus explicit equality tying the receipt's invocation component trace to the charged same-block LCA subtrace. | singleton `ValidRange` -> third whole-query `lcaClose` instruction -> folded pre-state with equal closes -> `.canonicalClose` invocation -> same-block component trace -> global offset -> receipt/source/counting. | Accepted P is an actual successful closed-valid occurrence for leaf `.canonicalClose` with same-block invocation. Rejected Q is component `List.Mem` or source-level liveness reached by select/rank/cross-block. | Pending. | Open |
| `REQ-B4-03` | "including B2's explicitly deferred item: occurrence granularity for REPEATED EQUAL fringe/table reads (distinct receipts for repeated equal reads, matching `repeated_equal_read_occurrences_have_distinct_receipts`). Extend the checked provenance packet(s) consumed by the paper chain rather than creating sibling packets." The two positions "must arise from two distinct program-instruction occurrences". | Public witness theorems expose `instrPos1`, `instrPos2`, their exact `ProducesEventAt`/receipt evidence, and `instrPos1 != instrPos2`, while retaining both distinct indexed global reads and complete receipts. | Singleton two select-close instructions at program positions 0 and 1 -> same component local event -> two composed global positions -> existing manifest packet fields. | `firstPos != secondPos` with existentially hidden instruction positions fails. Unrelated instruction positions not tied to the two receipts fail. | Pending. | Open |
| `R1-E` | Correct all false target statements listed by A07; add explicit payload-bit scope text: "the theorem proves exact equality of flattened payload BIT CONTENTS with the public payload; empty sentinel cells and per-cell padding are not payload bits and are not charged by it" and do not claim an allocated-cell bound; note that topology lint checks identifier topology and not prose numeric values. | `RMQPaper.lean`, `README.md`, `docs/FAMILY_SUMMARY.md`, `RMQ/Headlines/RMQ.lean`, and `docs/PAPER_MODEL_ADEQUACY.md` state 207; select/rank/fringe/interior = 35/11/37/30; 22 sources and logical segments 0..22 with shared BP role; fresh rejected segment 23 and live segment 21; exact flattened-bit scope; lint limitation. | Public paper/root/docs -> claim drift and topology checks -> reviewer-facing model. | No allocated-cell claim; no stale 76/13/4/4, 20-source, through-20, or fresh-21 current-route prose survives in assigned surfaces. | Pending. | Open |
| `REQ-B6-07` | "library green at EVERY commit"; "no dead sources"; parallel-then-swap. Complete the omitted post-freeze implementation commits `194c4e6`, `285c43e`, and `b77f385`. | Matrix evidence lists all governed implementation commits and distinguishes the historical per-commit command ledger as attested process evidence; this repair branch records `lake build RMQ` at every new commit. | Git history/worklogs -> B6 process row. | Missing governed commits or presenting process attestation as kernel evidence fails. | Pending. | Open |
| `REQ-B6-05` | Mark coordinator-confirmed: "the coordinator verified that the route literal genuinely did not move and that the authorization to move it went unused." | Matrix evidence records the supplied coordinator confirmation while retaining the checked `rfl` derivation and branch cap. | component algebra -> route literal 207 -> public consumers. | Confirmation alone cannot replace the checked derived equality; an asserted numeral fails. | Pending. | Open |
| `R1-F` | "In both matrices, relabel rows whose evidence is an attested command outcome rather than a checked proposition so they are visually distinct from kernel-checked rows (for example a status of `Closed (attested)` with the evidence tier named)." Apply this to every row enumerated by A07 and repair REQ-B6-05/07/08 honestly. | Enumerated process/verification rows use a distinct `Closed (attested: <tier>)` status or equivalent explicit evidence-tier label; semantic kernel rows remain visually distinct; B6-08 points to durable inventories after R1-A. | Acceptance matrices -> coordinator reconstruction. | Executable, artifact, Git-history, and process evidence must not be labeled as kernel propositions. | Pending. | Open |
| `COMPLETE-COMMITTED-HYGIENE` | "CANDIDATE_COMPLETE requires all R1-A through R1-F rows closed on one committed unchanged final tree"; R1-G is added at the same priority as R1-A; no forbidden constructs; `lake build RMQ` green at every commit; final gate required once on the unchanged final tree. | One committed HEAD, clean tree, exact-base range diff clean, hygiene scans clean, all required commands exit 0 with durations, and final aggregate gate passes while holding `Global\RMQHeavyVerification`. | Every row above -> exact candidate commit -> coordinator audit. | Dirty or post-verification source changes, skipped validator/gate, or a green narrow build with an open semantic row fails. | Pending. | Open |
| `INV-STORE-IDENTITY` | "the exact payload/store executed is the payload/store counted by the public space theorem; a theorem about a sibling payload is insufficient". | R1-B uses the canonical accepted global store and changes exactly one segment-21 word/cell; same source/table object remains counted by the public payload chain. | reviewer payload -> global logical store segment 21 -> whole-query execution. | A separately built component table with no equality to the canonical store fails. | Pending. | Open |
| `INV-SEMANTIC-NONVACUITY` | Semantic coverage, liveness, ownership, and refinement predicates are derived from the operational construction. | R1-C uses existing `HasClosedValidOccurrence`/receipt relations on the actual whole-query run, with full guard and occurrence data. | Valid ordinary query -> actual emitted global occurrence -> actual component local occurrence. | A `True` predicate, source enumeration, or compatible component membership fails. | Pending. | Open |
| `INV-TRACE-EXECUTION` | "traces and footprints are derived from the execution they describe". | All new occurrence facts are obtained from `ProducesEventAt`/`global_getElem`, never a hand-written trace. | accepted program fold -> instruction trace -> composed global trace. | Synthetic or separately constructed trace fails. | Pending. | Open |
| `INV-STORE-AGREEMENT` | "supplied-store agreement determines result, cost, and the relevant trace". | R1-B corruption store agrees with canonical store everywhere except the named consumed address; evaluator difference is derived by reduction/refinement of the actual supplied-store evaluator. | canonical store / one-cell variant -> same evaluator. | Replacing an unconsumed address or changing multiple regions without an agreement theorem fails. | Pending. | Open |
| `INV-READ-BACKING` | "every successful read is backed positionally by the counted store". | R1-B/C exhibit the successful segment-21 occurrence and reuse the existing receipt/source/counting chain. | indexed event -> source -> region -> counted payload. | `List.Mem` without position or source/counting receipt fails. | Pending. | Open |
| `INV-PROOF-SEPARATION` | "proof-only fields never carry answers or uncharged routing information". | New answer inequality is about evaluator `.value` under supplied-store mutation; no proof packet computes the answer. | store reads -> chunk decode/fold -> close -> whole-query answer. | An answer injected after reads or obtained first from reference semantics fails. | Pending. | Open |
| `INV-NO-SYNTHETIC` | "synthetic events, decorative rereads, and post-hoc replay do not support the execution claim". | The changed segment-21 entry is an actual consumed read whose decoded result changes the whole-query answer. | accepted read event -> returned answer. | A trace-only disagreement or unread-cell mutation fails. | Pending. | Open |
| `INV-CATEGORY-SEPARATION` | Payload bits, proof fields, model ticks, machine state, Lean runtime, and measured performance remain distinct. | Kernel theorems close semantic rows; executable validator is labeled executable evidence; matrix/history commands are attested; payload scope explicitly excludes cell padding/sentinels. | theorem and artifact evidence tiers remain explicit. | Presenting `#guard` or process logs as theorem evidence fails. | Pending. | Open |
| `INV-PUBLIC-COMPOSITION` | A theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution and over the same validity domain. | No accepted object changes; additive R1 theorems and corrected prose point to the existing canonical payload/execution and `ValidRange` domain. | public builder/payload -> canonical store -> accepted execution -> answer/cost/provenance. | Sibling payload/store or guarded/unguarded mismatch fails. | Pending. | Open |
| `DEFER-COORDINATOR-AUDIT` | "Explicitly deferred work: coordinator exact-commit audit and integration after this worker reports CANDIDATE_COMPLETE." | Report exact candidate commit and frozen matrix; make no acceptance, integration, merge, or push claim. | Candidate -> coordinator-owned audit/integration. | Worker self-acceptance fails. | Explicitly deferred and non-blocking. | Deferred |

The replay acceptance IDs `REPLAY-EXACT-REGISTRY`,
`REPLAY-SELECTOR-NONVACUITY`, and `REPLAY-SUBPROCESS-DEADLINE` are
`NOT_APPLICABLE`: this repair does not use a mutation replay harness and will
not claim count-only or vacuous replay evidence.

## Verification coverage plan and command ledger

All commands operate on this worktree only. Commands expected to exceed five
minutes acquire `Global\RMQHeavyVerification` and release it in `finally`.
Only one heavy Lean/Lake process runs at a time.

| Command | Role | Paths / rows covered | Distinct failure mode | Expected runtime and timeout | Final result |
| --- | --- | --- | --- | --- | --- |
| `lake build RMQ` | Development loop and required at every commit | All Lean changes; all semantic rows | Elaboration/import regression | A07 comparable 462 s cold; mutex; timeout >= 20 min | Pending |
| focused touched-module build(s) | Development loop | R1-B/C/D | Local theorem/type error before broad build | Expected < 10 min; mutex if projected > 5 min | Pending |
| `lake build RMQPaper RMQExamples` | Final required | R1-E/public consumers | Narrow paper/example import or statement drift | A07 comparable 109 s; timeout 10 min | Pending |
| `lake env lean scripts/wordram_axiom_check.lean` | R1-A development + final required | R1-A, B6 inventories | Unknown declaration or new trust dependency | A07 reached failure in 106 s; timeout 10 min | Pending |
| `lake env lean scripts/axiom_check.lean` | R1-A development + final required | R1-A, broad trust inventory | Unknown declaration or unexpected axiom | Expected several minutes; mutex if needed; timeout 15 min | Pending |
| `lake env lean scripts/headline_axiom_check.lean` | Final required | Public headline trust surface | Public theorem trust drift | A07 comparable 46 s; timeout 10 min | Pending |
| `lake exe rmq_succinct_classic_validate` | R1-G development + final required | R1-G and neighbouring fixtures | Stale concrete trace indices or differential validation failure | Base scout comparable 128 s; timeout 10 min | Pending |
| `lake exe rmq_succinct_classic_cost_harness` | Final required | 207 and charged-route behavior | Derived-literal or route-cost executable regression | A07 comparable 74 s; timeout 10 min | Pending |
| `scripts/claim_drift_scan.ps1` | Final required | R1-E/F | Claim vocabulary/numeric drift in configured surfaces | A07 comparable 24 s; timeout 5 min | Pending |
| `scripts/paper_topology_lint.ps1` | Final required | R1-E | Identifier topology and documentary resolution (explicitly not prose-number validation) | A07 comparable 91 s; timeout 10 min | Pending |
| `scripts/design_decision_check.ps1 -Strict -Base 1a825f3...` | Final required | DD/worklog discipline | Missing nontrivial design rationale | Expected < 1 min; timeout 5 min | Pending |
| hygiene `rg` scans | Development + final required | COMPLETE-COMMITTED-HYGIENE | Forbidden trust/runtime constructs | Expected < 1 min | Pending |
| `git diff --check` and `git diff --check 1a825f3...HEAD` | Development + final required post-commit | COMPLETE-COMMITTED-HYGIENE | Working-tree or committed whitespace defects | Expected < 1 min | Pending |
| `scripts/gate.ps1` | Final aggregate, required once on unchanged final tree | Entire repair campaign | Cross-surface integration and fatal inventory omission | A07 stopped at 135 s; prompt allows >45 min; mutex; timeout 75 min | Pending |

Any source/theorem/executable edit invalidates transitive Lean checks. A
docs/matrix-only edit invalidates claim/design/topology/diff checks but not an
already checked unchanged Lean object. The final aggregate gate is run at most
once on an unchanged candidate tree unless it does not complete; a late failure
is repaired through its smallest component before one final certification run.

## Parallelization check

The join theorem is the accepted whole-query route plus its reviewer-facing
evidence. Three independent read-only inventories were delegated: R1-B value
dependency; R1-C/D/G provenance and validator positions; R1-A/E/F trust and
document/matrix drift. R1 retains sole ownership of all edits, shared records,
public theorem signatures, verification, and commits.

## Milestone ledger

Every checkpoint records tree identity, exact command, exit code, duration,
process disposition, and the reason for any rerun.

| Milestone | Tree / diff | Command | Exit | Seconds | Process and rerun disposition |
| --- | --- | --- | ---: | ---: | --- |
| Frozen matrix baseline | HEAD `1a825f3a940f0ff59084b69b25ba0c318569f33f`; only untracked `R1_WORKLOG.md` | mutex-held `lake build RMQ` | 1 | 0.197 | Sandboxed launcher could not reach GitHub; process ended. This was an environment failure before Lean/build work. |
| Frozen matrix baseline | Same Lean tree; only untracked `R1_WORKLOG.md` | approved-access, mutex-held `lake build RMQ` | 0 | 695.834 | Material rerun condition: approved toolchain/cache network access. Single owned process; 238 jobs; build completed successfully. |
| Frozen matrix amendment recheck | Same Lean tree; worklog records the coordinator's second R1-A defect | sandboxed `lake build RMQ` | 1 | 0.066 | Launcher network failure; process ended before build work. |
| Frozen matrix amendment recheck | Same Lean tree; amended untracked worklog only | approved-access `lake build RMQ` | 0 | 0.332 | Material rerun condition: approved toolchain access. Cached build completed successfully; the worklog is not an RMQ build input. |
