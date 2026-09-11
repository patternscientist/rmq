# PQ1 continuation audit, 2026-09-11

## Frozen scope and acceptance

User request: "You hit a usage limit and Claude picked up where you left off.
Audit the work and make any changes if you'd like / if necessary."

This is a continuation audit and repair, not coordinator acceptance of the PQ1
milestone. The source target is e1b08483955980080c6cd6a5c87ab6dcd02758ab;
the comparison base is 8910d5364677f296462665e9cbf99e409b76321a; workflow
governance is 4639223bc8130b0ef752270b5cbdd74325abcd60. Coordinator and
proof-sprint preflights passed with all three canonical/runtime RMQ skills.

The root owns repairs and the single Lean/Lake build slot. Three independent
read-only agents inspect certificate/consumer/evaluator proofs, replay/runtime
validation, and paper/model/status correspondence. Their frozen prompts are
preserved in the task's ignored `.lake/pq1-review-prompts` directory; this
document is the durable synthesis. These are bounded support reviews, not a
fresh blind whole-candidate acceptance audit.

Frozen repair scope: `scripts/owned_process_tree.ps1`,
`scripts/packed_query_replay.ps1`, `docs/WORD_RAM_REVIEW_PACKET.md`,
`docs/internal/packed_query/PQ1_VALIDATION_PLAN.md`, this report and
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`. No Lean source change is planned.

| ID | Exact frozen requirement | Scope / consumer | Required evidence and challenge | Status |
| --- | --- | --- | --- | --- |
| AUD-01 | Audit the work and make any changes if you'd like / if necessary. | Continuation delta, three support reviews and root reconstruction | Record source-supported findings and dispositions; distinguish proof correctness from acceptance status. | OPEN |
| FIX-01 | Repository cleanliness must use Git state output, preserve diagnostics, and reject command failures and actual dirty state. | Shared bounded Git observer consumed by replay restoration | Clean LF bytes under autocrlf=true must pass despite a real conversion warning; tracked, staged and untracked mutations must fail; a nonzero Git command must fail. | OPEN |
| FIX-02 | The frozen certificate registry must reject extra declarations even when their names use legal non-alphanumeric Lean spelling. | Complete and marked field/initializer inventory consumed by Assert-Registry | Reproduce the underscore bypass; reject underscore, apostrophe, Unicode and escaped-name additions inside and outside both marker regions through the production verdict, preserving the unchanged expected-accept control. Unsupported declaration layout must fail closed. | OPEN |
| FIX-03 | Describe the exact invalid guard count with its actual branch condition. | Review packet consumed alongside QueryCertificate | Four steps when left >= right; otherwise six for an invalid range. Check n=0,left=1,right=1, which satisfies right>n but takes four. | OPEN |
| CHK-01 | Run affected production checks and the complete committed 38-case replay with restoration. | Audit repair and unchanged Lean public contract | Owned full replay, exact source commit, all 38 expected verdicts and 15 runtime fixture IDs, restored bytes and clean tree; relevant script, claim, paper, hygiene and whitespace checks. | OPEN |

The full aggregate gate and fresh blind exact-commit acceptance audit remain the
existing milestone obligations. This task does not change their status or
substitute support review for them. No semantic model, payload accounting,
theorem surface or trust-base change is authorized by these repairs.

## Initial execution evidence

The first complete replay attempt at the source target stopped after C01 in
123.526 seconds, without timeout or surviving owned process. Its producer and
public builds passed, `checkC01` rejected the weakened field as expected, exact
source bytes were restored, and the restored consumer passed. The subsequent
clean-state check misclassified Git stderr warnings about LF-to-CRLF conversion
as dirty paths. The report correctly records `Completed=false` at
`.lake/pq1-replay/run-e05b8f68df9940babb9ea3449cf7f0f2/report.json`.
Registry, diagnostic, selector-boundary, 45-file committed provenance and owned
deadline self-tests passed before that failure. This is incomplete replay
evidence, not a successful campaign.

## Review findings and final evidence

The three exact-target reviews completed all their `REQ-REVIEW-SCOPE`,
`REQ-REVIEW-EVIDENCE` and `REQ-REVIEW-NONCLAIM` rows. They found two P2 issues;
the root found a third by executing the replay. None is a Lean proof defect.

1. **Git diagnostic/state conflation (P2, FIX-01).** The shared helper returned
   merged stdout/stderr as machine-readable Git state. The repair preserves the
   existing combined `Output` for diagnostic consumers, adds separate stream
   arrays, checks failures before using stdout, and emits successful stderr as
   warnings. Real temporary-repository controls pass for an actual conversion
   warning, clean LF and CRLF bytes, rejected tracked/untracked/staged changes,
   and a rejected nonzero Git command. The warning control runs at initial add:
   later state-query warnings depend on Git's stat cache. No autocrlf override
   or diagnostic-text filtering is used to change the cleanliness verdict.
2. **Incomplete declaration inventory (P2, FIX-02).** The original production
   `Assert-Registry` was invoked in memory with an extra `unregistered_field`
   and initializer inside both markers; it accepted them. The ASCII name regex
   ignored legal identifiers. The revised early scanner catches every member
   token at the declared source indentation and rejects the tested unsupported
   indentation. A follow-up review found that Lean permits a more-indented
   default field; the authoritative elaborated-metadata check below closes that
   boundary. Its five negative controls and unchanged control compiled and
   passed against the actual 33-field certificate. This does not weaken any
   exact-type consumer or alter any proposition.
3. **Invalid-guard wording (P2, FIX-03).** The review packet incorrectly said
   six steps whenever `right > n`. The producer's exact conclusion is
   `steps = if left < right then 6 else 4`, under
   `not (left < right and right <= n)`. At `n=0,left=1,right=1` the first guard
   takes four steps despite `right>n`. The packet now states four when
   `left>=right`, otherwise six. The manuscript's existing at-most-six claim
   was already correct.

### Proof and consumer reconstruction

The proof reviewer inspected `QueryCertificate.lean`, `ArrayRun.lean`,
`Capstone.lean`, `PackedQueryContract.lean` and direct load-bearing definitions.
All 33 fields concern the same
`run (buildMemory xs) queryProgram queryBudget (initialState xs.length left right)`.
The canonical theorem supplies `queryRun_execution_safe` itself; no supplied
correctness, readiness, or successful-load premise escapes into the public
alias through `RMQPaper`.

- `specResult` concludes that every valid range's actual result is
  `some (scanWindow xs left (right-left) + 1)`. It follows packet decoding and
  the proved reference contract, without a caller-supplied correctness premise.
- `noFailedLoads` follows the stronger theorem that every canonical receipt
  replies `some value`: a failed physical load faults and cannot later halt.
- `invalidGuardSteps` follows concrete guard execution of four or six steps.
  Its domain is every invalid natural endpoint pair.
- `runArray memory program.toArray fuel s = run memory program fuel s`
  preserves the complete `Run`, including transitions, repeated receipts and
  final state, for arbitrary memory/program/fuel/state. The runtime fixtures
  execute that exact array program and retain direct list-program controls.
- The public expected-type consumer projects all 33 exact propositions and
  contains 38 literal definitional pins. A fuel bound alone would not imply
  completion, but the same-run halt and answer fields provide it here.

The replay reviewer traced C01-C33 to their corresponding `checkCNN`, P01 to
`publicContract`, D01 to `pinInstructionCategory` after a closure rebuild,
R01 to the exact `specResult` initializer, and N01 to the literal-answer runtime
failure. Fixture answers are independent reference/literal values. S10 changes
loaded metadata and checks a changed answer; S11 changes an actually unread
allocated word. Source inspection alone is not recorded as replay execution.

### Paper and model reconstruction

The paper reviewer matched the manuscript's six clause groups to the capstone,
including common width, counted data/code/registers, reference answers,
halting/charging, safety and positional read backing. Logical read expansion
uses the stored bit span and preserves ordering and repetition. Missing or
zero-length logical spans produce no load under the declared semantics;
failed actual loads remain logged and faulting. The explicit unit-cost model
includes multiplication, division/remainder and variable shifts; preprocessing
and Lean execution time are separate.

The manuscript's base `3849ecbb53bbedfcd679352cc68d095fa5a304c2` has no Lean
library delta from the review target. Candidate/process status is explicit;
the ledger's documented kernel-status exception for `L-PQ-01` records neither
integration nor coordinator acceptance. The 210 trace and 427 probe claims
remain distinct from the primitive-instruction theorem. Primary-source spot
checks supported the cited operation-model terminology; the reviewer did not
re-verify every bibliography metadata field or every published version.

These support reviews performed source inspection, governance preflight,
committed-diff whitespace checks and both trust/hygiene scans. They ran no
Lean/Lake or mutation processes. Root's verification outcomes are recorded
separately below; the historical pending milestone rows are not proof holes.

Contract amendment (root coordinator, before adding the check): FIX-02's
source-only parser is insufficient. Lean 4.22 allows a later defaulted field at
greater indentation, which can look like a continuation. Extend repair scope
to `scripts/packed_query_inventory_check.lean` and `docs/internal/DESIGN_DECISIONS.md`.
The authoritative completeness check will compare elaborated structure metadata
with a literal field list after the baseline build. Preserve the textual
diagnostic and test its known boundaries; do not claim it parses all Lean.
No library theorem or public proposition changes.

### Verification checkpoint before full replay

The new Lean metadata check passed (actual=33; unchanged accepted;
defaulted/indented, underscore, apostrophe, Unicode, escaped and absent controls
rejected). The production registry and diagnostic self-tests passed. The
shared process helper's deterministic, collection and Windows grandchild
barrier self-tests passed; the grandchild was absent immediately after owned
termination. The full replay will run only after committing this repair tree.
