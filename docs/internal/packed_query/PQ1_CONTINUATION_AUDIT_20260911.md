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
| AUD-01 | Audit the work and make any changes if you'd like / if necessary. | Continuation delta, three support reviews and root reconstruction | Record source-supported findings and dispositions; distinguish proof correctness from acceptance status. | PASS: three findings fixed; support reviews and evidence below. |
| FIX-01 | Repository cleanliness must use Git state output, preserve diagnostics, and reject command failures and actual dirty state. | Shared bounded Git observer consumed by replay restoration | Clean LF bytes under autocrlf=true must pass despite a real conversion warning; tracked, staged and untracked mutations must fail; a nonzero Git command must fail. | PASS: real Git fixtures on both PowerShell hosts; formerly failing C01 restoration passed with warnings retained. |
| FIX-02 | The frozen certificate registry must reject extra declarations even when their names use legal non-alphanumeric Lean spelling. | Complete and marked field/initializer inventory consumed by Assert-Registry | Reproduce the underscore bypass; reject underscore, apostrophe, Unicode and escaped-name additions inside and outside both marker regions through the production verdict, preserving the unchanged expected-accept control. Unsupported declaration layout must fail closed. | PASS under the explicit metadata-check amendment below: production text controls plus actual compiled field inventory and controls. |
| FIX-03 | Describe the exact invalid guard count with its actual branch condition. | Review packet consumed alongside QueryCertificate | Four steps when left >= right; otherwise six for an invalid range. Check n=0,left=1,right=1, which satisfies right>n but takes four. | PASS: wording matches the exact conditional; producer and C33 consumer checked. |
| CHK-01 | Run affected production checks and the complete committed 38-case replay with restoration. | Audit repair and unchanged Lean public contract | Owned full replay, exact source commit, all 38 expected verdicts and 15 runtime fixture IDs, restored bytes and clean tree; relevant script, claim, paper, hygiene and whitespace checks. | PASS as a resumed same-commit campaign: exact 38-case union and 15 runtime IDs checked; single uninterrupted invocation remains explicitly uncertified. Other required local checks passed below. |

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

## Final replay evidence at the repair commit

Repair commit: `c0ba2a31666ab3059982dba0e26cfed52a9ffa5e`. All 38 registered
cases were checked at this exact commit, with identical hashes for all nine
protected source files across the four case reports. The root independently
checked registry equality, distinct complete case coverage, every expected
verdict and every post-restoration success record. This is a resumed campaign,
**not a successful single uninterrupted full invocation**.

The full attempt at this commit passed C01-C33, P01 and A01, including their
restored builds and clean-tree checks. It then stopped because the ambient
Elan `lake.exe` launcher attempted a blocked network download before D01's
build. It correctly recorded `Completed=false` after 1346.061 seconds, without
a timeout or output overflow. The installed toolchain's Lake executable
reported Lean 4.22.0 and worked directly. No repository/toolchain setting was
changed: focused reruns placed that installed `bin` directory first on their
process-local PATH. Following the smallest-failing-component verification
rule, the already passed 35 cases were retained and the three remaining cases
and full runtime registry were run at the same source commit.

| Evidence under `.lake/pq1-replay/` | Coverage | Outcome |
| --- | --- | --- |
| `run-08f05f5435094a8d96adb69366306eb9/report.json` | C01-C33, P01, A01 | 35 post-restoration successes; parent invocation incomplete at D01 launcher failure. |
| `run-bb09fb6e0eee46e49d73c6fb44e7f303/report.json` | D01 | Complete; mutated producer closure built in 172.852 s, consumer rejected only at `pinInstructionCategory`, restored closure built in 173.833 s, restored consumer and clean state passed. |
| `run-ff22725183fa44e3aea1fcd01f763c60/report.json` | R01 | Complete; changed specification packet rejected at the exact `specResult` producer initializer; restoration passed. |
| `run-05b164390ee4464ab4148d5e217671bc/report.json` | N01 | Complete; wrong literal expected answer rejected by the runtime result check; clean state passed. |
| `run-649e006a7351452dbd9bfa574ba4d143/report.json` | Full runtime and selector controls | Complete; all 15 S01-S15 fixtures, both list-evaluator controls, four invalid selectors and the focused valid selector passed. |

The runtime first re-elaborated `ArrayRun.lean` successfully. Its complete
15-fixture stage took 131.009 seconds under the unchanged 1200-second deadline.
Observed valid-query counts remained 6003-16358 primitive steps. Invalid
fixtures returned in four or six steps with no reads; the independent route
checks covered same, adjacent and non-adjacent summary blocks. The report's
large-route limitations remain unchanged: finite fixtures do not replace the
universal Lean theorems.

The replayable source for every case, expected failure surface, control and
restoration check is committed in `scripts/packed_query_replay.ps1` and its
validation modules. The root's checked report join is retained locally at
`.lake/pq1-continuation-case-coverage.json`; this synthesis does not turn an
incomplete parent report into a completed report.

## Other verification and reviewer follow-up

- Both the Windows PowerShell 5.1 and PowerShell 7.6.5 real-Git fixture runs
  passed clean LF/CRLF, real diagnostic separation, dirty tracked/untracked/index,
  restoration and nonzero-command controls. Windows process ownership,
  collection and grandchild-termination self-tests passed.
- The registry, diagnostic, script-boundary selector and 45-entry committed
  provenance self-tests passed. The final metadata check passed before each
  mutation run. Follow-up independent reviews found no remaining issue in
  FIX-01 or the authoritative FIX-02 metadata guard.
- `constant_sync_check.ps1 -SelfTest` passed. Claim-drift self-tests passed;
  the policy regression passed 88 expected rejections, 42 expected acceptances
  and 16 path/context/bypass controls, including tracked-state restoration.
- `paper/check_paper.ps1 -SelfTest` and its citation self-tests passed against
  an isolated local checkout of the exact repair commit, while the main replay
  temporarily mutated sources. The same checkout's hygiene and native-decision
  scans found no matches. Its Lean library and build inputs were unchanged
  from manuscript pin `3849ecbb53bbedfcd679352cc68d095fa5a304c2`.
- Strict design-decision checking and committed-range whitespace checking
  passed before replay. The repair introduces no library theorem, proposition,
  payload, operation model or trust-base change.

The bibliography follow-up checked all eight added entries' basic metadata
and DOI against publisher or author-institution records without finding a
repository correction. Available primary versions supported the nearby model
claims. Some published full texts and the AMT detailed instruction inventory
were unavailable for independent full-version checking. The follow-up also
corrected the support review's HMP link to the actual
[Hagerup-Miltersen-Pagh accepted manuscript](https://www.rasmuspagh.net/papers/det-jour.pdf);
the repository's bibliography required no edit.

The final `wordram_axiom_check.lean` and `headline_axiom_check.lean` runs passed:
348 and 114 dependency lists, respectively, contained only `propext`,
`Classical.choice` and `Quot.sound`. Neither contained `sorryAx` or
`Lean.ofReduceBool`. Both ran sequentially under an owned 600-second bound,
finishing together in 96.719 seconds. The separate production
`claim_drift_scan.ps1 -Strict` run passed with zero strict failures; the earlier
`-SelfTest` invocation exits after its controls and was not substituted for
this production scan.

## Disposition and proof digestion

The continuation audit and its three repairs are complete. No concrete defect
was found in the inspected Lean proof delta. Claude's added fields expose the
reference answer, successful physical loads and guard cost directly on the
actual canonical execution; the array evaluator preserves that complete
execution by equality. The repairs make validation less likely to reject clean
source or overlook added certificate fields, and correct one guard-cost sentence.

The live model assumptions remain explicit: logarithmic-width words and
unit-cost scalar operations including multiplication, division/remainder and
variable shifts. These are query-model results, separate from preprocessing
and Lean runtime. No optimality or attainment of the instruction budget is
asserted. A skeptical reviewer should next ask for the frozen whole-milestone
certification, rather than infer it from this bounded audit.

No full `lake build` or aggregate `scripts/gate.ps1` was run for this repair:
the scoped work changes validation and prose, while the affected producer
closure, public consumer, runtime evaluator and trust inventories were checked
directly. **PQ1 remains a candidate.** Its existing aggregate gate and fresh
blind exact-commit acceptance audit are still required; this report neither
records coordinator acceptance/integration nor closes those roadmap rows.
The evidence-only report update after the repair commit changes no tested
source, consumer, replay runner, or claim surface.
