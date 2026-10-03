# V1-BLIND — P2-01 continuation audit

## Findings and verdict

**P2-01 is closed on `ff92a2f94a97655a995ec744150ae7bab15ccb56`. Source verdict: MERGE_READY_WITH_FOLLOWUPS.** No remaining source defect requiring repair was established within R1–R6. Replacement artifacts, coordinator acceptance, required hosted checks, protected merge and release tagging remain pending. This verdict does not certify those future actions.

The actual production consumer now requires a completed process and the correct normal exit: rejection needs exit 1 plus the intended failure diagnostic; acceptance needs exit 0 plus any required allowance/output witness. A timeout, failed cleanup status or overflow invalidates either result. At `scripts/claim_drift_policy_regression.ps1:799–857`, these checks feed the real failure counter used by the aggregate. The focused regression extracts and invokes this function's production AST; it does not restate the predicate.

The retained old candidate remains a discriminating negative. Its actual consumer accepted the real result `Code=124, TimedOut=true, Cleaned=true` after the intended diagnostic. The repaired consumer rejects that condition. My fresh, unmodified final-source focused replay reached the exact intended diagnostic, observed the real timeout, rejected the verdict and passed the explicit two-PID death assertion. Its outer exit was 0 because correctly rejecting that deliberate negative is the control's expected outcome. Deliberate `CLAIM-POLICY-REGRESSION: FAIL` lines in these controls must not be mistaken for failed production policy cases.

Two bounded observations qualify the conclusion:

- The consumer is not a validator for arbitrary malformed PowerShell objects. My actual-AST fault injection found that missing timeout/overflow fields, null flags, a string `"false"` cleanup value and a string `"0"` exit can be accepted through PowerShell coercion. Missing cleanup or exit fails. These require replacing the trusted producer: the supported scanner path always constructs all fields from integer exit values and literal Boolean flags, or throws. Captured scanner text is never deserialized into that status object. This is an optional hardening opportunity, not a demonstrated remaining P2-01 path. Do not advertise acceptance as validation of externally supplied status objects.
- Shared-runner ownership retains its existing scope. Windows closes the owned job; if member enumeration throws, its existing fallback waits only for the root. POSIX contains the inherited process group, not a descendant that creates a new session. Consequently, “every possible cleanup failure throws” and universal descendant containment would overstate the implementation. The required normal inherited-descendant controls additionally check both recorded PIDs after the barrier; those checks pass. No new regression in the shared runner was introduced.

Smallest mandatory source repair: **none identified**. The remaining mandatory work is the delivery/hosted sequence described below.

## Identity, independence and scope

- Handle: V1-BLIND. Mode: returning auditor, explicitly labelled continuation of my own finding; this is not a new blind audit or a second independent gate.
- Target and checkout: `ff92a2f94a97655a995ec744150ae7bab15ccb56`, `codex/v1-finalization`, `C:/Users/poin/.codex/worktrees/v1-finalization/RMQ`.
- Original failed candidate: `4ded05caa68531307d0e9c827161a8611a477015`. Intermediate repair/full-run source: `143fa1e5408cff0ece537129b26c7c409891d792`.
- Original report remains 66,510 bytes, SHA256 `d19d2b027295c1de6ee0b9c0dfbdc60539dfb61b0f51878dc5d88ef3a56ccfd4`. Its historical NOT_READY verdict remains intact.
- Preflight passed against governance ref `ee44f04a561f2194b3713f071c26b6faf9ba7fab`, with `-AllowNoRequiredSkills` and the actual runtime catalog `rmq-proof-sprint,rmq-audit-prompt,rmq-coordinator`. Applicable audit-worker role skills: none. The continuation provisions of `docs/internal/AUDIT_PROTOCOL.md` were read. Evidence: `repair-audit-evidence/preflight.log` and `preflight.receipt.json`.
- Source stayed pinned and clean. The entire base-to-target delta has exactly four paths: `.github/workflows/release-artifact.yml`, `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, `scripts/claim_drift_policy_regression.ps1`, and new `scripts/claim_drift_policy_process_regression.ps1`. All Lean files, toolchain, Lake configuration, theorem interfaces, mathematical DDs and shared runner are unchanged.

I reviewed the complete delta and the actual scanner/verdict/owned-runner and reproduction/checker boundaries. Independent read-only leaves checked process evidence, exact policy mappings and workflow consumers; their scripts and detailed reports are under `repair-audit-evidence`. All writes in this continuation were confined to this new report and that evidence directory. Neither checkout/ref was moved; the original dirty working tree, original report and historical inputs were not edited. No source repair, commit, publication or message to another chat occurred.

Packet root for all evidence references below: `C:/Users/poin/Documents/RMQ/research-duet-20261001/implementation/fresh-blind-release-20261002`.

## Frozen requirements and dispositions

The following requirement and evidence-obligation text is quoted exactly from `REPAIR_CONTRACT.md`.

| ID | Frozen repair requirement | Evidence obligation | Disposition |
| --- | --- | --- | --- |
| R1 | Require normal scanner exit1 for rejection, exit0 for acceptance, no timeout, successful cleanup and no output overflow before interpreting diagnostics. | Production verdict controls for normal accept/reject, wrong exit, timeout, cleanup failure and output overflow. | SATISFIED for the supported production producer/consumer boundary. Actual consumer checks and fresh controls described below; arbitrary-object limitation recorded above. |
| R2 | Reuse the shared owned process runner, preserving finite positive deadlines, process-tree cleanup and finally restoration. | Real fail-then-hang through production scanner/verdict functions; Windows5.1, pwsh and POSIX process ownership checks. | SATISFIED for the required inherited-descendant controls, with the existing ownership limits stated. All three final-source records reach the antecedent; fresh pwsh replay corroborates it. |
| R3 | Retain each case's actual exit, timeout, cleanup and output-limit status in full-run logs. Preserve all134 policy and21 context IDs and semantics. | Full production regression both Windows shells; exact registry and process-status reconstruction. | SATISFIED. All 155 cases in each full run have independently source-mapped normal completion; transfer to final source is explicit and limited. |
| R4 | Keep the exact failed candidate as a named discriminator; no test-only copy of the verdict predicate. | AST extraction of actual production functions, historical candidate fails repaired expectation; original report/probe untouched. | SATISFIED. Authenticated probe2 and the original probe preserve the old failure; the new committed control invokes actual production functions and is nonvacuous. |
| R5 | Preserve failed and superseded evidence, pin new source, refresh affected checks/artifacts before acceptance. | Independent continuation review, final checks, archive identities, then hosted CI. | PARTIAL / COORDINATOR FOLLOW-UP. Evidence preservation, exact-source review and affected local checks are supported. Replacement archives, final delivery qualification and hosted CI remain pending. |

R6 amendment, quoted exactly:

> Coordinator amendment before the follow-up edits: add R6, align the tag-release
> workflow's checkout depth and log location with the existing branch reproduction
> workflow so the same retrospective/clean-baseline checks receive valid inputs;
> mark hyphenated version tags as prereleases. Own `.github/workflows/release-artifact.yml`
> and append WDD-20261003-V1-RELEASE-PREFLIGHT. Do not change the checked commands,
> required hosted contexts, protections or version. Verification: inspect the
> actual caller/checker relationship, parse the resulting shell blocks, strict
> per-commit design check and independent continuation review. Hosted execution
> remains pending until publication.

**R6: SATISFIED at source/local-check level; hosted execution pending.** Full-history checkout and external log match the branch workflow's actual inputs. Only new hyphenated releases receive the added prerelease flag; existing releases retain the upload-only branch and their prior classification. No stable promotion, checked-command weakening, version or protection-configuration change is hidden in the delta. Remote protection state was not queried.

R2 timing amendment, quoted exactly:

> Measured timing amendment for R2: the first POSIX test at143fa1e5 expired after
> five seconds before emitting the required diagnostic, so it failed (receipt
> `process-posix.receipt.json`). A copied isolated control with a fifteen-second
> margin passed all11 controls and descendant cleanup (`process-posix-margin.receipt.json`).
> Adopt fifteen seconds for that synthetic timeout only, retain both records,
> and rerun the focused control on final source in all three shells. The normal
> production scanner deadline remains thirty seconds. Do not edit source while
> the full143fa1e5 Windows runs are still active.

**Disposition: supported with historical-record limits retained.** The five-second attempt is failed, the isolated margin test is a separate experiment, and the final three-shell records use final source. Only the synthetic deadline changes 5000→15000 ms; ordinary scanning remains 30000 ms, and both deliberate sleepers remain 60 seconds. Full Windows receipts begin/end at143fa; final focused receipts begin/end atff92. Historical receipts do not continuously attest the worktree or record every consumed blob at launch; no missing chronology is invented. This continuation made no source edits.

Negative-reproduction amendment, quoted exactly:

> Independent negative reproduction: `coordinator-negative-probe2/receipt.json`
> reproduced the exact old P2-01 with matching clean initial/final4ded source.
> The first copied probe's Git commands were denied by safe-directory protection;
> its blank identity fields cannot authenticate a target, despite its zero exit.
> It is retained under `coordinator-negative-probe` as a failed identity-check
> attempt and is not qualification evidence.

**Disposition: supported.** Probe2's four copied production functions exactly match old-source AST extents; raw source SHA256 `ac004c96a73ab69eac7c135e2035190c6533c144716ec9261af0d568f7f278a0` matches the Git source with checkout CRLF conversion. Copied-function SHA256 is `81e30bc6a53f1d6b5c94403fc7da6dea1069683fb6db2e54a51a74a699d5a295`. Driver/functions/scanner bytes match the original audit probe. Its recorded launch working directory does not substitute the dirty checkout's source: the driver scopes Git to the old audit checkout, reads its scanner functions/policy, and runs the synthetic child in its isolated probe directory. Probe1's blank identity remains disqualifying. Fresh independent authentication exited0 in3.5694618 s under a90-second outer bound; details are in `registry-audit/negative-validation/NOTES.md` and `RESULT.json`.

## Actual verdict and ownership evidence

Production flow is `Test-FinalVerdict` → `Invoke-StrictClaimScan` (`claim_drift_policy_regression.ps1:766–797`) → `Invoke-BoundedProcess` (`:629–650`) → unchanged `Invoke-RMQOwnedBoundedProcess`. The wrapper requires a positive millisecond deadline, converts it to a positive second bound, sets a 16 MiB output cap, and returns timeout/exit/overflow/ownership plus cleanup status after the helper returns. Git subprocesses also reject incomplete/nonzero results. Output redirects are files, avoiding inherited-pipe waits. Existing fixture restoration remains in `finally`; the focused fixture deletes only its validated owned temporary directory.

The helper initializes exit as integer -1 and both flags as Boolean false; its only flag assignments are Boolean true, and normal exit is explicitly cast to integer. Its returned object includes every field. No wrapper/scanner catch turns an exception into a partial result. This source chain is why malformed-object fault injection is reported separately from reachable production statuses. OS containment has the narrower semantics already stated, independent of schema completeness.

Fresh evidence in `repair-audit-evidence`:

| Check | Actual result | Scope |
| --- | --- | --- |
| `focused-final-pwsh.receipt.json` | exit 0, 22.0243982 s wall, 120 s outer bound, no outer timeout/overflow | Unmodified committed focused script under pwsh 7.6.5; all exact 11 controls, intended real diagnostic, inner exit124/timeout=true/cleanup=true/overflow=false, actual consumer rejection, two-PID death assertion. |
| `boundary-pwsh.receipt.json` | exit 0, 3.1172925 s wall, 60 s bound | 52 actual-AST consumer calls: 26 each at old4ded and finalff92. All 19 well-formed final controls matched expected outcomes; seven malformed substitutions are observations, not falsely labelled rejection passes. |
| `process-evidence/run-01.receipt.json` | exit 0, 0.873517 s wall, 60 s bound | Independent raw-record checker, 148 assertions; exact 11 IDs/statuses/streams, shell invocations, source transfers and retained failures. |

`verdict_boundary_probe.ps1` saves the actual old/final consumer extents. The 19 well-formed cases include rejection exits 0/2/124, acceptance exits 1/2, absent/wrong-term diagnostics, required allowance and output-pattern witnesses, and timeout/cleanup/overflow failures for both verdict directions. `verdict-boundary-observations.json` retains every supplied record and actual result. The old consumer accepts the historical timeout combination; the new one rejects it. No predicate copy supplies the observed verdict.

Raw coordinator process records independently checked:

| Record | Source/fixture | Outer exit / elapsed / bound | Qualification |
| --- | --- | --- | --- |
| `process-posix.receipt.json` |143fa, five-second control | 1 / 45.615 s / 90 s | FAILED: real-case intended diagnostic missing; its control verdict alone is insufficient. |
| `process-posix-margin.receipt.json` | isolated143fa copy with fifteen-second margin | 0 / 55.792 s / 120 s | Valid separate timing experiment, not final-source qualification. |
| `process-final-pwsh.receipt.json` |ff92, pwsh executable | 0 / 24.411 s / 120 s | All 11 controls and real antecedent/death check pass. |
| `process-final-winps.receipt.json` |ff92, Windows PowerShell executable | 0 / 23.411 s / 120 s | All 11 controls and real antecedent/death check pass. |
| `process-final-posix.receipt.json` |ff92, WSL Ubuntu-24.04 pwsh | 0 / 44.879 s / 120 s | All 11 controls; real ownership is `setsid-process-group`; intended diagnostic and death check pass. |

Final records' real cases have inner Code124, TimedOut=true, Cleaned=true and OutputLimitExceeded=false, followed by actual production verdict failure and expected control success. Windows ownership is `kill-on-close-job`. The final marker follows executable assertions requiring exactly two recorded PIDs and zero surviving PIDs (`claim_drift_policy_process_regression.ps1:88–90`). Raw PID values and inner elapsed/deadline are not emitted by the committed test; its fixture is deleted in `finally`. The fifteen-second inner deadline is pinned by source, not an invented receipt field. Raw records pin HEAD/helper and streams but do not themselves supply every launch-time source hash/dirty snapshot. My fresh replay independently records clean initial/final source.

## Exact full-run registry and transfer

Independent source comparison preserves the complete fixture block, expected IDs, per-case term/path/witness mappings, expected verdict counts, context invocations, shadow construction and selector handling from4ded through143fa toff92. This includes fixture text and semantics, not merely counts. Empty default selection still means the full nonempty registry; unknown/nonunique selectors fail.

For both `policy-full-pwsh` and `policy-full-winps`, the inspector reconstructs expected verdicts from original source, then compares every raw process JSON record and immediately following verdict line in exact order. All134 policy cases (90 REJECT, 44 ACCEPT) and21 contexts are present once. Every production child has exit1 for source-expected rejection or exit0 for acceptance, TimedOut=false, Cleaned=true, OutputLimitExceeded=false and Windows job ownership. The 166 total records comprise 11 deliberate controls plus155 production cases. The nine displayed failure verdicts belong exactly to deliberate controls.

Both full-run receipts identify initial/final143fa, outer exit0/no timeout/no overflow and a1800-second deadline. Wall times are787.9693418 s (pwsh child) and662.8208957 s (Windows PowerShell child). Each raw stdout matches all405 receipt output lines; stderr is explicitly empty. A recording wrapper's `hostPowerShell=7.6.5` is not confused with the selected Windows PowerShell child executable. Full final-case/context/restoration assertions are present.

Production runner/verdict, scanner, policy JSON, consumed policy prose/frozen matrix and shared helper blobs are unchanged143fa→ff92. Key blobs: regression `f08e57240d977ee49de8d18eb2939694048793b6`; scanner `1967d707d3024672567d46f995bc893feae34521`; policy `147889ce5bd6ab6334734a8c7db27be7ec354943`; helper `71b2704e9b77af3b55d4b97c626207013938b5b0`. Full per-path hashes, per-ID maps and comparison results are retained in `registry-audit/RESULT.json` (SHA256 `94be2aee7ca63e37749e2dc2196765bfae809990dd41a735b8f56f88a8c3cb6c`). That independent inspection exited0 in2.5050588 s under a90-second bound; it did not rerun the full campaign.

The full driver also consumes the focused helper, which **does change** its synthetic deadline. Thus this is a transfer of the155 unchanged production case paths, coupled to separate final focused evidence; it is not a claim that every full-suite input is identical or that a fullff92 campaign was rerun. It does not repair missing per-child information in historical4ded logs. The coordinator's checker derived individual expectations from logs; this continuation strengthened that assessment with independently source-derived per-ID expectations.

## Workflow and unchanged formal evidence

At release workflow line19, `fetch-depth: 0` supplies historical commits consumed by the actual retrospective checker. `reproduce_artifact.sh:74–85` invokes the gate; `gate.ps1:271` invokes design regression, which resolves old commits and checks each immediate-parent range (`design_decision_check_regression.ps1:1041–1094`). No requirement is bypassed.

Release workflow line37 writes the running tee log to `$RUNNER_TEMP`, with its attachment-copy source adjusted at48. This matters because M1's actual clean-baseline consumer (`m1_certificate_mutation_regression.ps1:721–725`) checks untracked-inclusive repository status through the shared helper. The existing branch workflow already supplies the same full history/external-log inputs. The exact reproduction command and pipefail remain intact.

Release lines61–69 pass `--prerelease` for newly created hyphenated tags. Existing-release branches only upload and do not repair any pre-existing classification. Publication should inspect resulting metadata; no release was created here.

Fresh `workflow-audit/attempt3/receipt.json` retains30 commands and18 assertions, harness exit0 in5.333131 s, with40-second per-child bounds: four complete shell-block syntax parses, four actual publication-block stub cases (new/existing × hyphenated/plain), and exact reproduction-block fixtures propagating exits0 and7 while logging externally. These are shell-wiring tests, not artifact reproduction. Successful local shell testing used Git Bash5.2.37; hosted Ubuntu remains unrun. Two fresh strict design checks on4ded→143fa and143fa→ff92 each exit0 and classify three changed files as0 code/2 workflow/1 neutral. WDD entries at16370 and16395 match their respective changes. Their retained original receipts were also independently checked against raw streams and exact parent ranges.

Fresh final scans returned no matches for the mandated forbidden-proof/import and `native_decide|Lean\.ofReduceBool` patterns. Both committed-range and worktree `git diff --check` passed. `source-final-check.json` records exact commands, exits, source identity and original-report hash. The retained `build-repair-ff92` receipt/raw stdout agree on a successful cached `lake build` atff92 (exit0,17.132 s process time,1800 s bound); the ledger-only strict claim scan agrees on exit0,3.561 s,120 s bound and0 strict failures. These are inspected coordinator executions, not new cold builds. No proof/implementation source was edited during this audit, and unchanged formal/heavy campaigns were not repeated.

The original report's formal, trust-base, model-category, archive and historical-evidence limits remain applicable to their original objects. This tooling repair changes no theorem, axiom, packed payload construction, cost model, half-open/leftmost semantics or `List Int` reference layer. Earlier archive identities identify earlier archives; they do not certify replacementff92 packages.

## Affected inherited rows

| Inherited ID | Continuation disposition |
| --- | --- |
| REPLAY-SUBPROCESS-DEADLINE | P2-01 closed for the policy consumer onff92. Finite bounds, owned execution, completion predicate and real diagnostic-then-hang negative are supported; inherited containment/record limits remain explicit. Historical missing statuses remain unknown. |
| REPLAY-EXACT-REGISTRY | Supported: exact134+21 mappings and outcomes preserved, with actual155 completed-child records in each new full Windows run. Existing unrelated formal/EH/native registry assessments transfer only on unchanged inputs. |
| REPLAY-SELECTOR-NONVACUITY | Supported by unchanged selector source and the original assessment; new focused11-ID registry includes real antecedent/death checks. No new selector campaign is claimed. |
| INV-CATEGORY-SEPARATION | Supported unchanged: payload bits, proof fields, modeled ticks, machine operations and Lean/native timing remain separate. Tooling evidence is not mathematical strengthening. |
| V1-08 | SOURCE REPAIR SUPPORTED; DELIVERY/HOSTED FOLLOW-UPS PENDING. Local affected evidence is sufficient for this source verdict; no replacement artifact/hosted qualification is inferred. |
| V1-09 | CONTINUATION REPORT COMPLETE; PENDING COORDINATOR DISPOSITION. The original fresh audit remains immutable and this is its explicitly labelled correction loop. |

No wholesale re-adjudication of all85 original rows is claimed. Unaffected dispositions and limitations remain in the original report; this report changes only the affected source-finding assessment and records R6's bounded follow-up.

## Preserved failed attempts and evidence limits

Historical failures remain failures: original4ded P2-01; coordinator negative probe1 with unavailable Git identity; the five-second POSIX run without the diagnostic; isolated margin experimentation; earlier aggregate/chronology limits in the original report. Their existence is not erased by later successful controls.

Fresh audit-only unsuccessful attempts are also retained. Parent native `pwsh -File` argument-array invocation failed parameter binding before the probe; direct invocation then stopped at Git safe-directory identity failure (`parent-invocation-attempt1.json`, `parent-invocation-attempt2.json`, preserved wrapper). Subsequent identity queries used a per-command exception restricted to the explicitly requested checkout, with no persistent Git configuration change. The first final-source inspector completed identity/diff checks but failed to launch PATH-resolved rg; `source-check-attempt1` and `source-final.receipt.json` retain exit1/error. Resolving the installed rg executable explicitly produced the separate successful `source-final-attempt2` record. Workflow attempts failed first at Git ownership, then at WSL access; all files remain in `workflow-audit`, and successful checks explicitly used Git Bash. Preliminary path-discovery/read commands with absent files were exploratory, not passed qualifications.

The independent process and registry inspectors verify retained evidence; they are not re-executions of the historical full campaigns. Successful source/AST tests cannot establish future hosted execution, artifact byte identity, external protection state or publication metadata. Empty historical stderr streams and missing dirty-state/PID fields are described as such rather than manufactured.

## Coordinator follow-ups and proof digestion

The coordinator must disposition this continuation against exactff92 and preserve both reports; refresh final source/report checks and qualification records; build and verify replacement source/evidence ZIPs with exact included report/source identities; run the required hosted contexts through the PR; then decide protected merge and rc tagging. Preserve all failed/superseded receipts. Any subsequent source change needs an explicit applicability review; these results are not a blanket approval of later revisions. This ordering keeps evidence production ahead of its acceptance decision.

Conceptually, the repair connects the diagnostic claim to the process fact that makes it valid: the scanner must finish normally with the required exit. In plain English, printing the expected rejection and then hanging no longer passes the test. The release workflow supplies the history and clean tree already demanded by its checkers. All formal assumptions and theorem meanings remain unchanged. A skeptical graduate student should next ask whether the delivered archives contain exactly this source/report and whether the actual hosted jobs and release metadata satisfy the remaining contract; neither question is answered by these local tooling results.

**Status: CANDIDATE_COMPLETE for this continuation report only. Coordinator acceptance remains required.** Final report byte length and SHA256 are recorded in the separate `repair-audit-evidence/completion.json`, avoiding a self-referential report hash.
