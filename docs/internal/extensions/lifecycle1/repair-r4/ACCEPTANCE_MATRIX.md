# LIFE-1-R4 acceptance matrix: run_check verdict gap and residual failure-path findings

This matrix was created before any other edit in this branch. The requirement
rows above the append-only marker are frozen: they change only by an explicit
coordinator contract amendment. Evidence, dispositions and the command ledger are
appended below the marker. A row does not close by a script name, a green run or
this file; it closes only when the recorded evidence entails the exact requirement.

- Worker: LIFE-1-R4 (fresh governed repair task).
- Worktree: C:/Users/poin/Documents/RMQ/.claude/worktrees/life1-r4-run-check-verdict.
- Branch: claude/life-1-r4-run-check-verdict.
- Exact base: d27ffa341f4ed8ceccc46817455eb26c73b319a1 (LIFE-1-R3 tip). Lifecycle candidate eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a; formal base bf31f983205175481fcb659caa4dfb70ef43e361.
- Workflow governance: 7b227c49ef2ec044b702126cc41c9add847eed01 (skill preflight PASS, required rmq-proof-sprint).
- Template: docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md.
- Source prompt: LIFE1_R4_RUN_CHECK_VERDICT.md, 15,890 bytes, SHA-256
  40f77ac4bbcc0f777364d7e27bdbce67bf785144d94c60ef7e2dcf222374f9f8. The nine R4
  requirement texts below are copied byte-for-byte from its lines 37-45 (the text
  after `- <ID>: ` or `- <ID> (audit P...): `; the audit tag is kept in the Scope
  column), mechanically from those bytes.
- Finding source: LIFE1_R3_A1_FRESH_BLIND_DELTA.md, 34,798 bytes, SHA-256
  1ae0d97e819c7e323164f8507ab25fe9de2d069e08642d81360ab0226aedb48f.

## Inherited frozen rows (referenced, not restated)

Each inherited row is the complete requirement-table line of
`docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at commit
695a7e72eb8c85a21689681fb6981c86dabbf31d (18770 bytes, SHA-256 c1c228637584ca2aef195ecfce681d868eeb2620f7b7cf05a5ca43c6cf1d85bb).
Those rows in turn reference the formal and native frozen matrices at
eb8e4f25; none of these files may change on this branch. Every inherited row must be
re-established on the R4 tip.

| ID | Frozen source | Line | Row bytes | Row SHA-256 |
| --- | --- | --- | --- | --- |
| `L1-18` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 44 | 920 | `7a9cbd270d320b466711969f72a0fb37a59179ce628d66e2cb451f3cf2cca228` |
| `INV-MUTATION-REPRODUCIBILITY` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 45 | 961 | `809adbe76fb47dc3610f5a80304fbb793ac84f640be3738242849792b5223435` |
| `CHK-SCOPE` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 46 | 642 | `4680398ba17c3ede3c9fa4077aef9364d9143233bbfed2138d3fcec6fc882646` |
| `CHK-FINAL` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 47 | 541 | `e57f95c75be16417a90739c581fc13231934a44aa1e1e83f80cb6c231eec87d7` |
| `REPLAY-EXACT-REGISTRY` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 48 | 804 | `cd9ba6b6e26259701e85e6a845870190f921110922d679f66379eeb2747efa5f` |
| `REPLAY-SELECTOR-NONVACUITY` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 49 | 721 | `e4cca75922cc5b0a8664f92853e0c59220fb5a222be06945dad48c70749d8a2f` |
| `REPLAY-SUBPROCESS-DEADLINE` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 50 | 967 | `26afb275831142fa7f49c7cb67683620386f4541f0528a87fdb8907f6615ad5a` |
| `REQ-L1R3-PROPERTY` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 51 | 1723 | `743c3e26cb5273abf25ae0fa7b7d90a9b12ff9914ffcd7b49b27f2fdfa70823a` |
| `REQ-L1R3-HARNESSES` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 52 | 2272 | `846d8ad6689ec361c67ada4f80dcb44f31eec0f4976550eebf63cffb105114ec` |
| `REQ-L1R3-CONTROLS` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 53 | 1940 | `3b8da460f7e075565a33b40478f70c8b7f5c749f0dd789023c6d9cc09c5c8c6c` |
| `REQ-L1R3-CAMPAIGNS` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 54 | 1417 | `c3ebc6973729644731e17badb7c5c8d10d113bff460b7a58b85f6d8d9641d131` |
| `REQ-L1R3-PRESERVATION` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 55 | 1205 | `219cd76a3e31011ca640842d49f92e4c225b5ec49c1f12667af5c51ea3d9955b` |
| `CHK-L1R3-VERIFICATION` | `docs/internal/extensions/lifecycle1/repair-r3/ACCEPTANCE_MATRIX.md` at 695a7e72 | 56 | 958 | `dbc3206232559acc6380b916527e9ca92acf143bf62d8a95713c9353918ca702` |

The three REPLAY rows are also restated verbatim in the R4 prompt (line 46) and
govern every new runner of this branch (the R4 control registry, the auxiliary
controls and the base probe).

## Requirement-to-evidence matrix

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `L1-18` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 44 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `INV-MUTATION-REPRODUCIBILITY` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 45 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `CHK-SCOPE` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 46 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `CHK-FINAL` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 47 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REPLAY-EXACT-REGISTRY` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 48 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REPLAY-SELECTOR-NONVACUITY` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 49 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 50 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R3-PROPERTY` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 51 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R3-HARNESSES` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 52 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R3-CONTROLS` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 53 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R3-CAMPAIGNS` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 54 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R3-PRESERVATION` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 55 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `CHK-L1R3-VERIFICATION` | Inherited frozen row: repair-r3/ACCEPTANCE_MATRIX.md line 56 at 695a7e72 (bytes and SHA-256 above; not restated). | Inherited R3 row, re-established on the R4 tip | The R3 evidence obligation of that row, re-run through the final R4 harnesses and runners. | As recorded in the R3 row. | As recorded in the R3 row; a result from d27ffa34 or earlier does not re-establish the row. | See append-only evidence below. | Open |
| `REQ-L1R4-VERDICT` | In both run_check.ps1 files the durable finalization verdict is "fail" whenever the stage child fails, times out, exceeds its output limit or returns a malformed/unowned result, as well as on any stage error, integrity difference or cleanup error; the exit-code semantics stay as documented (child exit; 2 timeout/overflow; 3 integrity or cleanup; 1 harness exception). No harness in the lane may use the life1-r3-finalization-v1 verdict field with a narrower meaning; if any field is integrity-only it must be named so. Discriminating controls: "ordinary child failure, pins intact" for both run_check files, and a REAL harness-level deadline (a stage that outlives a short positive deadline through the owned helper, not a flipped flag) for at least one run_check file; each must fail at d27ffa34 and pass at the R4 tip. | Local owned rung (audit P2-1) | In both run_check.ps1 files `finalization.verdict` is `fail` whenever `childFailure` (child exit != 0, helper TimedOut or OutputLimitExceeded), a malformed/unowned helper result (raised as a stage error), a stage error, an integrity difference or a cleanup error is non-empty; exit mapping unchanged. Lane scan: every writer of `life1-r3-finalization-v1` uses `verdict` as the overall verdict. | run_check.ps1 -> Invoke-RMQOwnedBoundedProcess result -> childFailure/stageError -> $failed -> finalization.verdict -> result.json -> R4 runner core predicate `expect.verdict`. | Controls K1-F/K2-F (stage exits 7, pins intact) and K1-T/K2-T (stage sleeps 60 s under a real 3 s owned deadline; the helper result must carry TimedOut=true and DeadlineSeconds=3, never a flipped flag) must FAIL at d27ffa34 (verdict pass) and PASS at the R4 tip. | See append-only evidence below. | Open |
| `REQ-L1R4-DURABLE` | In all nine harnesses and in failure_controls.ps1 and heavy_run.ps1, a failure to write the durable result makes the run fail (nonzero exit, no PASS line, no PASS.json or equivalent success marker) while still reporting the first error; the validator must not write PASS.json unless RESULT.json was written. At least one control injects a durable-write failure and shows the base passing and the repair failing. | Local owned rung (audit P3-1) | Every listed durable write sits in a guard that, on failure, reports the write error on stderr and forces the run to failure: nonzero exit, no PASS line, no PASS.json/success marker; the first error is still reported. The validator writes PASS.json only after RESULT.json was written. | harness finally -> durable write guard -> failure flag -> post-finally exit/PASS gate. | Controls K1-W/K2-W/LV-W make the durable path an existing directory during the stage: the base must exit 0 (LV also writing PASS.json and printing its PASS line) and the repair must exit nonzero with the write-failure diagnostic, no durable file and no success marker; auxiliary HR-W does the same for heavy_run.ps1. | See append-only evidence below. | Open |
| `REQ-L1R4-COVERAGE` | (a) at least one control injects an exception inside cleanup/restoration (not the integrity step) for a harness with nontrivial cleanup, and the original stage error, the cleanup error and every integrity result are all recorded; (b) the S-shape predicate requires that every pin captured before the failure is re-verified (status verified/changed/unreadable-final, never silently absent), not merely that pinChecks is nonempty; (c) where a harness checks the existence of a PINNED file (for example the validator executable) before its evidence root exists, move that check after the root is created so a durable result records it; pure argument validation may stay before the root. A control exercises the validator's missing-executable path. | Local owned rung (audit P3-2, P3-3) | (a) a cleanup/restoration exception control with stage error, cleanup error and all integrity results recorded; (b) runner pin-coverage predicate: every captured pin (non-null entry) re-verified with status verified/changed/unreadable-final, captured count equal to entryPinCount and, for setup-failure shapes, to the registry-declared count captured before the failure; (c) pinned-file existence checks moved after the evidence root, pre-root inventory for the nine harnesses, LV missing-executable control. | R4 registry -> runner -> harness durable result pinChecks/entryPinCount -> pin-coverage predicate; IC per-case finally -> cleanupErrors -> RESULTS.json; LV try -> RESULT.json. | Synthetic predicate controls: a doc that silently drops one captured pin, a doc with a captured pin marked not-captured, and a count mismatch must all be rejected (the R3 `pinChecks.Count -gt 0` predicate accepts them); IC-U must show the cleanup error beside the stage error with all 7 pins verified; LV-E must fail at d27ffa34 (no RESULT.json) and pass at the tip. | See append-only evidence below. | Open |
| `REQ-L1R4-LABELS` | integrity_controls.ps1 and harness_stream_controls.ps1 label their entry pins as entry pins in the durable result (as run_controls and run_check do), so no top-level key presents an entry value as verified. Before renaming, find every live reader of those keys (at least scripts/packed_native_lifecycle_stream_check.ps1) and show it reads only retained keys; if a live reader needs a renamed key, stop and report rather than editing it. | Local owned rung (audit P3-5) | integrity_controls and harness_stream_controls durable results carry entry pins under entry* keys; no top-level key presents an entry value as verified; the retained old keys hold the post-run (final) pins they held at eb8e4f25; every live reader reads only retained keys. | Reader inventory (packed_native_lifecycle_stream_check.ps1, literal_selector_controls.ps1, historical verifiers) -> retained keys; harness finally final pins -> RESULTS.json. | Controls IC-L/HS-L change a labelled pinned file during the run: the tip must record entryX = entry pin and X = changed final pin (pinCheck status changed); d27ffa34 (top-level key carries the entry value, no entry* key) must fail. | See append-only evidence below. | Open |
| `REQ-L1R4-ORDER` | both run_check.ps1 files and run_controls.ps1's per-case mutex re-check integrity before releasing the mutex, as lifecycle_validator.ps1 does. | Local owned rung (audit P3-6) | In both run_check.ps1 finally blocks and in run_controls.ps1 per-case finally, every integrity recording precedes the first ReleaseMutex call. | AST of the exact Git blob -> finally block -> offsets of `$integrityErrors.Add` vs `ReleaseMutex`. | Static controls ORD-K1/ORD-K2/ORD-RC must fail on d27ffa34 blobs and pass on the tip; ORD-LV (the reference validator) must pass on both. | See append-only evidence below. | Open |
| `REQ-L1R4-OWNED-GIT` | the git calls R3 introduced in finalization (repair-r2 run_check.ps1 git rev-parse; harness_stream_controls.ps1 git status) run through scripts/owned_process_tree.ps1 with positive deadlines, exits and stderr preserved, and a failure recorded as an integrity or cleanup error, never a hang or a silent pass. | Local owned rung (audit P3-7) | The finalization git calls (repair-r2 run_check HEAD, harness_stream_controls carrier/fixture status) launch through Invoke-RMQOwnedBoundedProcess with positive deadlines; exit, stderr, timeout and overflow are recorded in the durable result; any failure is an integrity error. | harness finally -> owned git process record -> integrityErrors -> durable result. | K2-G: a git double that hangs after the stage; the tip must record an owned timeout as an integrity error and exit 3, the base must hang until the control deadline. HS-G: a git double that exits 128 with a stderr line; the tip must record exit and stderr in the integrity error, the base must not. | See append-only evidence below. | Open |
| `REQ-L1R4-CAMPAIGNS` | through the final R4 harnesses, re-run and commit receipts for the complete frozen 67-case registry on pwsh and 66 on winps via run_controls.ps1 invoked by repair-r2 run_check.ps1; the validator's standard modes (startup, single, full) on both shells; the normal full run of each lifecycle-native-p0 harness on pwsh (and on winps where the harness supports it; otherwise record uncovered). Report executed/expected counts, durations, exits and receipt hashes. A campaign not run is uncovered, never passed. | Local owned rung | Committed receipts with executed/expected counts, durations, exits and hashes for every listed campaign run through the final R4 harnesses; uncovered runs named as uncovered. | heavy_run.ps1 -> repair-r2 run_check.ps1 -> run_controls.ps1 / lifecycle_validator.ps1 / run_owned.ps1 / harness_stream_controls.ps1 -> durable results -> receipts. | A partial, timed-out or setup-failed campaign, or one run on harness bytes other than the final tip, is not recorded as passed; the frozen registry blobs stay unchanged. | See append-only evidence below. | Open |
| `REQ-L1R4-PRESERVATION` | git diff --name-status --no-renames d27ffa341f4ed8ceccc46817455eb26c73b319a1..HEAD lists only paths inside the write scope; zero diff under every protected path of REQ-L1R3-PRESERVATION and under repair-r3/receipts/**, repair-r3/REPORT.md and repair-r3/ACCEPTANCE_MATRIX.md; ledgers append-only; every changed file stored LF with no lone CR (git ls-files --eol plus a byte scan). | Local owned rung | Range diff only inside the write scope; protected paths and R3 evidence zero-diff; ledgers append-only; LF-only blobs. | git diff --name-status --no-renames d27ffa34..HEAD; git ls-files --eol; byte scan; prefix comparison. | One out-of-scope path, a CR byte, an R3 receipt change or a non-prefix ledger edit fails the row. | See append-only evidence below. | Open |
| `CHK-L1R4-VERIFICATION` | run and record (command, host, duration, deadline, mutex waits, exit): base reproductions; the complete control registry (all R3 controls plus the new ones) on pwsh 7 and Windows PowerShell 5.1 at the final tip, and base-mode runs of the new controls at d27ffa34; selector/registry controls; the REQ-L1R4-CAMPAIGNS runs; scripts/claim_drift_scan.ps1 -Strict and -SelfTest on the FINAL tip (never commit scanner result lines or its summary line; state counts in prose); git diff --check for the range and worktree; design_decision_check.ps1 -Strict per commit and once for the range from d27ffa34; both trust hygiene scans. | Verification | Every listed command recorded with command, host, duration, deadline, mutex waits and exit on the final content. | Append-only command ledger below. | A check that did not complete, or ran on a different tree, is not recorded as passed. | See append-only evidence below. | Open |

Explicitly deferred by the prompt (non-blocking for this rung, coordinator-owned):
audit P3-4 (historical evidence verifiers repair-r1/source_manifest.py,
repair-r1/collect_evidence.py and repair-r2/verify_evidence.py read pre-R3 key names;
not edited); integration with main; the audit of this pass; CI certification;
acceptance; scripts/gate.ps1.

<!-- LIFE-1-R4 APPEND-ONLY EVIDENCE BELOW THIS LINE -->

## E-00 Identities and startup

- Contract LIFE1_R4_RUN_CHECK_VERDICT.md: 15,890 B, SHA-256 40f77ac4bbcc0f777364d7e27bdbce67bf785144d94c60ef7e2dcf222374f9f8 (verified before work).
- Finding source LIFE1_R3_A1_FRESH_BLIND_DELTA.md: 34,798 B, SHA-256 1ae0d97e819c7e323164f8507ab25fe9de2d069e08642d81360ab0226aedb48f (verified).
- Initial HEAD d27ffa341f4ed8ceccc46817455eb26c73b319a1, `git status --porcelain` empty.
- `scripts/project_skill_preflight.ps1 -GovernanceRef 7b227c49ef2ec044b702126cc41c9add847eed01 -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-coordinator,rmq-proof-sprint,rmq-audit-prompt"`: SKILL-PREFLIGHT PASS, exit 0, 1.3 s.
- Frozen block of this matrix: every commit after ea7e11bf appends below the marker only.

## E-01 Base reproductions (unchanged base harness blobs)

| Finding | Reproduction | Base observation |
| --- | --- | --- |
| P2-1 | `base_probe.ps1 -HarnessRef d27ffa34 -Expect defect` (receipt `probe-base-d27ffa34`, 31 s) and v2 base controls K1-F/K2-F/K1-T/K2-T | r1 and r2 run_check: exit 7 with `verdict: "pass"` and `childFailure: "R?-CHECK: child exit 7"`; a 30 s stage under a real 3 s owned deadline: exit 2, `result.TimedOut = true`, `verdict: "pass"` |
| P3-1 | probe P31-K2-WRITE; controls K1-W/K2-W/LV-W at d27ffa34 | K2 durable write denied, exit 0; K1 exit 0; validator exit 0 with PASS.json and its PASS line although RESULT.json was not written |
| P3-2 | source (R3 runner L466-468) and aux PRED-PIN-* | the R3 predicate `pinChecks.Count -gt 0` accepts a dropped captured pin, a captured pin marked not-captured, a registry-count mismatch and a duplicate row (recorded as `r3PredicateAccepts: true`); no R3 control throws inside cleanup |
| P3-3 | probe P33-LV-EXE; control LV-E at d27ffa34 | validator without its executable exits 1 with no RESULT.json (throw before the log root) |
| P3-5 | controls IC-L/HS-L at d27ffa34 | IC `helper` and HS `source` hold the entry pin while pinChecks says `changed`; no entry* key |
| P3-6 | aux ORD-K1/ORD-K2/ORD-RC at d27ffa34 (receipt `aux-base-d27ffa34`) | each releasing finally releases the mutex before any `$integrityErrors.Add` (RC per-case finally: none at all); ORD-LV passes |
| P3-7 | control K2-G at d27ffa34 | the unowned final `git rev-parse` hangs with the git double until the 180 s control deadline kills the harness (no durable result) |

## E-02 Repair (commits 5fbc1c99, 25451ca4, d9411a7d; lines at d9411a7d)

- run_check r1: malformed/unowned helper result raised as a stage error L44-46; integrity loop before mutex release L70; `$failed` includes `childFailure` L76; durable-write failure forces exit 1 when it would be 0 L86, L92.
- run_check r2: `Get-R2OwnedHead` L36-49 (owned, 60 s, exit/streams kept in `finalization.gitProcesses`), entry L51, final L117; malformed guard L79-81; release after HEAD check L122; `$failed` L128; durable L140, L146.
- run_controls: per-case pin re-check before release L103-115 (`finalization.caseSlotChecks`); durable L146.
- finalizer_control L442, dependency_child L153, dependency_controls L125: durable-write failure fails the run.
- lifecycle_validator: identity capture, then the unchanged missing-executable diagnostic L110, then helpers; durable failure L178 fails the run and PASS.json (L190) is written only after RESULT.json.
- integrity_controls: `entrySource`/`entryHelper` = entry pins, `source`/`helper` = post-run pins L248-249; durable L254.
- harness_stream_controls: owned finalization git status L169 (`finalization.ownedRootStatus`); `entryRegistry`/`entrySource`/`entryValidator` and post-run `registry`/`source`/`validator` L209-212; durable L215.
- failure_controls.ps1 (runner), heavy_run.ps1 L60, selector_controls.ps1 L127: their own durable-write failure fails the run.
- Pre-root inventory (clause (c)): run_check r1/r2 (spec read, name/deadline validation), run_controls (runtime-profile argument check, frozen registry/component identity, selector), finalizer_control (shell resolution, registry read that validates -Case), dependency_child (spec read), harness_stream_controls (stream registry and selector validation), integrity_controls and dependency_controls (none): argument, selector or registry validation only; none launches or pins anything. The one pinned-file existence check before a root was the validator executable, now moved.
- Live readers of the IC/HS keys: packed_native_lifecycle_stream_check.ps1 (controls, fixtureRestoration, candidateUnchanged, installedToolsUnchanged, fixtureRestored), repair-r3/literal_selector_controls.ps1 (selected), the dormant lifecycle-native-p0 verifiers repair-r2/verify_results.py (`source`, `helper`, `registry`, `validator`) reused by repair-r3/verify_contract.py. All read only retained keys; the old keys keep their eb8e4f25 post-run meaning, so none needs editing.

## E-03 Control registry v2 and runner (d9411a7d)

- Registry `repair-r4/FAILURE_CONTROL_REGISTRY.json`, 48,252 B, normalized SHA-256 cf5ef090543773ef0a4fa473164e56633fabeef140301aad737bb2a7a3226dbc, 60 controls, base d27ffa34, generated by `make_registry.py` from the exact d27ffa34 v1 blob. The R3 v1 registry (normalized 500dd960...) is byte-identical and still the default.
- Base v2, both shells (receipts `controls-base-v2-pwsh` 663.1 s, `controls-base-v2-winps` 591.9 s): 60/60 predictions matched. The 47 R3 controls accept at d27ffa34. New controls at base: K1-F, K2-F exit 7 verdict pass (reject); K1-T, K2-T exit 2 verdict pass (reject); K1-W, K2-W exit 0, LV-W exit 0 with PASS.json (reject); IC-U accept (R3 already records the cleanup error, as predicted); LV-E no RESULT.json (reject); IC-L, HS-L entry value under the plain key (reject); K2-G timed out at the 180 s control deadline (timeout); HS-G git exit/stderr missing from the integrity error (reject).
- Candidate v2 at d9411a7d (receipts `controls-candidate-v2-pwsh` 557.8 s, `controls-candidate-v2-winps` 486.9 s): 60/60 PASS on each shell (core and structural predicates). New controls: K1-F/K2-F exit 7 verdict fail; K1-T/K2-T exit 2 verdict fail with the helper's TimedOut=true, DeadlineSeconds=3; K1-W/K2-W/LV-W exit 1, no durable file, no PASS.json or PASS line, write diagnostic on stderr; IC-U stage error plus two cleanup errors (untracked restoration, fixture snapshot) with 7/7 pins verified and the tree unchanged; LV-E RESULT.json with the unchanged diagnostic and 11 of 12 pins re-verified; IC-L/HS-L entry pins only under entry* keys and the plain key equal to the changed post-run pin; K2-G exit 3 with `final HEAD unavailable: git rev-parse timed out after 60 s`; HS-G integrity errors carrying `git exit 128` and the double's stderr line.
- v1 replay at d9411a7d (`controls-candidate-v1-pwsh`, 380.0 s): 47/47 PASS.
- Every control restored and verified its disposable copy (`restoration.verified`, `gitClean`), and each run's real worktree Git state was equal before and after.
- Selector/registry controls: `selector-v1` 15/15 and `selector-v2` 15/15 (omitted, valid, empty string, empty array, whitespace, malformed, unknown, duplicate selectors; exact copy, missing, duplicate, unknown and reordered middle IDs, byte drift, empty registry), no runner evidence created on any rejection.
- Auxiliary controls (`aux-base-d27ffa34` 7.8 s, `aux-candidate-9a21a547` 9.8 s): 17/17 each. Tip: every releasing finally records integrity before release (ORD-K1/K2/RC/LV); HR-W exits 1 without a success line; the eleven synthetic predicate cases match verdict and exact reason. The attempt-1 receipts record a fixture defect (a `[string]` parameter coerced null to '') found and fixed in 9a21a547; the pinned predicate was not changed.
- Probe at d9411a7d (`probe-candidate-d9411a7d`, 35.3 s): 6/6 in the repaired shape.

## E-04 Campaigns (head 2802b84d; harness and runner blobs equal d9411a7d)

Receipts `campaign-r4-*` and `campaign-summary/CAMPAIGN_SUMMARY.json`. Every run_check finalization pass, 17/17 pins verified; global-mutex waits at most 0.006 s; no timeout or overflow.

| Campaign | Executed / expected | Child exit | Child seconds |
| --- | --- | --- | --- |
| frozen registry, pwsh | 67/67 in frozen order; registry 385c9bc9...; summary 12/12 pins; 67 per-case slot checks verified | 0 | 273.4 |
| frozen registry, winps | 66/66 in frozen order; 66 per-case slot checks verified | 0 | 204.5 |
| validator startup / single / full, pwsh | PASS, 2 / 3 / 9 processes, 12/12 identity pins, PASS.json | 0 | 5.4 / 8.2 / 47.1 |
| validator startup / single / full, winps | same | 0 | 4.1 / 6.7 / 44.5 |
| p0 integrity, pwsh / winps | 15 controls, verdict pass, 7/7 pins, fixtureRestoration and candidateUnchanged true | 0 | 273.5 / 170.8 |
| p0 dependencies, pwsh / winps | 19 controls, verdict pass, 13/13 pins, installedToolsUnchanged and fixtureRestored true | 0 | 20.0 / 14.0 |
| p0 harness-stream, pwsh / winps | 11 controls, verdict pass, 9/9 pins, 12/12 owned git status checks verified | 0 | 121.7 / 94.4 |

The three LF-pinned frozen inputs were materialized as exact blob bytes before the queue and restored after it (content proof by empty `git diff`; clean status after restore).

## E-05 Preservation and checks at 8ec10ec2

- `git diff --name-status --no-renames d27ffa34..8ec10ec2`: 808 entries (16 M, 792 A), none outside the write scope. M: the nine harnesses, the three R3 runners, three R3 doubles, the ledger. The R3 v1 registry, R3 receipts, R3 REPORT.md and ACCEPTANCE_MATRIX.md, materialize_registries.py, the P3-4 historical verifiers, DESIGN_DECISIONS.md and every REQ-L1R3-PRESERVATION path: zero diff.
- Ledger: the d27ffa34 blob (973,117 B) is a byte prefix of the 8ec10ec2 blob (991,675 B).
- `git ls-files --eol` over changed paths: 744 i/lf, 64 i/none (empty receipts); byte scan of 808 changed blobs: 0 CR.
- `git diff --check d27ffa34..8ec10ec2` and `git diff --check`: exit 0.
- `design_decision_check.ps1 -Strict -Base <parent> -Head <commit>` for all eight commits ea7e11bf..8ec10ec2 and for the range: pass.
- Hygiene: both rg scans over RMQ and lakefile.toml: no matches.
- `git diff d9411a7d..8ec10ec2` over every harness, runner, double, predicate and registry file: empty.

## E-06 Command ledger (host POINPAD; runner shell pwsh 7.6.5 unless noted)

| Command | Role | Deadline | Mutex wait | Duration | Exit |
| --- | --- | --- | --- | --- | --- |
| lake build rmq_lifecycle_validate (heavy_run, global+lane) | prerequisite (cold worktree) | 14,400 s | 0.004 s | 1,356.6 s | 0 |
| base_probe -Expect defect @ d27ffa34 | base reproduction | 120 s per case | none (short) | 31.2 s | 0 |
| base_probe -Expect repaired @ 5fbc1c99 / 25451ca4 | development loop | 120 s per case | none | 40.7 / 35.2 s | 1 (caught the validator ordering) / 0 |
| failure_controls -HarnessRef worktree, 13 R4 controls | development loop | 1,800 s | 0.003 s | 188.4 s | 0 |
| failure_controls v2 base pwsh / winps | final-required | 5,400 s | 0.004 / 0.004 s | 663.1 / 591.9 s | 0 / 0 |
| failure_controls v2 candidate pwsh / winps @ d9411a7d | final-required | 5,400 s | 0.009 / 0.006 s | 557.8 / 486.9 s | 0 / 0 |
| failure_controls v1 candidate pwsh @ d9411a7d | replayability | 5,400 s | 0.003 s | 380.0 s | 0 |
| selector_controls v1 / v2 | final-required | 1,800 s | 0.004 / 0.003 s | 19.6 / 19.4 s | 0 / 0 |
| aux_controls base / candidate (attempt 1) | superseded | 900 s | 0.004 s | 10.4 / 10.5 s | 0 / 1 (fixture defect) |
| aux_controls base @ d27ffa34 / candidate @ 9a21a547 | final-required | 900 s | 0.004 / 0.003 s | 7.8 / 9.8 s | 0 / 0 |
| base_probe -Expect repaired @ d9411a7d | final-required | 900 s | 0.004 s | 35.3 s | 0 |
| materialize_registries.py / --restore | campaign prerequisite | 60 s per git call | - | <2 s | 0 / 0 |
| 14 campaigns (E-04) through heavy_run + repair-r2 run_check | final-required | per E-04 | <= 0.006 s | E-04 | all 0 |

Claim-drift `-Strict` and `-SelfTest` must run on the final tip, which includes this appendix; they are run after this commit on that exact tip and their counts are given in the worker report (never scanner lines).

## E-07 Row dispositions (worker; coordinator acceptance pending)

| ID | Disposition | Evidence |
| --- | --- | --- |
| `REQ-L1R4-VERDICT` | Met | E-01, E-02, E-03: K1-F/K2-F/K1-T/K2-T fail at d27ffa34 and pass at the tip on both shells; the T controls use a real owned 3 s deadline on a 60 s stage (helper TimedOut, terminated IDs), never a flipped flag; lane scan: every writer of `life1-r3-finalization-v1` (nine harnesses, runner, selector controls, probe, aux) uses `verdict` as the overall verdict. |
| `REQ-L1R4-DURABLE` | Met | E-02; K1-W, K2-W, LV-W and HR-W exit 0 (LV with PASS.json and PASS line, HR with its success line) at the base and exit nonzero with no durable file and no success marker at the tip, reporting the write error. The runner and selector controls are source-evident (their result path cannot be obstructed without a runner-level fixture). |
| `REQ-L1R4-COVERAGE` | Met | (a) IC-U; (b) Test-R4PinCoverage in every structural evaluation (60 and 47 controls), exact S counts, PRED-PIN-* rejecting the four mutations the R3 predicate accepts; (c) E-02 pre-root inventory and LV-E. |
| `REQ-L1R4-LABELS` | Met | E-02 reader inventory; IC-L and HS-L fail at the base and pass at the tip; PRED-LABEL-*; campaign RESULTS carry entry* keys equal to the post-run keys on intact runs. |
| `REQ-L1R4-ORDER` | Met | ORD-K1/K2/RC fail at d27ffa34 and pass at the tip; ORD-LV passes at both; campaigns record 67 and 66 per-case slot checks. A behavioural race control would contend for the live lane mutex (recorded in WDD-05). |
| `REQ-L1R4-OWNED-GIT` | Met | E-02; K2-G times out under the owned 60 s deadline (exit 3, integrity error) where the base hangs; HS-G records git exit 128 and stderr where the base does not. |
| `REQ-L1R4-CAMPAIGNS` | Met | E-04; the p0 harnesses also run on winps. |
| `REQ-L1R4-PRESERVATION` | Met at 8ec10ec2; to be rechecked on the final tip | E-05. |
| `CHK-L1R4-VERIFICATION` | Met except the final-tip claim-drift runs, which follow this commit | E-06, E-05. |
| `L1-18` (failure-path sub-clause) | Re-established | E-04 frozen 67/66 through the R4 run_controls launched by the R4 repair-r2 run_check; RC-* at the tip on both shells. |
| `INV-MUTATION-REPRODUCIBILITY` | Re-established | v2 60/60 and v1 47/47 replays with restoration and clean copy/worktree state; synthetic predicate controls with pinned reasons. |
| `CHK-SCOPE` | Re-established | E-05 (scope against the R4 write scope). |
| `CHK-FINAL` | Re-established except the final-tip claim-drift runs | E-05, E-06. |
| `REPLAY-EXACT-REGISTRY` | Re-established | the runner rejects empty, duplicate, missing, unknown and reordered IDs and pinned-byte drift for v1 and v2 (REG-09..15 twice) and reports executed/expected; the probe and aux runners have exact rosters. |
| `REPLAY-SELECTOR-NONVACUITY` | Re-established | SEL-01..08 for v1 and v2; the probe and aux runners take no selector. |
| `REPLAY-SUBPROCESS-DEADLINE` | Re-established | every control, campaign, probe and aux launch and every finalization git call runs through the unchanged owned helper with a positive deadline; exits and streams are retained; restoration verified. |
| `REQ-L1R3-PROPERTY` | Re-established, now including clause (e) for run_check | E-03 all P/C/Q/S/M/X/R controls plus the R4 shapes at the tip on both shells. |
| `REQ-L1R3-HARNESSES` | Re-established | the nine harnesses remain repaired; the R4 changes are control-flow, finalization and result-key only. |
| `REQ-L1R3-CONTROLS` | Re-established | the 47 R3 controls pass at the tip on both shells (v2 and v1); their eb8e4f25 base receipts are unchanged. |
| `REQ-L1R3-CAMPAIGNS` | Re-established | E-04. |
| `REQ-L1R3-PRESERVATION` | Re-established | E-05. |
| `CHK-L1R3-VERIFICATION` | Re-established except the final-tip claim-drift runs | E-05, E-06. |
