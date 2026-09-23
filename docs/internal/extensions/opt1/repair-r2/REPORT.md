Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# OPT-1-R2 worker report: claim-scan evidence receipts

- Handle and title: OPT-1-R2, `(OPT-1-R2) Repair compiler claim-scan evidence receipts`.
- Branch `codex/opt-1-r2-claim-receipts`; worktree `C:/Users/poin/Documents/RMQ/.claude/worktrees/opt1-r2-claim-receipts`.
- Base `4cc95012a31cda9459d06d87b3371c8c172bb973` (OPT-1-R1 final head); original mathematical candidate `aecf4a580c591e8f694a3699e19e843198089194`; proof base and workflow-governance ref `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Skill preflight PASS (required `rmq-proof-sprint`; runtime `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`).
- Governing prompt `OPT1_R2_CLAIM_RECEIPTS.md`, 15,923 bytes, SHA-256 `09E40892CD88E0B39C1AC7EC3F5B942E4C4C1873AEA4C7BEFEC1245D002CED41`.
- Commits: `55f0f64fc03e7c5a3ca2a30271174d67b3a1f2ad` freezes the R2 acceptance matrix and records WDD-20260913-OPT1-R2-001; `3b8296767f93cd11fed7eb6a257ce94683430228` is the repaired commit (archives, manifest, verifier, controls, preservation tooling, attributes). The branch tip adds only this report, the matrix evidence appendix, the curated receipts under `repair-r2/receipts/`, their attribute lines and a WDD verification note. A file cannot contain the hash of the commit that adds it, so the tip SHA is given in the submission message.
- Request: run the coordinator aggregate gate on the exact branch tip, and disposition the independent audit of the repaired candidate. The tip's scanned content differs from `3b82967` only by the report-commit files listed below. This worker has not run `scripts/gate.ps1` or the full default `lake build`, and claims no gate result, acceptance or integration.

Quoting convention: scanner text quoted in this report writes `(` as `&#40;` and `[` as `&#91;` (and `|` as `&#124;`). Rendered, it is exact; the file's bytes contain neither the scanner's result-line prefix nor its scan-complete summary shape, so this report is not a new claim surface.

## What changed

Two OPT-1 receipts stored an earlier focused claim scan's complete stdout as one JSON string on one physical line, including that scan's own scan-complete summary. The unchanged default-root scanner prints those receipt lines as review hits, and prints them before its real summary. The unchanged self-test reads each child run's hit count from the first line anywhere in the output that has the summary shape, so it read the embedded count from a receipt in both runs and reported that the process-record exclusion removed nothing. Each of the two receipts is now a gzip archive at its original path plus `.gz` that decompresses to the exact Git blob bytes at the base. The scanner, its self-test, the policy, globs, allowlists and exclusions are unchanged, and so is every Lean source, script, profile, registry, pin and production-consumed receipt. The self-test and the strict default-root scan now pass on the repaired commit. A committed manifest, verifier and 20-case control runner recompute the recovery from Git objects, and two committed preservation demonstrations show that the change is exactly the relocation the coordinator admitted.

## Changed paths

`git diff --no-renames --name-status 4cc95012a31cda9459d06d87b3371c8c172bb973..3b8296767f93cd11fed7eb6a257ce94683430228`:

- `M` `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `M` `docs/internal/extensions/opt1/.gitattributes`
- `D` `docs/internal/extensions/opt1/checkpoint-claims.json`
- `A` `docs/internal/extensions/opt1/checkpoint-claims.json.gz`
- `D` `docs/internal/extensions/opt1/checkpoint-report-claims.json`
- `A` `docs/internal/extensions/opt1/checkpoint-report-claims.json.gz`
- `A` `docs/internal/extensions/opt1/repair-r2/.gitattributes`
- `A` `docs/internal/extensions/opt1/repair-r2/ACCEPTANCE_MATRIX.md`
- `A` `docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json`
- `A` `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.ps1`
- `A` `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.py`
- `A` `docs/internal/extensions/opt1/repair-r2/preservation/relocation_controls.json`
- `A` `docs/internal/extensions/opt1/repair-r2/receipt_archive_control_helper.py`
- `A` `docs/internal/extensions/opt1/repair-r2/receipt_archive_controls.json`
- `A` `docs/internal/extensions/opt1/repair-r2/run_receipt_archive_controls.ps1`
- `A` `docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py`

The report commit adds `docs/internal/extensions/opt1/repair-r2/REPORT.md`, `docs/internal/extensions/opt1/repair-r2/receipts/scan-base-4cc9501.json`, `docs/internal/extensions/opt1/repair-r2/receipts/scan-repaired-3b82967.json`, `docs/internal/extensions/opt1/repair-r2/receipts/controls-3b82967.json`, `docs/internal/extensions/opt1/repair-r2/receipts/preservation-3b82967.json`, `docs/internal/extensions/opt1/repair-r2/receipts/checks-3b82967.json`; it appends to `docs/internal/extensions/opt1/repair-r2/ACCEPTANCE_MATRIX.md (evidence appendix after the frozen rows)`, `docs/internal/extensions/opt1/repair-r2/.gitattributes (serialization lines for the new files)`, `docs/internal/WORKFLOW_DESIGN_DECISIONS.md (verification note)`. `docs/internal/DESIGN_DECISIONS.md` is unchanged: the strict design check classifies every changed path as workflow or neutral, no Lean, public-claim or repository-code path changed, and the decision is a workflow decision recorded in `WORKFLOW_DESIGN_DECISIONS.md`.

Out-of-scope follow-ups from the fresh audit of `4cc9501` were not touched: `docs/internal/extensions/opt1/repair-r1/profile/SOURCE_PROFILE.json` (mislabelled GitBlobSHA1/RawGitSHA256 fields) and `scripts/packed_optimized_runtime.ps1` (culture-sensitive string comparison) are byte-identical at the branch tip; neither appears in the changed-path lists above, and the relocation-aware run's amendment identity covers the former.

## Reproduced failure and mechanism on the unchanged base

The unchanged scanner ran on the clean worktree at `4cc95012a31cda9459d06d87b3371c8c172bb973` (status empty before and after; no ignored files under the scan roots), under pwsh 7.6.6 inside `Global\RMQHeavyVerification`, from host `POINPAD` (Microsoft Windows NT 10.0.26200.0). Scanner SHA-256 `5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7`; policy SHA-256 `4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9`.

| Command | Exit | Duration (s) | Deadline (s) | Summary-shaped output lines | Summary lines |
| --- | --- | --- | --- | --- | --- |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | 1 | 297.532 | 10800 | 0 | CLAIM-DRIFT SELFTEST: ok -- 6 protected probes rejected and 2 attributed probes accepted<br>CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path<br>CLAIM-DRIFT SELFTEST: FAIL -- exclusion removed nothing &#40;136 hits with records, 136 without); a filter that matches nothing looks identical to one that works<br>CLAIM-DRIFT SELFTEST: RESULT: FAIL |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 0 | 171.054 | 5400 | 26 | CLAIM-DRIFT: scan complete &#40;1831 hits, 0 strict failures) |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords` | 0 | 157.787 | 5400 | 26 | CLAIM-DRIFT: scan complete &#40;2262 hits, 0 strict failures) |

The self-test printed CLAIM-DRIFT SELFTEST: FAIL -- exclusion removed nothing &#40;136 hits with records, 136 without); a filter that matches nothing looks identical to one that works. The two standalone runs report the true totals 1831 (without records) and 2262 (with records), so the exclusion does remove hits and the self-test measured something else.

Mechanism. `scripts/claim_drift_scan.ps1` lines 139-145 (`Get-ReportedHitCount`) return the count from the first line anywhere in a child run's output that matches its summary-shape regex; they do not anchor to the scanner's own final summary line (line 478). Two receipts hold that shape inside one JSON string each:

- `docs/internal/extensions/opt1/checkpoint-claims.json:15`, a 77,764-byte physical line beginning `"Stdout": "`, embeds at byte columns 77,705-77,760 the text CLAIM-DRIFT: scan complete &#40;457 hits, 0 strict failures), preceded on the same line by 327 embedded result lines of an earlier focused scan;
- `docs/internal/extensions/opt1/checkpoint-report-claims.json:14`, a 20,271-byte physical line, embeds at byte columns 20,212-20,267 the text CLAIM-DRIFT: scan complete &#40;136 hits, 0 strict failures), preceded by 83 embedded result lines.

Review-only terms with no allowances (for example `role-scoped-2pow128`, `all-size-196727` and `invalid-range-rejection`) match text inside those lines, so the scanner emits each whole line as a review hit, of the form CLAIM-DRIFT&#91;role-scoped-2pow128]&#91;explicit-compatibility-premise-or-proof-only-sparse-witness-never-canonical-activation]&#91;review] docs\internal\extensions\opt1\checkpoint-claims.json:15: "Stdout": "CLAIM-DRIFT&#91;role-scoped-2pow128]... (77 KB) ...CLAIM-DRIFT: scan complete &#40;457 hits, 0 strict failures)\n". The first policy term that matches them precedes the scanner's final summary by more than a thousand output lines.

In this session's standalone runs each output has 26 summary-shaped lines: 25 embedded receipt lines and the real final summary. Without records, the first is output line 47 from `docs/internal/extensions/opt1/checkpoint-report-claims.json:14` (term `role-scoped-2pow128`, embedded count 136). With records, the first is output line 44 from `docs/internal/extensions/opt1/checkpoint-claims.json:15` (term `role-scoped-2pow128`, embedded count 457). The self-test's two child runs both emitted the 136 line first, so it compared 136 with 136 and failed. The aggregate gate and the coordinator's reproduction both read 457 twice. The quoted gate line differs from this reproduction only in which receipt ripgrep's multithreaded emission put first. The ordering seen in these standalone runs (136 without records, 457 with records) would have made the self-test report a spurious positive exclusion and pass on the defective tree.

Mutex: this session waited 15807.84 s (acquired 2026-09-13T20:12:29.8967864Z) and held the mutex from the base reproduction through the repaired-commit scans. No scanner, pwsh or rg descendant of the driver survived any run (the post-run sweep found none).

## Archive inventory

Recomputed from all 830 Git blobs under `docs/internal/extensions/opt1/` at the base (the manifest is `docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json`; the verifier recomputes every value).

| Original (`docs/internal/extensions/opt1/`) | Result lines (embedded / physical) | Base blob id | Mode | Blob SHA-256 | Blob bytes | Archive SHA-256 | Archive bytes | Decompressed bytes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `checkpoint-claims.json` | 327 / 1 | `25a2026b26c792e42e90a53a6594e0c5c2fd52d9` | 100644 | `4073391ECBF3EE6C16301851F0F3F392C5ACF0E0E16BDD64F2B8CE68EE3DF24F` | 78,583 | `08167E54224598F390183A4EE2038ED8A69BB2E72CD52C5B3BB8506474C9C141` | 11,761 | 78,583 |
| `checkpoint-report-claims.json` | 83 / 1 | `eb59b5d20aed5491fb66c51e64e9a873ed043823` | 100644 | `71669AACBD57F32955738682AB135444DAD065594090BB89672DB30F59C3B5AB` | 20,740 | `718E2FA06AB7547546D5647B0A02536C11ABC81FD0A916DB2F6DC890754BFC41` | 3,724 | 20,740 |

Encoding: gzip (RFC 1952), one deflate member, FLG 0, MTIME 0, XFL 2, OS 255; writer Python gzip.compress(data, compresslevel=9, mtime=0) over git cat-file blob bytes. Appended attribute lines in `docs/internal/extensions/opt1/.gitattributes`: `# OPT-1-R2: exact gzip archives of receipts that embedded claim-scanner result lines.`; `/checkpoint-claims.json.gz binary`; `/checkpoint-report-claims.json.gz binary`.

Files that mention scanner text (the scanner name or a quoted summary) without any result line stay byte-identical, as required: `certificate-freeze-claims.json`, `certificate-refreeze-claims.json`, `final-report-claim-check.ps1`, `final-report-claims.json`, `freeze-claims-pass.json`, `freeze-claims.json`, `import-repair-refreeze-claims.json`, `repair-r1/final/claim-scan-a/RESULT.json`, `repair-r1/final/claim-scan-b/RESULT.json`, `repair-r1/final/claim-scan-c/RESULT.json`, `repair-r1/final/claim-scan-d/RESULT.json`.

Every file that refers to an original name at the base (not rewritten; the manifest resolves them):

- `docs/internal/extensions/opt1/RESOURCE_WAIT_20260912_REPORT.md` (checkpoint-claims.json)
- `docs/internal/extensions/opt1/checkpoint-verification.json` (checkpoint-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/git/git-005.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/git/git-011.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/git/git-017.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/git/git-018.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c1/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c2/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c2/git/git-005.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c2/git/git-008.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c2/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/git/git-005.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/git/git-011.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/git/git-017.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/git/git-018.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/final/preservation-c4/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-01/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-01/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-02/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-02/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-03/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-03/git/git-005.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-03/git/git-011.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-03/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-04/git/git-004.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-04/git/git-005.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-04/git/git-011.stdout.bin` (checkpoint-claims.json, checkpoint-report-claims.json)
- `docs/internal/extensions/opt1/repair-r1/preservation/selftest-04/result.json` (checkpoint-claims.json, checkpoint-report-claims.json)

## Verifier and controls

- `python.exe -B docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py`: exit 0, 2.379 s (deadline 900 s). RECEIPT-ARCHIVES: RESULT: PASS &#40;2 of 2 required archives verified; 2 manifest entries; 0 extra archives; 11 unselected scanner-text files present; base 4cc95012a31cda9459d06d87b3371c8c172bb973)
- `python.exe -B docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py --committed 3b8296767f93cd11fed7eb6a257ce94683430228`: exit 0, 2.81 s (deadline 900 s). RECEIPT-ARCHIVES: RESULT: PASS &#40;2 of 2 required archives verified; 2 manifest entries; 0 extra archives; 11 unselected scanner-text files present; base 4cc95012a31cda9459d06d87b3371c8c172bb973)

`run_receipt_archive_controls.ps1` ran the full registry `OPT1-R2-RECEIPT-ARCHIVE-CONTROLS-V1` on the committed repaired tree (HEAD `3b8296767f93cd11fed7eb6a257ce94683430228`) under Windows PowerShell 5.1.26100.9444 (`C:\WINDOWS\System32\WindowsPowerShell\v1.0\powershell.exe`, packaged host False), Python `C:\Python314\python.exe`: result PASS, executed 20 of 20 selected of 20 registered cases; work root removed True. Total runner duration 215.744 s.

| Case | Kind | Contract requirement | Verdict | Exit | Failure codes or observation | Deadline (s) | Case seconds | Copy removed | Repository state unchanged |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `positive-tree` | verify-tree | positive | PASS | 0 | none | 900 | 4.771 | True | True |
| `positive-committed` | verify-committed | positive | PASS | 0 | none | 900 | 7.242 | True | True |
| `positive-copy` | verify-copy | positive on an unmutated disposable copy | PASS | 0 | none | 900 | 12.185 | True | True |
| `changed-archive-header-byte` | verify-copy | changed archive byte | PASS | 1 | archive-gzip-invalid, archive-sha256-mismatch | 900 | 10.942 | True | True |
| `changed-archive-trailer-byte` | verify-copy | changed archive byte | PASS | 1 | archive-gzip-invalid, archive-sha256-mismatch | 900 | 11.774 | True | True |
| `missing-archive` | verify-copy | missing archive | PASS | 1 | archive-missing | 900 | 10.324 | True | True |
| `extra-archive` | verify-copy | extra archive not in the manifest | PASS | 1 | archive-extra | 900 | 14.082 | True | True |
| `duplicate-manifest-entry` | verify-copy | duplicated manifest entry | PASS | 1 | manifest-duplicate-entry | 900 | 11.964 | True | True |
| `wrong-base-blob-id` | verify-copy | wrong base blob id | PASS | 1 | base-blob-id-mismatch | 900 | 12.701 | True | True |
| `decompressed-byte-mismatch` | verify-copy | decompressed-byte mismatch | PASS | 1 | decompressed-bytes-mismatch | 900 | 13.14 | True | True |
| `original-restored` | verify-copy | original file restored beside its archive | PASS | 1 | original-present | 900 | 9.158 | True | True |
| `manifest-entry-removed` | verify-copy | missing manifest entry &#40;additional) | PASS | 1 | archive-extra, attributes-manifest-mismatch, manifest-missing-entry | 900 | 9.038 | True | True |
| `new-result-line-file` | verify-copy | reintroduced result-line file &#40;additional) | PASS | 1 | new-result-line-file | 900 | 12.866 | True | True |
| `deadline-descendant-cleanup` | deadline | REPLAY-SUBPROCESS-DEADLINE | PASS | -1 | timed out True; root and child pids [29752, 12460]; alive after [] | 5 | 12.727 | True | True |
| `selector-valid` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 0 | argument positive-tree; executed [positive-tree] | 1800 | 22.436 | True | True |
| `selector-empty` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 2 | argument ''; executed [] | 1800 | 7.154 | True | True |
| `selector-whitespace` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 2 | argument ' '; executed [] | 1800 | 7.23 | True | True |
| `selector-malformed` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 2 | argument 'Positive Tree!'; executed [] | 1800 | 8.185 | True | True |
| `selector-unknown` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 2 | argument no-such-case; executed [] | 1800 | 8.626 | True | True |
| `selector-duplicate` | selector | REPLAY-SELECTOR-NONVACUITY | PASS | 2 | argument positive-tree,positive-tree; executed [] | 1800 | 7.729 | True | True |

Every negative ran on a disposable copy of `docs/internal/extensions/opt1/` outside the repository and produced exactly its pinned failure-code set. The contract's positive and seven negatives map to `positive-tree`, `positive-committed` and `positive-copy`; `changed-archive-header-byte` and `changed-archive-trailer-byte`; `missing-archive`; `extra-archive`; `duplicate-manifest-entry`; `wrong-base-blob-id`; `decompressed-byte-mismatch` (a well-formed archive whose manifest digests were updated to match, so only the decompressed content differs); and `original-restored`. `manifest-entry-removed`, `new-result-line-file`, the deadline case and the six selector cases are additional. Development history: a first full rehearsal in a disposable clone failed `selector-malformed` on its restoration check alone, because this worker was writing new files into that clone while the case ran; the check detected a real repository change and the case failed closed. The clean rehearsal and this run passed 20 of 20.

## Preservation demonstrations

`docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.ps1 -CandidateRef 3b8296767f93cd11fed7eb6a257ce94683430228 -FreezeRef 55f0f64fc03e7c5a3ca2a30271174d67b3a1f2ad` ran under Windows PowerShell 5.1.26100.9444 with a 900 s deadline per stage; every stage ran through the owned supervisor. All three stages gave their expected verdicts: True.

| Stage | Verdict | Expected | Exit | Seconds | Status | Failure code |
| --- | --- | --- | --- | --- | --- | --- |
| `unchanged-r1` | EXPECTED_FAILURE | exit 1, status FAIL, code LIVE_PROTECTED_MISSING on docs/internal/extensions/opt1/checkpoint-claims.json | 1 | 4.037 | FAIL | LIVE_PROTECTED_MISSING |
| `controlled-difference` | EXPECTED_CONTROLLED_DIFFERENCE | exit 0, status EXPECTED_CONTROLLED_DIFFERENCE | 0 | 4.74 | EXPECTED_CONTROLLED_DIFFERENCE |  |
| `relocated` | PASS | exit 0, status PASS | 0 | 8.351 | PASS |  |

### (a) Unchanged OPT-1-R1 checker: expected controlled difference, never credited as a pass

The byte-identical wrapper `repair-r1/preservation/check.ps1` and checker `check.py` (SHA-256 `AB47AF51D7074C00B1A3A8C73CA5321EC5447B284C0EDEBA04CE2A5D8954A38A`, blob `b9371490047ccd2b4d16329be4d6a499cb449410`, identical at the base, the candidate and live) ran against `3b8296767f93cd11fed7eb6a257ce94683430228` and failed as expected: status FAIL, `LIVE_PROTECTED_MISSING: docs/internal/extensions/opt1/checkpoint-claims.json`. It is fail-fast, so it stops at the first relocated original in its live snapshot and never reaches its other comparisons.

The controlled-difference stage imports the same unchanged module and calls its own `check_protected` repeatedly over the committed tree map and the index map, restoring or removing only the paths each rejection names, and calls its own `source_snapshot` path by path. The complete difference it reports:

- `candidate_tree` `PROTECTED_OMISSION`: `docs/internal/extensions/opt1/checkpoint-claims.json`, `docs/internal/extensions/opt1/checkpoint-report-claims.json`
- `candidate_tree` `PROTECTED_ADDITION`: `docs/internal/extensions/opt1/checkpoint-claims.json.gz`, `docs/internal/extensions/opt1/checkpoint-report-claims.json.gz`, `docs/internal/extensions/opt1/repair-r2/.gitattributes`, `docs/internal/extensions/opt1/repair-r2/ACCEPTANCE_MATRIX.md`, `docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json`, `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.ps1`, `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.py`, `docs/internal/extensions/opt1/repair-r2/preservation/relocation_controls.json`, `docs/internal/extensions/opt1/repair-r2/receipt_archive_control_helper.py`, `docs/internal/extensions/opt1/repair-r2/receipt_archive_controls.json`, `docs/internal/extensions/opt1/repair-r2/run_receipt_archive_controls.ps1`, `docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py`
- `candidate_tree` `PROTECTED_IDENTITY`: `docs/internal/extensions/opt1/.gitattributes`
- `index` `PROTECTED_OMISSION`: `docs/internal/extensions/opt1/checkpoint-claims.json`, `docs/internal/extensions/opt1/checkpoint-report-claims.json`
- `index` `PROTECTED_ADDITION`: `docs/internal/extensions/opt1/checkpoint-claims.json.gz`, `docs/internal/extensions/opt1/checkpoint-report-claims.json.gz`, `docs/internal/extensions/opt1/repair-r2/.gitattributes`, `docs/internal/extensions/opt1/repair-r2/ACCEPTANCE_MATRIX.md`, `docs/internal/extensions/opt1/repair-r2/RECEIPT_ARCHIVES.json`, `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.ps1`, `docs/internal/extensions/opt1/repair-r2/preservation/check_relocated.py`, `docs/internal/extensions/opt1/repair-r2/preservation/relocation_controls.json`, `docs/internal/extensions/opt1/repair-r2/receipt_archive_control_helper.py`, `docs/internal/extensions/opt1/repair-r2/receipt_archive_controls.json`, `docs/internal/extensions/opt1/repair-r2/run_receipt_archive_controls.ps1`, `docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py`
- `index` `PROTECTED_IDENTITY`: `docs/internal/extensions/opt1/.gitattributes`
- `live_snapshot`: `LIVE_PROTECTED_MISSING` `docs/internal/extensions/opt1/checkpoint-claims.json`; `LIVE_PROTECTED_MISSING` `docs/internal/extensions/opt1/checkpoint-report-claims.json`

This equals the enumerated admitted set (the two relocated originals omitted; the two archives and the new `repair-r2/` files added; `docs/internal/extensions/opt1/.gitattributes` changed) on every surface: {'candidate_tree': True, 'index': True, 'live_snapshot': True}. Nothing else differs: without any mapping, the same unchanged functions accept all 35 frozen rows in the candidate's original matrix (True) and in its OPT-1-R1 matrix (True). Status EXPECTED_CONTROLLED_DIFFERENCE; this is recorded as an expected difference, not as a preservation pass.

### (b) Relocation-aware preservation run: PASS

Status PASS. The receipt-archive verifier ran first inside the run (exit 0): RECEIPT-ARCHIVES: RESULT: PASS &#40;2 of 2 required archives verified; 2 manifest entries; 0 extra archives; 11 unselected scanner-text files present; base 4cc95012a31cda9459d06d87b3371c8c172bb973). Only then was the manifest mapping applied:

- `docs/internal/extensions/opt1/checkpoint-claims.json.gz` (blob `0fae86e162e6f220a31d747520d45e1620788fdb`, mode 100644) decompresses to 78,583 bytes with recomputed blob id `25a2026b26c792e42e90a53a6594e0c5c2fd52d9` = base blob `25a2026b26c792e42e90a53a6594e0c5c2fd52d9`, SHA-256 `4073391ECBF3EE6C16301851F0F3F392C5ACF0E0E16BDD64F2B8CE68EE3DF24F`; substituted at `docs/internal/extensions/opt1/checkpoint-claims.json`.
- `docs/internal/extensions/opt1/checkpoint-report-claims.json.gz` (blob `4dbace32334765620f1ee094405b12c11e2c5ad4`, mode 100644) decompresses to 20,740 bytes with recomputed blob id `eb59b5d20aed5491fb66c51e64e9a873ed043823` = base blob `eb59b5d20aed5491fb66c51e64e9a873ed043823`, SHA-256 `71669AACBD57F32955738682AB135444DAD065594090BB89672DB30F59C3B5AB`; substituted at `docs/internal/extensions/opt1/checkpoint-report-claims.json`.
- 10 new files under `repair-r2/` admitted: `.gitattributes`, `ACCEPTANCE_MATRIX.md`, `RECEIPT_ARCHIVES.json`, `preservation/check_relocated.ps1`, `preservation/check_relocated.py`, `preservation/relocation_controls.json`, `receipt_archive_control_helper.py`, `receipt_archive_controls.json`, `run_receipt_archive_controls.ps1`, `verify_receipt_archives.py`.
- `.gitattributes`: candidate blob `85d70dcaa28b954b72e266f4bc41a4c9ac85b1f5` equals base blob `98ee7ff03f07aa528ed09248a602bbcb33ec68cf` followed by exactly 161 appended bytes (SHA-256 `70FACA1EE6FA2119A71FEF1559D5CB6E1853A9CC316D914EAB84117D9678B957`).

Then every OPT-1-R1 preservation check was reproduced through the unchanged module's own functions:

- Amendment identity: the mapped committed protected map equals the protected map of `4cc95012a31cda9459d06d87b3371c8c172bb973` exactly (901 entries); the mapped index map as well (901 entries); index relocation record equal to the committed one: True. Protected counts: {'r1_baseline': 510, 'r2_base': 901, 'candidate': 911}.
- OPT-1-R1 protected identity against its baseline `aecf4a5`: 510 entries all equal (True); index: 510 entries all equal (True).
- Frozen rows (35 inherited IDs each; exact UTF-8 row-content bytes against the freeze `1f3a419`): `freeze_to_base` 35 rows byte-equal True; `freeze_to_live_old` 35 rows byte-equal True; `freeze_to_live_repair` 35 rows byte-equal True; `freeze_to_candidate_old` 35 rows byte-equal True; `freeze_to_candidate_repair` 35 rows byte-equal True. Original matrix entire blob equal to the author baseline: True.
- OPT-1-R1 requirement cells, byte-equal among `f7cf20d`, the candidate and live: `REQ-OPT-R1-EXCLUSIVE-REJECTION` (579 bytes), `REQ-OPT-R1-CHECKOUT-PROVENANCE` (919 bytes), `REQ-OPT-R1-PRESERVATION` (603 bytes), `CHK-OPT-R1-PRODUCTION-REPLAY` (826 bytes).
- R2 requirement rows byte-equal between the freeze commit `55f0f64fc03e7c5a3ca2a30271174d67b3a1f2ad` and the candidate: `REQ-OPT-R2-SELFTEST`, `REQ-OPT-R2-HISTORY`, `REQ-OPT-R2-PRESERVATION-AMENDMENT`, `CHK-OPT-R2-VERIFICATION`.
- Certificate field types: 39 live and 39 committed ExpectedType byte strings exact (True) with 78 named consumers; axiom roots 93.
- OPT-1-R1 control registry: executed 17 of 17 in order, all with their pinned verdicts: `P01-EXACT-ROWS` ACCEPT, `P02-MISSING-MIDDLE-ROW` REJECT ROW_IDS, `P03-DUPLICATE-MIDDLE-ROW` REJECT ROW_DUPLICATE, `P04-CHANGED-MIDDLE-ROW` REJECT ROW_BYTES, `P05-UNKNOWN-ROW` REJECT ROW_IDS, `P06-MISSING-REPAIR-ROW` REJECT ROW_IDS, `P07-DUPLICATE-REPAIR-ROW` REJECT ROW_DUPLICATE, `P08-MOJIBAKE` REJECT MOJIBAKE, `P09-ORDINARY-UNICODE` ACCEPT, `P10-PROTECTED-OMISSION` REJECT PROTECTED_OMISSION, `P11-PROTECTED-BLOB` REJECT PROTECTED_IDENTITY, `P12-PROTECTED-MODE` REJECT PROTECTED_IDENTITY, `P13-UNAUTHORIZED-ADDITION` REJECT PROTECTED_ADDITION, `P14-REPAIR-ADDITION` ACCEPT, `P15-INVALID-UTF8` REJECT UTF8, `P16-LINE-TERMINATORS` ACCEPT, `P17-FIELD-TYPE-ALTERED` REJECT FIELD_TYPE_BYTES.
- Relocation controls (`preservation/relocation_controls.json`, 10 cases, each through the same mapping and identity functions): `X01-EXACT-RELOCATION` ACCEPT, `X02-UNENUMERATED-DELETION` REJECT AMENDMENT_IDENTITY, `X03-OTHER-BLOB-CHANGED` REJECT AMENDMENT_IDENTITY, `X04-ADDITION-OUTSIDE-R2` REJECT AMENDMENT_IDENTITY, `X05-ORIGINAL-BESIDE-ARCHIVE` REJECT RELOCATION_ORIGINAL_PRESENT, `X06-ARCHIVE-WRONG-BYTES` REJECT RELOCATION_BYTES, `X07-ATTRIBUTES-NOT-APPEND-ONLY` REJECT GITATTRIBUTES_APPEND, `X08-ARCHIVE-MISSING` REJECT RELOCATION_ARCHIVE_MISSING, `X09-PACKED-MODE-CHANGED` REJECT AMENDMENT_IDENTITY, `X10-ADDITION-UNDER-REPAIR-R1` REJECT AMENDMENT_IDENTITY.
- Live and index restoration: 512 live snapshot entries unchanged (True), the two relocated originals snapshotted through their live archives; index bytes unchanged (True, SHA-256 `3CD806B12CD7B2573E385FC4B9C09FA08DD04FFC6A0FC84CBF092BA9BF934F4C`); live protected diff and untracked protected files empty, with and without the OPT-1-R1 `repair-r1/` exclusion. 51 bounded Git captures, all with expected exit and no timeout or overflow (True). Duration 7.649 s.

Development evidence for anti-vacuity beyond the registered controls: in a disposable clone, a rehearsal commit that additionally appended one comment line to `RMQ/Core/WordRAM/Packed/Accounting.lean` made the wrapper exit 1, with the controlled-difference stage reporting UNEXPECTED_DIFFERENCE and the relocation-aware stage failing `AMENDMENT_IDENTITY` with `changed: RMQ/Core/WordRAM/Packed/Accounting.lean`. The committed checker imports the unchanged OPT-1-R1 module with bytecode writing disabled, so no `__pycache__` appears inside the protected `repair-r1/` scope, and the stage outputs are written outside the repository.

## Self-test and strict scan on the repaired commit

Same host, same unchanged scanner and policy (SHA-256 `5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7` and `4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9`), clean worktree at `3b8296767f93cd11fed7eb6a257ce94683430228` before and after, no ignored files under the scan roots.

| Command | Exit | Duration (s) | Deadline (s) | Summary-shaped output lines | Summary lines |
| --- | --- | --- | --- | --- | --- |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | 0 | 270.884 | 10800 | 0 | CLAIM-DRIFT SELFTEST: ok -- 6 protected probes rejected and 2 attributed probes accepted<br>CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path<br>CLAIM-DRIFT SELFTEST: ok -- exclusion removed 431 hits &#40;2241 -> 1810)<br>CLAIM-DRIFT SELFTEST: RESULT: PASS |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 0 | 143.329 | 5400 | 1 | CLAIM-DRIFT: scan complete &#40;1810 hits, 0 strict failures) |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords` | 0 | 147.911 | 5400 | 1 | CLAIM-DRIFT: scan complete &#40;2241 hits, 0 strict failures) |

The self-test printed CLAIM-DRIFT SELFTEST: ok -- exclusion removed 431 hits &#40;2241 -> 1810): its two parsed counts, 2241 with records and 1810 without, equal the summary counts of the separate `-Strict -IncludeProcessRecords` and `-Strict` runs on the same tree. Each strict output now contains exactly one summary-shaped line, its own final summary (output lines 1241 and 1580, the last lines), so the unanchored parser cannot read anything else. The strict default-root scan exits 0 with 0 strict failures. Relative to the base, both totals fell by the same amount (1831 to 1810 and 2262 to 2241): the removed hits were the receipts' embedded lines, which both runs had counted, net of hits added by this repair's new scanned files. The process-record exclusion still removes the same 431 hits it removed on the base (431). No scanner, pwsh or rg descendant survived any run.

## Readers of the relocated files

Grep evidence that no production runner, profile manifest, build receipt or registry reads the relocated files (all three commands in `receipts/checks-3b82967.json`):

1. `git grep -l -F -e checkpoint-claims.json -e checkpoint-report-claims.json HEAD --` over the whole repaired tree lists 34 files: the base referring files listed in the archive inventory above (OPT-1-R1 preservation receipts that enumerate the protected history paths, `checkpoint-verification.json` and `RESOURCE_WAIT_20260912_REPORT.md`), plus this repair's own manifest, matrix, attributes file and WDD entry. None is under `scripts/`, `RMQ/`, `lakefile.toml`, a runtime or certificate replay directory, `repair-r1/profile/`, or a `REGISTRY.json` or `registry.json`.
2. `git grep -n -E -e checkpoint- -e 'Get-ChildItem|os.listdir|os.walk|.glob(|rglob|iterdir|-Filter|-Include' HEAD -- scripts lakefile.toml` together with every `.ps1`, `.py`, `REGISTRY.json`, `registry.json` and `repair-r1/profile/*.json` under the OPT-1 history (excluding `repair-r2/`) finds no `checkpoint-` reference. The directory enumerations it does find: `claim_drift_scan.ps1:282` recurses the scan roots, and its attribution pass reads only current-fact surfaces; lines 50 and 298 of the same file match only on the `-IncludeProcessRecords` flag name. `design_decision_check_regression.ps1:194` and `m1_certificate_mutation_regression.ps1:930` enumerate their own fixture and build directories, `packed_optimized_runtime.ps1:332` lists `RMQ/Core/WordRAM/Optimization/*.lean`, and `project_skill_preflight.ps1:61` lists skill directories. None enumerates the OPT-1 history directory.
3. The only reader of the history directory as a whole is the OPT-1-R1 preservation checker (`git ls-tree`/`ls-files` over its protected scopes), which is not a production runner. The coordinator amendment and the two demonstrations above cover it.

## Design, whitespace and trust hygiene checks

- `git.exe diff --check`: exit 0, 0.542 s (deadline 300 s), no output.
- `git.exe diff --check 4cc95012a31cda9459d06d87b3371c8c172bb973..HEAD`: exit 0, 0.58 s (deadline 300 s), no output.
- `pwsh.exe -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 4cc95012a31cda9459d06d87b3371c8c172bb973`: exit 0, 1.503 s (deadline 600 s): DESIGN-CHECK: checked 16 changed files &#40;0 code, 13 workflow, 3 neutral).
- `rg.exe -n \b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib RMQ lakefile.toml`: exit 1, 2.125 s (deadline 300 s), no output.
- `rg.exe -n native_decide|Lean\.ofReduceBool RMQ`: exit 1, 0.506 s (deadline 300 s), no output.

Both trust hygiene scans exit 1 (ripgrep: no match) with no output, identical to the base, where the same two commands also returned no matches; there are no matches to explain. The design check classifies the 16 changed files as 0 code, 13 workflow and 3 neutral, and the WDD entry satisfies the workflow requirement. Both whitespace checks are clean on the repaired commit.

## Command ledger

Host `POINPAD`, Microsoft Windows NT 10.0.26200.0. Every command below ran through `Invoke-RMQOwnedBoundedProcess`. Mutex wait is the wait before the heavy-verification session that served it; bounded checks expected under five minutes did not take the mutex.

| Command | Host process | Tree | Duration (s) | Deadline (s) | Mutex wait (s) | Exit |
| --- | --- | --- | --- | --- | --- | --- |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | pwsh 7.6.6 session driver (`pwsh.exe`) | base 4cc9501 | 297.532 | 10800 | 15807.84 | 1 |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | pwsh 7.6.6 session driver (`pwsh.exe`) | base 4cc9501 | 171.054 | 5400 | 0 (same session) | 0 |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords` | pwsh 7.6.6 session driver (`pwsh.exe`) | base 4cc9501 | 157.787 | 5400 | 0 (same session) | 0 |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | pwsh 7.6.6 session driver (`pwsh.exe`) | repaired 3b82967 | 270.884 | 10800 | 0 (same session) | 0 |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | pwsh 7.6.6 session driver (`pwsh.exe`) | repaired 3b82967 | 143.329 | 5400 | 0 (same session) | 0 |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict -IncludeProcessRecords` | pwsh 7.6.6 session driver (`pwsh.exe`) | repaired 3b82967 | 147.911 | 5400 | 0 (same session) | 0 |
| `python.exe -B docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 2.379 | 900 | 0 | 0 |
| `python.exe -B docs/internal/extensions/opt1/repair-r2/verify_receipt_archives.py --committed 3b8296767f93cd11fed7eb6a257ce94683430228` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 2.81 | 900 | 0 | 0 |
| `git.exe diff --check` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.542 | 300 | 0 | 0 |
| `git.exe diff --check 4cc95012a31cda9459d06d87b3371c8c172bb973..HEAD` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.58 | 300 | 0 | 0 |
| `pwsh.exe -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 4cc95012a31cda9459d06d87b3371c8c172bb973` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 1.503 | 600 | 0 | 0 |
| `rg.exe -n \b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib RMQ lakefile.toml` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 2.125 | 300 | 0 | 1 |
| `rg.exe -n native_decide|Lean\.ofReduceBool RMQ` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.506 | 300 | 0 | 1 |
| `git.exe diff --no-renames --name-status 4cc95012a31cda9459d06d87b3371c8c172bb973..HEAD` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.534 | 300 | 0 | 0 |
| `git.exe grep -n -F -e checkpoint-claims.json -e checkpoint-report-claims.json HEAD -- . :!docs/internal/extensions/opt1/repair-r1/final/preservation-*` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.707 | 300 | 0 | 0 |
| `git.exe grep -l -F -e checkpoint-claims.json -e checkpoint-report-claims.json HEAD --` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.726 | 300 | 0 | 0 |
| `git.exe grep -n -E -e checkpoint- -e Get-ChildItem|os\.listdir|os\.walk|\.glob\(|rglob|iterdir|-Filter|-Include HEAD -- scripts lakefile.toml docs/int` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 0.543 | 300 | 0 | 0 |
| `run_receipt_archive_controls.ps1` (full registry) | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 215.744 | 900 per verifier call, 300 per helper, 1800 per selector child, 5 for the deadline case | 0 | 0 |
| `preservation/check_relocated.ps1` stage `unchanged-r1` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 4.037 | 900 | 0 | 1 |
| `preservation/check_relocated.ps1` stage `controlled-difference` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 4.74 | 900 | 0 | 0 |
| `preservation/check_relocated.ps1` stage `relocated` | Windows PowerShell 5.1.26100.9444 | repaired 3b82967 | 8.351 | 900 | 0 | 0 |

## Limits and unexecuted checks

- Coordinator-owned and not run: `scripts/gate.ps1`, the full default `lake build`, the independent audit and acceptance. No Lean build ran; no Lean, toolchain, lakefile, script or replay input changed.
- Hosts: the scans ran under pwsh 7.6.6 (the gate's host) only; the verifier controls and preservation demonstrations ran under Windows PowerShell 5.1 only. Nothing ran under WSL or Ubuntu, so POSIX process-group ownership of the new runners is unexecuted.
- Process ownership under the packaged pwsh 7.6.6: NATIVE-1-R1 measured that this repository's kill-on-close job does not hold descendants started under the MSIX-packaged pwsh. The scans here finished far inside their deadlines, and the session driver swept for surviving scanner, pwsh and rg descendants after every run (results in the scan receipts). The controls runner refuses to credit its descendant-cleanup case on a packaged host (INCONCLUSIVE, exit 3); it passed under the non-packaged Windows PowerShell 5.1 host.
- The committed receipts are curated. The raw scan stdout, runner receipt and preservation result files stay outside the repository and are identified by SHA-256; the committed runners regenerate everything except the scans, which the coordinator gate reruns.
- The self-test's hit-count parser remains unanchored (explicitly deferred to the coordinator's integration governance commit). The frozen R2 matrix row `REQ-OPT-R2-SELFTEST` must quote the summary shape verbatim; no policy term matches that line, so it is never emitted, which the focused strict scan of the new files and the repaired runs' summary-shaped line counts confirm. A future policy term matching that line would re-arm the defect until the parser is anchored.
- The failure on the base is order-dependent: ripgrep's multi-threaded emission order decides which embedded count the unanchored parser sees first. Both base runs here, and both coordinator runs, put the 457-count receipt first.
- Tip certification scans: the branch tip adds only the report-commit files listed above, which a focused strict scan and a static shape check showed carry no summary-shaped or result-line text. The unchanged self-test and strict default-root scan on the exact tip were queued in the same heavy-verification session after this report was committed; their results are given in the submission message, because a file cannot record a run on the commit that contains it.
- Commit history note: the first report commit `a508eb17469d888bbb17a0cf938658eb302f1c6f` left one trailing space at the end of a report line (an empty timing sentence). The committed-range whitespace check caught it before the tip scans were signaled, and the following commit removes it; history was not rewritten.

## Proof digestion

- What changed conceptually: evidence storage only. A scanner's historical output, stored as text inside the scanned tree, was being read back as live scanner output. The bytes are now stored compressed at a recorded path, and nothing that the claims, theorems, builds or replays consume moved.
- Plain English: the gate's self-check was fooled by an old scan log that quoted its own total. The log is now zipped, still recoverable byte for byte, and the self-check reads the real totals.
- Live assumptions: ripgrep keeps skipping NUL-bearing files during traversal (and, measured here, no current policy term matches the compressed bytes even when forced to search them); Git stores the `binary` archives unconverted; the base commit stays reachable for the verifier and the relocation-aware checker; the coordinator amendment remains the governing reading of `REQ-OPT-R1-PRESERVATION`.
- Downstream consumer: the coordinator aggregate gate on the branch tip, then disposition of the independent audit and acceptance of the OPT-1 node.
- What a skeptical reviewer would ask next: whether any other committed text in the default roots is emitted and carries the summary shape (the repaired runs count summary-shaped output lines, and only the real summary remains); whether the controlled-difference neutralization could hide a difference (it only restores or removes the exact paths each unchanged rejection names, and its result must equal the enumerated set on the tree, index and live surfaces, which a rehearsal with an extra Packed source change rejected); and when the parser anchoring lands, so that this class of defect cannot recur.
