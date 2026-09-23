Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# PRE-1-R1 worker record: claim-scan evidence repair

- Handle and title: PRE-1-R1, `(PRE-1-R1) Repair preprocessing claim-scan evidence lines`.
- Branch `codex/pre-1-r1-claim-receipts`; worktree `C:/Users/poin/Documents/RMQ/.claude/worktrees/pre1-r1-claim-receipts`.
- Base `84ae12f6f6bad99fd3215c5bdd5b2a93e3779897` (PRE-1 final candidate); contract candidate `c1c970b8bfbae03163633365e512d487ae1c98f2`; frozen PRE-1 matrix commit `26d6b5c2b10ed06ae4f72d9075d746ede987bdab`; proof base and workflow-governance ref `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
- Governing prompt `PRE1_R1_CLAIM_RECEIPTS.md`, 18,738 bytes, SHA-256 `4E2B4CE3DCEB27074797B1FB5517F082ED59F2F61410835ACE8C6CA8949963D2`. Skill preflight PASS (required `rmq-proof-sprint`; runtime `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`); `git diff 0e6a00f654abc64f8b68988fa9675b9a839dca2f -- .agents/skills` is empty; the initial HEAD was the base and the tree was clean.
- Commits: `3264da7f6c9a4b8fc4598261166e13701f85a5c9` freezes the R1 matrix (WDD-20260914-PRE1-R1-001); `e977053d8355d0d429da33d71a42251cfa5e964a` is the repaired commit (WDD-20260914-PRE1-R1-002); `ece8ae5606f48befdd03b2c6a33af1e7371733c3` fixes two control-runner defects found by the first full control run (WDD-20260914-PRE1-R1-003); the tip adds this record, the receipts, the appended R1 sections of BUILDER_STAGE_LOG.md and REPORT.md, the matrix evidence appendix and WDD-20260914-PRE1-R1-004. The tip SHA and the checks rerun on it are in the submission message, because a file cannot contain the hash or the scan results of the commit that adds it.
- Request: run the coordinator aggregate gate on the exact branch tip. This worker has not run `scripts/gate.ps1`, the full `lake build` or the builder and contract replay campaigns, and claims no gate result, audit disposition, acceptance or integration.

## What changed

The unchanged claim scanner's self-test failed on `84ae12f` because two lane records quoted earlier scanner summaries and the scanner re-emitted those quotes inside result lines ahead of its own summary. The repair removes every such quote from the scanned tree without touching the scanner, its policy, any Lean file, script, registry, manifest, pin, contract text or frozen row:

- the byte-exact PRE-1-A1 contract audit report left `docs/internal/audit_reports/` and is a single-member gzip at `docs/internal/extensions/pre1/evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz`;
- `docs/internal/extensions/pre1/evidence/author-final-checks-summary.json`, the only lane blob holding a raw claim-scanner result line, is its own path plus `.gz`;
- both archives decompress to their exact base blobs and are marked `binary` in the new lane `.gitattributes`;
- BUILDER_STAGE_LOG.md lines 427, 428 and 488 and REPORT.md lines 245 and 246 state the same counts and outcomes in prose with the same ordered integers, and both files gain an appended R1 section.

On the repaired commit the unchanged `-SelfTest` exits 0 with exclusion counts equal to the separate strict runs on both PowerShell hosts, the strict default-root scan has 0 strict failures, and the order-independent detector finds no emitted quote.

## Changed paths

`git diff --name-status --no-renames 84ae12f6f6bad99fd3215c5bdd5b2a93e3779897..e977053d8355d0d429da33d71a42251cfa5e964a`:

- `M` `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `D` `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md`
- `A` `docs/internal/extensions/pre1/.gitattributes`
- `M` `docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md`
- `M` `docs/internal/extensions/pre1/REPORT.md`
- `A` `docs/internal/extensions/pre1/evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz`
- `D` `docs/internal/extensions/pre1/evidence/author-final-checks-summary.json`
- `A` `docs/internal/extensions/pre1/evidence/author-final-checks-summary.json.gz`
- `A` `docs/internal/extensions/pre1/repair-r1/.gitattributes`
- `A` `docs/internal/extensions/pre1/repair-r1/ACCEPTANCE_MATRIX.md`
- `A` `docs/internal/extensions/pre1/repair-r1/RECEIPT_ARCHIVES.json`
- `A` `docs/internal/extensions/pre1/repair-r1/REWORDS.json`
- `A` `docs/internal/extensions/pre1/repair-r1/build_repair.py`
- `A` `docs/internal/extensions/pre1/repair-r1/check_preservation.py`
- `A` `docs/internal/extensions/pre1/repair-r1/claim_scan_detector.py`
- `A` `docs/internal/extensions/pre1/repair-r1/repair_control_helper.py`
- `A` `docs/internal/extensions/pre1/repair-r1/repair_controls.json`
- `A` `docs/internal/extensions/pre1/repair-r1/run_checker_modes.ps1`
- `A` `docs/internal/extensions/pre1/repair-r1/run_claim_scans.ps1`
- `A` `docs/internal/extensions/pre1/repair-r1/run_repair_controls.ps1`
- `A` `docs/internal/extensions/pre1/repair-r1/verify_receipt_archives.py`
- `A` `docs/internal/extensions/pre1/repair-r1/verify_rewords.py`

`git diff --name-status --no-renames e977053..ece8ae5`: `M docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, `M docs/internal/extensions/pre1/repair-r1/run_repair_controls.ps1`.

The tip commit adds `repair-r1/REPORT.md` (this record) and `repair-r1/receipts/*.json`, and appends to `repair-r1/ACCEPTANCE_MATRIX.md`, `BUILDER_STAGE_LOG.md`, `REPORT.md` and `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`. `docs/internal/DESIGN_DECISIONS.md` is unchanged: the strict design check classifies every changed path as workflow or neutral and no code-sensitive path changed.

## Reproduced failure and mechanism

All base runs used the unchanged scanner blob `62badf7e071447a3f3a3f8db0d47a3970b918ad5` (live SHA-256 `5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7`) and policy blob `491791898dca137d2a7d94126b87402545ccaa9d` on a clean checkout, with `repair-r1/claim_scan_detector.py` (SHA-256 `CDBCBC8816E094A9BA20D49410EB78F9C724F40153267D36697615AD087C8C76`, byte-identical to the copy used before the matrix freeze). Receipt: `repair-r1/receipts/reproduction-84ae12f.json`.

| Tree and host | Strict (exit, final hits, strict failures) | Records (exit, final hits) | Self-test (exit, exclusion form, with records, without) | Result lines with the summary pattern (detector) | First parser match |
| --- | --- | --- | --- | --- | --- |
| `84ae12f`, pwsh 7.6.6, `run_claim_scans.ps1` | 0, 1612, 0 (18.3 s) | 0, 2056 (18.4 s) | 1, removed nothing, 1609, 1609 (26.0 s) | strict: 2, both citing `BUILDER_STAGE_LOG.md:488` (rules `fast-regime-118`, `live-compatibility-352`); records: those 2 plus 2 citing `audit_reports/2026-09-12_PRE1_contract_fresh_blind.md:911` (rules `principled-charged-trace-76`, `historical-silent-sparse-level-207`) | 1609 from the stage-log quote in both logs |
| `84ae12f`, six pwsh and three Windows PowerShell 5.1 self-tests | n/a | n/a | 1, removed nothing, 1609, 1609 in all nine | n/a | n/a |
| export of `babfbef` (author's R-11i tree), pwsh 7.6.6 | 0, 1609 (21 s) | 0, 2053 (14 s) | 1, removed nothing, 11, 1609 (26 s) | strict: 0; records: the 2 audit-report quotes | strict 1609 from the real summary; records 11 from the audit quote |
| coordinator logs `pre1-final-precheck/*.stdout.log` | 1612 | 2056 | removed nothing, 1609, 1609 | the same 2 and 4 result lines as the first row | 1609 in both |

Both observed forms reproduce: the coordinator's form on the base (nine of nine self-tests, both hosts) and the author's form on the author's tree. Mechanism: `Get-ReportedHitCount` in `scripts/claim_drift_scan.ps1` returns the first output line anywhere that matches its hit-count regex; the scanner prints review and fail hits as result lines quoting the matched document line; a quoted historical summary therefore supplies the count. Refinement of the prompt's statement that ripgrep's file order decides which quote comes first: the scanner starts one ripgrep process per policy term, in policy order, and the stage-log line is matched by term index 8 while the audit-report line is first matched by term index 12 (35 terms), so on `84ae12f` the stage-log quote comes first on every run. The two forms differ because the author's R-11i run predated row R-11h, not because of emission order; file order matters only among lines one term matches in several files. The repair does not depend on any order: no pattern-bearing result line remains.

## Archive inventory

Recomputed from Git blobs at the base: 55 blobs under `docs/internal/extensions/pre1/`; exactly one has a raw claim-scanner result line; every scanner prefix occurrence begins a full result line; `BUILDER_STAGE_LOG.md` and `REPORT.md` contain scanner text without a result line (reworded, not archived); three zip containers (`aggregate-gate.zip`, `author-final-checks.zip`, `postgate-final-checks.zip`; 4,300, 4,300 and 2,150 result lines inside compressed members) are not read by the scanner and stay unchanged. Manifest `repair-r1/RECEIPT_ARCHIVES.json` (blob SHA-256 `8351A360960132F8F37FF15189FB6BFB84422FD83DB3DBB725F0DE98C3F0885B`).

| Original (base) | Kind | Base blob id | Blob SHA-256 | Blob bytes | Result lines | Summary-pattern lines | Archive | Archive SHA-256 | Archive bytes | Decompressed bytes |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md` (added unchanged by `5f325ddb856b9095d1ad2aacc0bc69eda571d447`) | named | `b8a7abc83d9347f00198836ac2c011805b0ec6e3` | `2B35DD0386D202EA7D73D28C4754791B43232D4E6CE591E6DAB7C543393EEA52` | 88,646 | 0 | 909, 911 | `docs/internal/extensions/pre1/evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz` | `E8F77103CE5AB4E15734AF6E09564D3FE8A6BDA8C2463C2776471E8A02D0FDBD` | 33,919 | 88,646 |
| `docs/internal/extensions/pre1/evidence/author-final-checks-summary.json` | result-line | `f52767d9b690ecc444b9e181e56fb6a411f93dbd` | `5590C0FB372BDDCE4B29BAB621E9F86B16C1F8E3F251BC5889BEF8181301B4BB` | 4,453 | 1 | 137 | `docs/internal/extensions/pre1/evidence/author-final-checks-summary.json.gz` | `DB44F7AC0D2DBFE58CAB93CCF20B0BF1ABD14B71625C458AC72F66822FD45E39` | 1,199 | 4,453 |

Lane `.gitattributes` (new, blob `9bd69dd96a4e84d257b6d97cc197fa0215573443`): `/evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz binary` and `/evidence/author-final-checks-summary.json.gz binary`, and nothing else. Recovery: `gzip -dc <archive>` or the verifier.

Files that refer to an archived original name at the base (recomputed by `git grep` over the whole base tree and pinned per entry in the manifest; none is rewritten, the manifest resolves them):

- `2026-09-12_PRE1_contract_fresh_blind.md`: `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md` (the report itself), `docs/internal/extensions/pre1/AMENDMENTS.md`, `docs/internal/extensions/pre1/ATTACK_TABLE.md`, `docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md`, `docs/internal/extensions/pre1/CONTRACT.md`, `docs/internal/extensions/pre1/REPORT.md`.
- `author-final-checks-summary.json`: none.

The new R1 files (the matrix, both manifests, the verifiers, the producer, the preservation checker, WDD-20260914-PRE1-R1-001..004 and this record) also name the originals, as resolution records.

## Reword inventory

Recomputed from Git blobs at the base over the 10 lane Markdown blobs: exactly the five lines below match the summary pattern, the coordinator's set. Manifest `repair-r1/REWORDS.json` (blob SHA-256 `8FCEA55E77C01C13FC1EA8137875F62065E6513A5833B9989C88B7DB3A772E23`); base blobs `BUILDER_STAGE_LOG.md` `684a2894ca21fcc3f9e9c9d4c457578fb4db078d` (103,510 bytes, 495 lines) and `REPORT.md` `b3d07015f9aa4150578c7db26a9fc8ff2d33f13c` (143,433 bytes, 1,661 lines).

| File:line | Base line SHA-256 | New line SHA-256 | Ordered integers (base = new) | Rewording |
| --- | --- | --- | --- | --- |
| `BUILDER_STAGE_LOG.md:427` (C7-13) | `B9041FFCF36D864B6FED35C600B712F69C973C4BF1D90674C7D6A8DC1C734BBE` | `60C315C96C0D52D4DA74E2DF673D2F3143A0B5344CD91ABD6F917E24E9BD7AAA` | 7, 13, 1, 1, 1, 31, 28, 23, 68, 0, 1, 1603, 0, 11, 1603, 1 | quoted strict summary becomes "completed with a summary of 1603 hits and 0 strict failures" |
| `BUILDER_STAGE_LOG.md:428` (C7-14) | `694E3291E8A86E06BE82C3D140AC0EE9BAA8A696069312C1A1175C7894741978` | `87043B1AED181995C2B6783EE31E90EB9ADD6CFD9BAB5C5E9F27125583042761` | 7, 14, 7, 13, 1, 1, 1, 33, 1, 36, 20, 0, 0, 2047, 587, 2026, 9, 12, 1, 911, 11, 0, 11, 444, 2047, 1603, 0, 5, 325, 1 | "reports a summary of 2047 hits (rest elided)"; "quotes a scanner summary of 11 hits and 0 strict failures" |
| `BUILDER_STAGE_LOG.md:488` (R-11h) | `B431B175A7B3A7F3E82AD29A942D2FFEFCDEA715CB10C2655831F2B12B860DA6` | `B9A1DD36729D38192380742B73B66EFDB2B9CBB379466A56CAFE7A6836633C98` | 11, 1, 1800, 6, 17, 1, 8, 29, 0, 1609, 0, 7, 13, 118, 352 | "completed with a summary of 1609 hits and 0 strict failures" |
| `REPORT.md:245` | `02A65007166AFC4850EDE6E53CE365765288B4201FD12F7F27321428083D3EA4` | `66EF35FC786CF38F69B2CD16408E8331AEFCBE9409284300221F8E4F8F5AC76F` | 11, 0 | "a scanner summary of 11 hits and 0 strict failures" |
| `REPORT.md:246` | `734A6A0B8DEF9E6A45C863FB94A2DEB40A2E377C836A1729CCFB73FEB83B76E5` | `25CA7643B409D35FF140802D16AEEE451FDF70C5B2F3C31EBAB5D27DC2A61F4E` | 2047 | "a summary of 2047 hits (rest elided)" |

The digit runs (including leading zeros such as `01`) are also equal. No other base byte of either file changed; on the tip each file carries an appended R1 section after its last base line.

## Verifiers and registered controls

`verify_receipt_archives.py --committed` exit 0 on `e977053` and on `ece8ae5`: 2 of 2 required archives verified, 2 manifest entries, 0 extra archives, 2 unselected scanner-text files and 3 zip containers present and unchanged. `verify_rewords.py --committed` exit 0 on both: 2 of 2 files, 5 recorded lines, 0 pattern lines under the lane root, 18 changed text paths in the range without a new pattern line. Receipts `verifiers-e977053.json`, `verifiers-ece8ae5.json`.

`run_repair_controls.ps1` (registry `PRE1-R1-REPAIR-CONTROLS-V1`, 34 cases) ran the full registry on the clean `ece8ae5606f48befdd03b2c6a33af1e7371733c3` inside one mutex hold (wait 0.002 s): Windows PowerShell 5.1 exit 0 in 280.1 s, `RESULT: PASS executed 34 of 34 selected cases`; pwsh 7.6.6 exit 3 in 324.7 s, `RESULT: INCONCLUSIVE executed 34 of 34 selected cases`, where 33 cases passed and the deadline case is INCONCLUSIVE because the packaged host cannot hold descendants. Receipts `controls-ece8ae5-ps51.json` and `controls-ece8ae5-pwsh.json` record every exit, code set, stdout and stderr line, duration, deadline, the export and mutation of each copy, the repository state digest before and after each case (unchanged for all 34 on both hosts) and the removal of each copy and of the work root. Runner SHA-256 `3C7AE3B0AEF6FBB4A83EA027C528AD4AC8EF16E5FAE8C6EDC337FF4E683B1B87`, registry `3B44C6BC3693B1017D4451BDC5DF1E372AF97AFEE1B7183366C7C349C5EB7ED7`, helper `7D4ED15EDDFF0E6358D1973E782240CFC215EA9CB393DA8B3B82EC45C246A476`, archive verifier `76AFAACBA4D788856F4F023872019CF999C63B2AF41AD9FBCC6DA5D2D278A3D3`, reword verifier `B980778487D495B2BC7434EDF26D03C758A5A81FFD975C3DE5F93A7F0F65DF85`. Each negative runs on an exact export of the committed lane root and audit_reports directory in a disposable directory outside the repository and must produce exactly its registered code set in both the stdout failure lines and the result JSON.

| Case | Kind | Requirement | Expected exit and codes | Windows PowerShell 5.1: observed, seconds, verdict | pwsh 7.6.6: verdict, seconds |
| --- | --- | --- | --- | --- | --- |
| `archives-positive-tree` | verify-tree | archive verifier positive on the live checkout | 0; none | exit 0; none; 4.326 s; PASS | PASS; 8.68 s |
| `archives-positive-committed` | verify-committed | archive verifier positive on committed blobs | 0; none | exit 0; none; 8.634 s; PASS | PASS; 10.507 s |
| `archives-positive-copy` | verify-copy | archive verifier positive on an unmutated exact export | 0; none | exit 0; none; 12.159 s; PASS | PASS; 10.572 s |
| `archives-changed-archive-header-byte` | verify-copy | changed archive byte | 1; archive-gzip-invalid, archive-sha256-mismatch | exit 1; archive-gzip-invalid, archive-sha256-mismatch; 11.764 s; PASS | PASS; 10.703 s |
| `archives-changed-archive-trailer-byte` | verify-copy | changed archive byte | 1; archive-gzip-invalid, archive-sha256-mismatch | exit 1; archive-gzip-invalid, archive-sha256-mismatch; 11.584 s; PASS | PASS; 10.675 s |
| `archives-missing-archive` | verify-copy | missing archive | 1; archive-missing | exit 1; archive-missing; 11.619 s; PASS | PASS; 10.509 s |
| `archives-extra-archive` | verify-copy | extra archive not in the manifest | 1; archive-extra | exit 1; archive-extra; 11.909 s; PASS | PASS; 10.66 s |
| `archives-duplicate-manifest-entry` | verify-copy | duplicated manifest entry | 1; manifest-duplicate-entry | exit 1; manifest-duplicate-entry; 11.876 s; PASS | PASS; 10.236 s |
| `archives-wrong-base-blob-id` | verify-copy | wrong base blob id | 1; base-blob-id-mismatch | exit 1; base-blob-id-mismatch; 11.517 s; PASS | PASS; 10.433 s |
| `archives-decompressed-byte-mismatch` | verify-copy | decompressed-byte mismatch | 1; decompressed-bytes-mismatch | exit 1; decompressed-bytes-mismatch; 10.552 s; PASS | PASS; 10.497 s |
| `archives-original-restored` | verify-copy | original file restored beside its archive | 1; original-present, result-line-file-present | exit 1; original-present, result-line-file-present; 8.45 s; PASS | PASS; 10.805 s |
| `archives-audit-report-restored` | verify-copy | original file restored beside its archive (the named audit report, additional) | 1; original-present | exit 1; original-present; 8.379 s; PASS | PASS; 10.423 s |
| `archives-manifest-entry-removed` | verify-copy | missing manifest entry (additional) | 1; archive-extra, attributes-manifest-mismatch, manifest-missing-entry | exit 1; archive-extra, attributes-manifest-mismatch, manifest-missing-entry; 8.572 s; PASS | PASS; 10.33 s |
| `archives-result-line-file` | verify-copy | reintroduced result-line file (additional) | 1; result-line-file-present | exit 1; result-line-file-present; 8.279 s; PASS | PASS; 10.197 s |
| `rewords-positive-committed` | verify-committed | reword verifier positive on committed blobs | 0; none | exit 0; none; 9.196 s; PASS | PASS; 11.981 s |
| `rewords-positive-copy` | verify-copy | reword verifier positive on an unmutated exact export | 0; none | exit 0; none; 7.752 s; PASS | PASS; 9.797 s |
| `rewords-changed-integer` | verify-copy | changed integer | 1; digit-runs-mismatch, integers-mismatch | exit 1; digit-runs-mismatch, integers-mismatch; 7.897 s; PASS | PASS; 9.846 s |
| `rewords-unrecorded-line-changed` | verify-copy | line changed outside the recorded set | 1; unrecorded-line-changed | exit 1; unrecorded-line-changed; 7.617 s; PASS | PASS; 9.74 s |
| `rewords-missing-recorded-line` | verify-copy | missing recorded line | 1; digit-runs-mismatch, new-integers-mismatch, new-line-hash-mismatch, unrecorded-line-changed | exit 1; digit-runs-mismatch, new-integers-mismatch, new-line-hash-mismatch, unrecorded-line-changed; 7.666 s; PASS | PASS; 10.07 s |
| `rewords-reintroduced-pattern` | verify-copy | reintroduced pattern | 1; new-line-hash-mismatch, pattern-present | exit 1; new-line-hash-mismatch, pattern-present; 7.742 s; PASS | PASS; 10.087 s |
| `rewords-wrong-base-line-hash` | verify-copy | wrong base line hash | 1; base-line-hash-mismatch | exit 1; base-line-hash-mismatch; 7.915 s; PASS | PASS; 9.47 s |
| `rewords-manifest-entry-removed` | verify-copy | missing recorded line in the manifest (additional) | 1; reword-missing-entry, unrecorded-line-changed | exit 1; reword-missing-entry, unrecorded-line-changed; 7.872 s; PASS | PASS; 9.679 s |
| `rewords-pattern-in-new-file` | verify-copy | reintroduced pattern in new committed text (additional) | 1; pattern-present | exit 1; pattern-present; 7.656 s; PASS | PASS; 9.634 s |
| `deadline-descendant-cleanup` | deadline | REPLAY-SUBPROCESS-DEADLINE | timeout; root and child absent | timed out after 5.105 s; root 248 and child 29660 both absent; 8.577 s; PASS | INCONCLUSIVE; 5.277 s |
| `registry-missing-case` | registry | REPLAY-EXACT-REGISTRY | 1; registry failure marker, no probe | exit 1; 4.815 s; PASS | PASS; 6.811 s |
| `registry-reordered-cases` | registry | REPLAY-EXACT-REGISTRY | 1; registry failure marker, no probe | exit 1; 5.18 s; PASS | PASS; 6.939 s |
| `registry-version-changed` | registry | REPLAY-EXACT-REGISTRY | 1; registry failure marker, no probe | exit 1; 5.252 s; PASS | PASS; 6.739 s |
| `selector-omitted` | selector | REPLAY-SELECTOR-NONVACUITY | 0; marker probe of 34 | exit 0; executed []; 4.891 s; PASS | PASS; 6.755 s |
| `selector-valid` | selector | REPLAY-SELECTOR-NONVACUITY | 0; marker one executed case | exit 0; executed [archives-positive-committed]; 14.365 s; PASS | PASS; 20.588 s |
| `selector-empty` | selector | REPLAY-SELECTOR-NONVACUITY | 2; marker selector error | exit 2; executed []; 4.893 s; PASS | PASS; 6.638 s |
| `selector-whitespace` | selector | REPLAY-SELECTOR-NONVACUITY | 2; marker selector error | exit 2; executed []; 4.81 s; PASS | PASS; 6.611 s |
| `selector-malformed` | selector | REPLAY-SELECTOR-NONVACUITY | 2; marker selector error | exit 2; executed []; 4.775 s; PASS | PASS; 6.696 s |
| `selector-unknown` | selector | REPLAY-SELECTOR-NONVACUITY | 2; marker selector error | exit 2; executed []; 5.079 s; PASS | PASS; 6.826 s |
| `selector-duplicate` | selector | REPLAY-SELECTOR-NONVACUITY | 2; marker selector error | exit 2; executed []; 5.187 s; PASS | PASS; 6.646 s |

Two earlier attempts on `e977053` are incomplete and not counted (receipt `controls-e977053-incomplete-attempts.json`): a scratch queue wrapper passed a wrong script path (no case ran), then Windows PowerShell 5.1 started from pwsh could not load `Get-FileHash` (no case ran) while pwsh passed 33 cases and failed the deadline case with a locked-output runner error, leaving two sleepers that were stopped. `ece8ae5` fixed the runner only (WDD-20260914-PRE1-R1-003); focused reruns before that commit are in `controls-focused-runner-fix.json`.

## Preservation proof

`check_preservation.py` exit 0 with `--head e977053` and with `--head ece8ae5` (receipts `preservation-e977053.json`, `verifiers-ece8ae5.json`):

- Scope: 22 changed paths, all inside the write scope (the 8 required changes plus 14 additions under `repair-r1/`); no required change missing.
- Protected identities unchanged at `e977053`: `RMQ/` tree `52a4d6cb7d9b3fc66494cfaad2cacabecb5d7089`, `scripts/` tree `12654be15c002a70f5648e9f2f8d44e6ea15d3f3`, `lakefile.toml` `216c45274a0244445a3629d80a32aa49a71c18a9`, `lean-toolchain` `b9994064fbbb081ca94a50384ff5951b50ea5b42`, `RMQ.lean` `cdc7d2282a5bfb547c55960f54f89e198dc03c47`, `docs/DIGESTION_LOG.md` `16526f9fec5926edb8eff419c91417a51cbc9bf6`, `docs/FAMILY_SUMMARY.md` `96f0a2230ef3f0fa83efcc310b02cc8982116946`, `docs/internal/CLAIM_DRIFT_POLICY.json` `491791898dca137d2a7d94126b87402545ccaa9d` (the scanner is inside the unchanged `scripts/` tree).
- 52 lane blobs outside the write scope unchanged (same id and mode), including `CONTRACT.md`, `AMENDMENTS.md`, `ACCEPTANCE_MATRIX.md` (blob `166a048000d4f5de9d19b7a3bd9f1a3f270efae1`), `ATTACK_TABLE.md`, `BUILDER_PLAN.md`, `builder_manifest.json`, `primitive_manifest.json`, `builder_cases.json`, `contract_cases.json` and every other evidence file.
- Ledgers: `WORKFLOW_DESIGN_DECISIONS.md` is its base blob followed by appended bytes; `DESIGN_DECISIONS.md` unchanged.
- Frozen rows: 31 inherited IDs, both rows each (62 rows) byte-identical at the same line numbers as strict UTF-8; the frozen row of each ID is also byte-identical to its row at `26d6b5c` (checked at freeze).
- Checker inputs (22 paths or trees) unchanged and outside the write scope; the six checker scripts contain no code line naming an archived or reworded file (3 comment mentions of BUILDER_STAGE_LOG.md: `preprocessing_builder_gate.ps1` lines 20 and 23, `preprocessing_builder_replay.ps1` line 29); the only docs paths in their code are the four registries and manifests; no Lean file under `RMQ/` or the lane's Lean check scripts (452 files) uses a file-system read.

Reading of the checkers (line numbers at the base, unchanged):

- `scripts/preprocessing_builder_gate.ps1` dot-sources `owned_process_tree.ps1` (56) and runs `preprocessing_builder_replay.ps1` (58) as one owned child; it opens no docs file.
- `scripts/preprocessing_builder_replay.ps1` reads `builder_cases.json` (40), hashes the frozen contract surfaces `contract_cases.json`, `preprocessing_contract_firewall.ps1`, `preprocessing_contract_replay.ps1` and `primitive_manifest.json` (134-139, 166-173), reads `builder_manifest.json` only for re-hash cases (105, 765-775), `lean-toolchain` (347), runs the builder firewall, Lake producers and consumers and the validator (315-334, 698-720), hashes the registry case paths, every `RMQ/Core/WordRAM/Construction/**/*.lean`, the runners, firewalls, consumers, validators, `lakefile.toml`, both manifests and `lean-toolchain` (895-908), and compares `git status` and `git diff` before and after (369-382).
- `scripts/preprocessing_builder_firewall.ps1` runs the contract firewall child (81-102), reads the imports of the 17 closure modules and enumerates `RMQ/Core/WordRAM/Construction/Builder` (109-153), and hashes the closure against `builder_manifest.json` (173-192).
- `scripts/preprocessing_contract_gate.ps1` runs the contract firewall (58), `lake build RMQ.Core.WordRAM.Construction.Contract` (63) and `lake env lean scripts/preprocessing_contract_check.lean` (67).
- `scripts/preprocessing_contract_replay.ps1` reads `contract_cases.json` (28) and `lean-toolchain` (189), runs the contract firewall, Lake producer and consumer (159-173), hashes the registry paths, the construction sources, the runner, firewall, consumer, `primitive_manifest.json` and `lean-toolchain` (537-548).
- `scripts/preprocessing_contract_firewall.ps1` reads `Primitive.lean`, `Input.lean`, `Model.lean` (49-68) and `primitive_manifest.json` (69-88).

The validation checker `rmq_preprocessing_validate` (`RMQ/Validation/Preprocessing.lean`) reads only the environment variable `PRE1_VALIDATE_SELECTOR`. None of the archived or reworded files is an input of any of them, so the builder and contract replay campaigns were not rerun (their inputs are byte-identical; the coordinator gate runs them).

Cheap non-campaign checker modes (`run_checker_modes.ps1`; receipts `checker-modes-84ae12f.json`, `checker-modes-e977053.json`):

| Tree | Host | Result | Duration | Builder registry content SHA-256 (raw) | Contract registry content SHA-256 (raw) | Registry self-tests |
| --- | --- | --- | --- | --- | --- | --- |
| `84ae12f` | pwsh 7.6.6 | 10 of 10 PASS | 215 s | `0bc1fba4b974e05cd94830ff0d6038d6927d33b5928bb65587fc9a2dc166ffe7` (`67d48c7a...`) | `aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e` (`85eaffcd...`) | 42; 16 |
| `84ae12f` | Windows PowerShell 5.1 | 10 of 10 PASS | 151 s | same | same | 42; 16 |
| `e977053` | pwsh 7.6.6 | 10 of 10 PASS | 219 s | same | same | 42; 16 |
| `e977053` | Windows PowerShell 5.1 | 10 of 10 PASS | 187 s | same | same | 42; 16 |

The modes are the builder firewall (17 modules over the contract guard), the contract firewall, and for both replay runners `-SelectorProbeOnly` (52 and 18 selected), `-RegistrySelfTestOnly`, `-SelectorBoundarySelfTestOnly` and `-DeadlineSelfTestOnly` (contract sleeper deadline 45 s, because its 12 s default is known to fail on this host). Every recorded pin is identical across the four runs: the runners' `ExpectedRegistrySha256` values, the normalized SHA-256 of both registries, both manifests (builder `bba201c4...`, primitive `a1d31f0b...`), the contract firewall (`1f6903d5...`) and the contract replay runner (`b85ff767...`), and the runner SHA-256 values each replay mode reports.

## Scans, self-test and detector on the repaired commit

`run_claim_scans.ps1` on the clean `e977053` (receipt `scans-e977053.json`); the repository state was identical before and after each run:

| Host | Strict (exit, hits, strict failures, s) | Records (exit, hits, s) | Self-test (exit, exclusion counts, s) | Detector |
| --- | --- | --- | --- | --- |
| pwsh 7.6.6 | 0, 1633, 0, 20.8 | 0, 2064, 20.5 | 0, removed 431 (2064 with records, 1633 without), 28.3 | CLEAN: 0 result lines with the pattern in either log; exactly one pattern line per log, the scanner summary on the last line (1,120 and 1,459 lines) |
| Windows PowerShell 5.1 | 0, 1633, 0, 20.2 | 0, 2064, 21.7 | 0, removed 431 (2064, 1633), 33.4 | CLEAN, same counts |

Hit accounting (`-ShowAllowed` runs, receipt `hit-accounting-84ae12f-e977053.json`): the strict total rises by 21, all from new R1 text (WORKFLOW_DESIGN_DECISIONS.md +5, the R1 matrix +6, REWORDS.json +4, the producer +2, the control helper +4); the records total rises by 8, the same 21 less the 13 hits of the archived audit report. The archived JSON receipt had no hit and the rewordings changed no count.

## Commands

Host: Windows 11 Pro 10.0.26200, pwsh 7.6.6 (MSIX-packaged), Windows PowerShell 5.1.26100.9444, Python 3.14.4, Git 2.51.0.windows.1, ripgrep 15.1.0. Times are UTC on 2026-09-14. A blind audit of the PRE-1 builder candidate held `Global\RMQHeavyVerification` and ran Lean builds during this work. BUILDER_STAGE_LOG.md rows R1-1 onward carry the same ledger.

| Row | Command | Tree | Host | Start | Duration | Deadline | Mutex wait | Exit |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| R1-1 | `project_skill_preflight.ps1` (exact governance ref, required `rmq-proof-sprint`, runtime catalog); `git diff 0e6a00f6... -- .agents/skills` | `84ae12f` | pwsh 7.6.6 | ≈06:38 | 1.4 s | none (foreground) | not taken | 0; 0 |
| R1-2 | `run_claim_scans.ps1` (strict, records, self-test, detector) | `84ae12f` clean | pwsh 7.6.6 | 06:44:57 | 18.3, 18.4, 26.0 s | 3600, 3600, 7200, 300 s | not taken | 0, 0, 1; detector 1 |
| R1-3 | `claim_drift_scan.ps1 -SelfTest` x6 and x3 | `84ae12f` clean | pwsh 7.6.6; 5.1 | 06:46:21 | 24-31 s each | none (foreground) | not taken | 1 x9 |
| R1-4 | strict, records, self-test and detector over an export of `babfbef` | export outside the repository | pwsh 7.6.6 | 06:52:39 | 21, 14, 26 s | none (foreground) | not taken | 0, 0, 1; detector 1 |
| R1-5 | inventory recomputation from Git objects | `84ae12f` objects | Python 3.14.4 | ≈06:52 | seconds | none | not taken | 0 |
| R1-6 | `run_checker_modes.ps1` | `84ae12f` clean | pwsh 7.6.6; 5.1 | 06:55:47; 06:59:10 | 215 s; 151 s | 1200 s per mode | not taken | 0; 0 |
| R1-7 | commit; `design_decision_check.ps1 -Strict -Base 84ae12f... -Head 3264da7...` | `3264da7` | pwsh 7.6.6 | 07:07:48 | 2.1 s | none | not taken | 0 |
| R1-8 | `build_repair.py --repo <worktree>` | worktree at `3264da7` | Python 3.14.4 | ≈07:12 | < 5 s | none | not taken | 0 |
| R1-9 | both verifiers and `check_preservation.py` on the dangling dry-run commit `60c41ad` | `60c41ad` (tree `fe82c7d`) | Python 3.14.4 | ≈07:21 | < 60 s | 300-600 s per Git call | not taken | 0, 0, 0 |
| R1-10 | commit; `design_decision_check.ps1 -Strict -Base 3264da7... -Head e977053...` | `e977053` | pwsh 7.6.6 | 07:25:07 | 2.1 s | none | not taken | 0 |
| R1-11 | `run_repair_controls.ps1 -Case archives-positive-copy,rewords-missing-recorded-line` | `e977053` clean | 5.1 | ≈07:25:25 | 42 s | 900 s verifier, 300 s helper | not taken | 0 |
| R1-12 | `run_claim_scans.ps1` | `e977053` clean | pwsh 7.6.6; 5.1 | 07:26:50; 07:28:34 | 92 s; 93 s | 3600, 3600, 7200, 300 s | not taken | 0; 0 |
| R1-13 | `verify_receipt_archives.py --committed HEAD`; `verify_rewords.py --committed HEAD`; `check_preservation.py --head HEAD` | `e977053` | Python 3.14.4 | ≈07:29:55 | ≈134 s together | 300-600 s per Git call | not taken | 0, 0, 0 |
| R1-14 | `run_checker_modes.ps1` | `e977053` clean | pwsh 7.6.6; 5.1 | 07:32:38; 07:36:56 | 219 s; 187 s | 1200 s per mode | not taken | 0; 0 |
| R1-15 | full control registry, attempt 1 (scratch queue wrapper) | `e977053` clean | pwsh wrapper | 07:35:16 | 2.6 s | none | 526.1 s | wrapper 0; incomplete, no case ran |
| R1-16 | `claim_drift_scan.ps1 -Strict -ShowAllowed` and `-Strict -IncludeProcessRecords -ShowAllowed`, base export and `e977053` | export; `e977053` clean | pwsh 7.6.6 | ≈07:40 | ≈20 s each | none (foreground) | not taken | 0 x4 |
| R1-17 | range design check; `git diff --check`; `git diff --check 84ae12f...HEAD`; both trust `rg` scans | `e977053` | pwsh 7.6.6; Git; rg | ≈07:42 | < 10 s | none | not taken | 0; 0; 0; 0, 1 |
| R1-18 | full control registry, attempt 2 | `e977053` clean | 5.1 child; pwsh 7.6.6 child | 09:56:50 | 4.1 s; 347.3 s | 900 s verifier, 300 s helper, 5 s sleeper | 8,414.5 s | 1; 1; incomplete |
| R1-19 | focused reruns of the fixed runner (deadline case on 5.1 and pwsh; committed case on a 5.1 child of pwsh) | worktree `e977053` plus the uncommitted runner | 5.1; pwsh 7.6.6; 5.1 | 10:04:46 | 10 s; 6 s; 12 s | 5 s sleeper, 900 s verifier | not taken | 0; 3; 0 |
| R1-20 | commit; `design_decision_check.ps1 -Strict -Base e977053... -Head ece8ae5...` | `ece8ae5` | pwsh 7.6.6 | 10:05:49 | 2.1 s | none | not taken | 0 |
| R1-21 | both verifiers `--committed HEAD`; `check_preservation.py --head HEAD` | `ece8ae5` | Python 3.14.4 | 10:06:21 | 93 s together | 300-600 s per Git call | not taken | 0, 0, 0 |
| R1-22 | full control registry (`run_repair_controls.ps1`, no selector) | `ece8ae5` clean | 5.1; pwsh 7.6.6 | 10:06:12; 10:10:52 | 280.1 s; 324.7 s | 900 s verifier, 300 s helper, 1800 s child, 5 s sleeper | 0.002 s (one hold, 605.3 s) | 0; 3 |

## Row-by-row evidence

| ID | Evidence (repaired commit `e977053`; tip rerun in the submission message) | Worker status and residual |
| --- | --- | --- |
| REQ-PRE-R1-SELFTEST | Unchanged scanner and policy blobs. pwsh 7.6.6 and Windows PowerShell 5.1: `-SelfTest` exit 0, one PASS result, exclusion line ok form with counts 2064 and 1633, equal to the separate `-Strict -IncludeProcessRecords` (exit 0, 2064 hits) and `-Strict` (exit 0, 1633 hits, 0 strict failures) runs on the same clean HEAD; detector CLEAN on both hosts (0 emitted result lines with the summary pattern, exactly one pattern line per log, the scanner's own last line). Base reproduction with the same scanner and detector: DEFECT, both observed forms, the inventory recomputed (2 and 4 pattern-bearing result lines, as the coordinator measured) and the mechanism refined (policy term order). | Met on `e977053` in worker review; the same checks on the exact tip are reported in the submission message; coordinator certification pending |
| REQ-PRE-R1-ARCHIVE | The named audit report and the one recomputed result-line blob are archived at the pinned paths; `verify_receipt_archives.py --committed` exit 0 recomputes blob ids, SHA-256, lengths, line counts, archive digests, decompressed bytes, originals absent, no extra archive, exact `binary` attribute bytes and `check-attr`; the registered negatives reject changed archive bytes (header and trailer), a missing archive, an extra archive, a duplicated entry, a wrong base blob id, a decompressed-byte mismatch, the original restored (JSON receipt and audit report), a removed entry and a reintroduced result-line file with their exact code sets; this record lists every referring file. | Met in worker review; coordinator certification pending |
| REQ-PRE-R1-REWORD | Recomputed set equals the coordinator's five lines; `verify_rewords.py --committed` exit 0 checks base line hashes against the base blob, tip equals base with only the recorded lines replaced plus the tail, equal integer lists and digit runs, no pattern in any non-archive file under the lane root and no changed text path of the range gaining a pattern line; negatives reject a changed integer, an unrecorded line change, a missing recorded line, a reintroduced pattern, a wrong base line hash, a removed manifest entry and a pattern in a new file. R1 sections appended to BUILDER_STAGE_LOG.md and REPORT.md; no committed R1 text contains the pattern (checked on the tip by the same verifier). | Met in worker review; coordinator certification pending |
| REQ-PRE-R1-PRESERVATION | `check_preservation.py` exit 0: 22 paths inside the write scope; protected tree and blob ids unchanged; 52 lane blobs outside the scope unchanged; ledgers append-only; 62 frozen rows byte-identical; 22 checker inputs unchanged; no code-level read of an archived or reworded file; recorded reading of the five scripts and the contract firewall; cheap checker modes PASS with identical pins and registry hashes on both hosts at base and repaired commit. | Met in worker review; the tip adds only R1 text, receipts and ledger entries, rechecked by `check_preservation.py --head <tip>` in the submission message |
| CHK-PRE-R1-VERIFICATION | Both verifiers, the 34-case control registry on `ece8ae5` (Windows PowerShell 5.1: 34 of 34 PASS; pwsh 7.6.6: 33 PASS and the deadline case INCONCLUSIVE), the base reproduction, scans and detector on the repaired commit, the preservation proof, `git diff --check` and the committed-range check, the per-commit and range design checks, both trust scans; commands with host, duration, deadline, mutex wait and exit in the ledger above. | Met for `3264da7`, `e977053` and `ece8ae5`; the two incomplete control attempts on `e977053` are recorded, not counted; the tip's own per-commit design check, range checks and scans are in the submission message |
| REPLAY-EXACT-REGISTRY (R1 verifiers) | `repair_controls.json` version `PRE1-R1-REPAIR-CONTROLS-V1`, 34 ordered IDs pinned in the runner; both `ece8ae5` receipts report 34 executed = 34 selected = 34 expected; the three registry cases (a removed case, reordered cases, a changed version) exit 1 before any case. | Met in worker review |
| REPLAY-SELECTOR-NONVACUITY (R1 verifiers) | Real child invocations: omitted selects 34 (probe), `archives-positive-committed` executes exactly that case, bound empty, whitespace, malformed, unknown and duplicate selectors exit 2 before the registry is read and create no receipt or work directory. | Met in worker review |
| REPLAY-SUBPROCESS-DEADLINE (R1 verifiers) | Every subprocess through `Invoke-RMQOwnedBoundedProcess` with deadlines; exits and stderr retained in the receipts; copies removed in `finally` with their absence and the repository state digest checked for every case; the descendant sleeper's root and child are both absent after its 5 s deadline under Windows PowerShell 5.1, and the MSIX pwsh run reports that case INCONCLUSIVE without starting it, not passed (the first attempt under pwsh exposed a runner defect, fixed in `ece8ae5`). The POSIX branch is not executed on this host. | Met on Windows in worker review; POSIX uncovered |

The 31 inherited rows are preserved, not re-proved: P-MATRIX, P-TREES and P-LANE hold by `check_preservation.py`; P-LOGS by `verify_rewords.py` (no recorded line is a command row the inherited rows cite); P-ARCHIVE by `verify_receipt_archives.py` (the audit report cited by REQ-PRE-CONTRACT decompresses to its base blob); P-MODES by the identical checker-mode fingerprints.

## Limits

- Coordinator-owned and not run: `scripts/gate.ps1`, the full default `lake build`, the builder replay campaign (`preprocessing_builder_gate.ps1`) and the contract gate's Lean build; their inputs are byte-identical to the base (preservation proof), and no aggregate-gate result is claimed.
- The tip commit cannot carry its own SHA or the results of scans run on it. The scans, detector, verifiers, preservation check, per-commit design check and range whitespace check were rerun on the exact tip after committing and are reported in the submission message; the committed receipts cover `84ae12f`, `e977053` and `ece8ae5`; the tip's tree differs from `ece8ae5` only by R1 text, receipts and ledger entries, and `ece8ae5` from `e977053` only by the control runner and a ledger entry.
- Hit counts on the tip differ from `e977053` by whatever the changed runner, the appended R1 text and the receipts match; the self-test compares separate runs on one tree, so only equality on that tree is required, and the tip values are in the submission message.
- The shared first-match parser in `scripts/claim_drift_scan.ps1` is unchanged (deferred to the coordinator's integration governance commit). A future quote of a scanner summary in any scanned file that some policy term matches will reintroduce the failure; the reword verifier guards only this lane root and this range.
- Other scanned files outside this lane still contain the summary pattern on lines that no policy term emits (for example older worklogs, audit reports and one WORKFLOW_DESIGN_DECISIONS.md line); they are outside the write scope and do not affect the self-test today.
- The readable audit report is no longer under `docs/internal/audit_reports/`; restoring it there after the parser fix is an integration step. References to its original path are resolved by the manifest, not rewritten.
- Process deadline coverage: the descendant-cleanup control passes only under Windows PowerShell 5.1 on this host; under the MSIX-packaged pwsh 7.6.6 it is INCONCLUSIVE by design, and the claim-scan runs under pwsh would not have their descendants cleaned on a timeout (none timed out). The POSIX ownership branch is not executed.
- Two control attempts on `e977053` are recorded as incomplete, not as results: the first was a setup failure in a scratch queue wrapper (a case-insensitive variable collision) and ran no case; in the second, Windows PowerShell 5.1 started from pwsh could not load `Get-FileHash`, and under pwsh the deadline case hit a locked-output runner error and left two sleepers that were stopped by hand. The runner fix `ece8ae5` changed only the runner; the controls that count ran on `ece8ae5`.
- A blind audit held the heavy-verification mutex and ran Lean builds during this work, so durations include host contention.

## Proof digestion

What changed conceptually: nothing mathematical. The repair changes how two historical records are stored and how five log lines phrase a count, so the claim-scan self-test measures the tree instead of re-reading quoted history.

Plain English: the scanner's self-check compares two scans by reading the first number it sees after a certain phrase. Our logs had quoted that phrase with old numbers, the scanner printed those quotes as findings, and the self-check read the old numbers. The quotes are now compressed evidence (recoverable byte for byte) or plain prose with the same numbers, and the self-check reads the real totals.

Live assumptions: the scanner skips gzip files because ripgrep treats them as binary (confirmed by the hit accounting, where the archives contribute nothing); the policy and the scanner stay as they are until the coordinator's shared parser fix; `core.autocrlf=true` checkouts are compared through Git blobs, not working-tree bytes.

A skeptical graduate student would ask: "Your self-test passes because no current file quotes a summary, but the parser is still first-match; what stops the next lane from reintroducing the defect?" Nothing in this lane does; the reword verifier only guards the PRE-1 lane root and this range. The durable fix is the deferred shared-tooling change that anchors the parser to the scanner's own final line. A second question: "Is removing the audit report from `audit_reports/` a loss of provenance?" The archive decompresses to the exact blob added by `5f325dd`, the manifest pins its id and SHA-256, and restoring the readable copy is recorded as an integration step after the parser fix.

## Receipts

Under `docs/internal/extensions/pre1/repair-r1/receipts/`: `checker-modes-84ae12f.json`, `checker-modes-e977053.json`, `checks-e977053.json`, `controls-e977053-incomplete-attempts.json`, `controls-ece8ae5-ps51.json`, `controls-ece8ae5-pwsh.json`, `controls-focused-runner-fix.json`, `hit-accounting-84ae12f-e977053.json`, `preservation-e977053.json`, `reproduction-84ae12f.json`, `scans-e977053.json`, `verifiers-e977053.json`, `verifiers-ece8ae5.json`. None holds scanner output lines; paths under the worker's scratch directory are written as `<scratch>`.
