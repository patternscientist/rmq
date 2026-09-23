Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# NATIVE-1-R1 worker report: claim-scan evidence receipts

- Handle and title: NATIVE-1-R1, `(NATIVE-1-R1) Repair native claim-scan evidence receipts`.
- Branch `codex/native-1-r1-claim-receipts`; worktree `C:/Users/poin/Documents/RMQ/.claude/worktrees/native1-r1-claim-receipts`.
- Base `4edb1e14f607a809c018d569c3d4be99c0c54959` (NATIVE-1 final candidate); workflow-governance ref `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; skill preflight PASS (required `rmq-proof-sprint`, runtime `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`).
- Governing prompt `NATIVE1_R1_CLAIM_RECEIPTS.md`, 15,856 bytes, SHA-256 `84AF19C0FCEBD8ABC186E891EC62D9941522971B27002CFBE806E6F25C75F0FB`.
- Commits: `5d3bc54fb3c81027f21d908a46cc99b31dc4f233` freezes the repair matrix and records WDD-20260913-NATIVE1-R1-001; `d0b4cef57e87540f4e333d15a5564bda8834227d` is the repaired commit (archives, manifest, verifier, controls, attributes, implementation record). The branch tip adds only this report, the matrix evidence appendix, the committed controls receipt and a WDD verification note; its SHA is given in the submission message, because a file cannot contain the hash of the commit that adds it.
- Request: run the coordinator aggregate gate on the exact branch tip, and the continuation check of `4edb1e14f607a809c018d569c3d4be99c0c54959..<tip>`. This worker has not run `scripts/gate.ps1` and claims no gate result, acceptance or integration.

## What changed

Twelve NATIVE-1 command receipts embedded earlier claim-scanner output. The unchanged default-root scan read that output as claim text, so the aggregate gate on `4edb1e1` failed. Each of the twelve is now a gzip archive at its original path plus `.gz`, and it decompresses to the exact Git blob bytes at the base. The scanner, its policy, globs, allowlists and exclusions are unchanged. The strict default-root scan and the self-test now pass on the repaired commit. A committed manifest, verifier and 19-case control runner let anyone recompute the recovery from Git objects. Every other byte of the candidate is unchanged except the admitted additions listed below.

## Changed paths (`git diff --no-renames --name-status 4edb1e1..d0b4cef`)

- `M` `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `M` `docs/internal/extensions/native1/.gitattributes`
- `D` `docs/internal/extensions/native1/commands/claim-drift-native-readme.json`
- `A` `docs/internal/extensions/native1/commands/claim-drift-native-readme.json.gz`
- `D` `docs/internal/extensions/native1/commands/claim-drift-packet.json`
- `A` `docs/internal/extensions/native1/commands/claim-drift-packet.json.gz`
- `D` `docs/internal/extensions/native1/commands/claim-native-source-checkpoint.json`
- `A` `docs/internal/extensions/native1/commands/claim-native-source-checkpoint.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-claims-process-command.json`
- `A` `docs/internal/extensions/native1/commands/final-claims-process-command.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-claims-process.json`
- `A` `docs/internal/extensions/native1/commands/final-claims-process.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-claims-public-command.json`
- `A` `docs/internal/extensions/native1/commands/final-claims-public-command.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-claims-public.json`
- `A` `docs/internal/extensions/native1/commands/final-claims-public.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-metadata-checks.json`
- `A` `docs/internal/extensions/native1/commands/final-metadata-checks.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-static-command.json`
- `A` `docs/internal/extensions/native1/commands/final-static-command.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-text-claims-command.json`
- `A` `docs/internal/extensions/native1/commands/final-text-claims-command.json.gz`
- `D` `docs/internal/extensions/native1/commands/final-text-claims-process.json`
- `A` `docs/internal/extensions/native1/commands/final-text-claims-process.json.gz`
- `D` `docs/internal/extensions/native1/commands/metadata-checks-before-public-blob.json`
- `A` `docs/internal/extensions/native1/commands/metadata-checks-before-public-blob.json.gz`
- `A` `docs/internal/extensions/native1/repair-r1/ACCEPTANCE_MATRIX.md`
- `A` `docs/internal/extensions/native1/repair-r1/RECEIPT_ARCHIVES.json`
- `A` `docs/internal/extensions/native1/repair-r1/receipt_archive_control_helper.py`
- `A` `docs/internal/extensions/native1/repair-r1/run_receipt_archive_controls.ps1`
- `A` `docs/internal/extensions/native1/repair-r1/verify_receipt_archives.py`

The report commit adds `docs/internal/extensions/native1/repair-r1/REPORT.md` and `docs/internal/extensions/native1/repair-r1/CONTROLS_RECEIPT_d0b4cef.json`, and appends to `docs/internal/extensions/native1/repair-r1/ACCEPTANCE_MATRIX.md` and `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`. `docs/internal/DESIGN_DECISIONS.md` is unchanged: the strict design check classifies every changed path as workflow or neutral, and no code-sensitive path changed.

## Reproduced failure on the unchanged base

The unchanged strict default-root scan and self-test ran on the clean worktree at `4edb1e14f607a809c018d569c3d4be99c0c54959`, under pwsh 7.6.6 inside `Global\RMQHeavyVerification`. Scanner SHA-256 `5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7`; policy SHA-256 `4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9`.

| Command | Exit | Duration (s) | Deadline (s) | Summary |
| --- | --- | --- | --- | --- |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 1 | 1703.225 | 10800 | `CLAIM-DRIFT: strict mode found 17 unapproved sensitive matches` |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | 1 | 2291.572 | 21600 | `CLAIM-DRIFT SELFTEST: ok -- 6 protected probes rejected and 2 attributed probes accepted`; `CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path`; `CLAIM-DRIFT SELFTEST: FAIL -- could not read a hit count from both runs`; `CLAIM-DRIFT SELFTEST: RESULT: FAIL` |

All 17 strict failures come from the term `forbidden-2pow128-canonical-activation`: 14 in `commands/final-static-command.json` and 3 in `commands/final-claims-public.json`. This matches the gate record. The frozen matrix records the per-file table. Mutex: this session waited 10303.26 s (acquired 2026-09-13T12:13:13.6628118Z). Two earlier queued attempts were cancelled while still waiting so that their deadlines could be raised; neither ever held the mutex. Counted from the first queue at 2026-09-13T08:06:19Z, the total wait was 14,814 s. The same session then served the scans of the repaired commit, so no second wait was needed.

## Archive inventory

Twelve archives replace 8,785,885 blob bytes and 4,571 claim-scanner result lines with 1,206,228 archive bytes. The counts, blob ids and digests below are the committed manifest `docs/internal/extensions/native1/repair-r1/RECEIPT_ARCHIVES.json`, and the verifier recomputed each of them on `d0b4cef`.

| Original receipt (`commands/`) | Result lines | Base blob id | Blob SHA-256 | Blob bytes | Archive SHA-256 | Archive bytes | Decompressed bytes |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `claim-drift-native-readme.json` | 2 | `ae85ea8f985f001629cc1b06bdf56bfb25209358` | `ECDE3DCF2D2DB9D25C9F2B7A3445EBB22B31843F0484FCC43001F3A9FB0B8639` | 1,378 | `13C39FCF08BDD46E3FDB735A57244E9D087220BA59433746BB20A0DD849FFBCD` | 621 | 1,378 |
| `claim-drift-packet.json` | 58 | `393537de9cef52e4e2e2cf0ad3322b9c5b575549` | `9012550729DC59F6A4FF2202A4CDEC5A9160C79DD5BC31F468D85C206FBDF424` | 15,518 | `1C7D2F500130E861CA6288C32739533B449956C19A130EE85B8CA78D346A8085` | 1,558 | 15,518 |
| `claim-native-source-checkpoint.json` | 184 | `75730d644fae2e001ab0a98bc23b16a5b037ab2b` | `1645FBAF9478D69586EA1AB9B7328DE7416A565F236BD7D7AFCFB7AAD4C61830` | 50,485 | `3677A12060580E070DE15972EDC4C7E562DFD82D2BA56FBAAFA1CA86AB518386` | 5,812 | 50,485 |
| `final-claims-process-command.json` | 8 | `0de72bf0243aee216beab3ff703a01b90cf3661e` | `16E5FC0AA866338B5269E24A9769DFE1418D52E25DB8C6083404C5ECC894B280` | 4,790 | `471EC10A7974D0BBB805D20FD4D62374611F73210C192E6EE16B2EB1BCB3DDE1` | 1,353 | 4,790 |
| `final-claims-process.json` | 282 | `f0d0d24aa6246e727d1273c20c9d96fb41c8ec0f` | `60E2469637958ECD701375EB85E06B4C88DFC4649CE669642CC59F9572222575` | 129,943 | `0C50B6A46D0277023FE9635A7D8A8F6C32F3251B54091A66F896911AE16DFA6F` | 22,256 | 129,943 |
| `final-claims-public-command.json` | 8 | `f734369147652e9b835a97a34f1e83a91063576f` | `AC7B1CDBE521F3C22E03AE9B96BDFE6A22AD09765DEBA7B95F850ED7C777A373` | 2,993 | `771F4654B086D65F2A401FDEF3BA7D0E19933ED9F0D5A979EF92787738B49779` | 789 | 2,993 |
| `final-claims-public.json` | 277 | `25da3996e47a45187ae6b8ead41a0304f27344e7` | `B42003CE4F66E2682172861842B2789B631FC6DF0A9011F201753A40E211EC22` | 139,441 | `5D4DB70088AA5FB163C2B7C918CB754F482B03678DCD13ABEDA068D7F96410C2` | 24,569 | 139,441 |
| `final-metadata-checks.json` | 84 | `655a0e41a7dab1f8109dde91ae007bcac9441a94` | `C825CB3393E349629B507B65F7ECB964C0B5EAFBFB7C72F933A3EDC42479CD74` | 26,282 | `AF13F3AD9EBD8FDFACE7D7F02DEE89CAD1700D84FA101E15AB120D06850F3C43` | 5,384 | 26,282 |
| `final-static-command.json` | 3,294 | `98331e54b9259b42feb8482bb0189acb67680c19` | `CF300AC0127A4FEC0D9DDED1EBCB906C5BA16CEC84FEFC323E5D36CE47217EF3` | 8,253,880 | `FB288DCBED23770DC9C45E35BF7A00D8434A064F21ACE1BC8946F93263CE79C1` | 1,114,860 | 8,253,880 |
| `final-text-claims-command.json` | 8 | `c1eda55352806ea5979637177ec5677ba47917a7` | `279E52386697567774D704CF75FE2524183C2C14F4C3C98DFD54AF758A910F40` | 4,793 | `F9B8E8610C08D3A300CB09BA8112402E060309581C0BA916D08BE8EE6463AA97` | 1,358 | 4,793 |
| `final-text-claims-process.json` | 282 | `00b401d7d17d4f60b0d6f1be7ea7c76d7f39dec7` | `6BB49BA80D5395EB5ECDAE40C33680EBAABF48DF7A6ED7347B96DEE9CA2B7175` | 129,948 | `9441834D18427E7653D0157EBC6973710E159AC76128F7F1642FE98543507D30` | 22,238 | 129,948 |
| `metadata-checks-before-public-blob.json` | 84 | `86f27ad5243395986821fb193401e8fb38e74258` | `7BA93098A74B4F38A0D02552662EF09BABA267D5AD74055EB675CA0268D15C2D` | 26,434 | `414976873974C97840A1FF89454F858FB8D75F06A61704CD91FEAC56D6A07886` | 5,430 | 26,434 |
| **12 receipts** | 4,571 | | | 8,785,885 | | 1,206,228 | 8,785,885 |

| Original receipt | Files referring to its name at the base (unchanged; resolved by the manifest) |
| --- | --- |
| `claim-drift-native-readme.json` | `native1/AUDIT_PACKET_INDEX.json`, `native1/COMMANDS.md`, `native1/commands/final-claim-surface-inventory.json`, `native1/commands/final-claims-process.json`, `native1/commands/final-claims-public.json`, `native1/commands/final-text-claims-process.json` |
| `claim-drift-packet.json` | `native1/AUDIT_PACKET_INDEX.json`, `native1/COMMANDS.md`, `native1/commands/final-claim-surface-inventory.json`, `native1/commands/final-claims-process.json`, `native1/commands/final-claims-public.json`, `native1/commands/final-static-command.json`, `native1/commands/final-text-claims-process.json` |
| `claim-native-source-checkpoint.json` | `native1/AUDIT_PACKET_INDEX.json`, `native1/commands/final-claim-surface-inventory.json`, `native1/commands/final-claims-process.json`, `native1/commands/final-claims-public.json`, `native1/commands/final-static-command.json`, `native1/commands/final-text-claims-process.json` |
| `final-claims-process-command.json` | `native1/AUDIT_PACKET_INDEX.json` |
| `final-claims-process.json` | `native1/ACCEPTANCE_MATRIX.md`, `native1/AUDIT_PACKET_INDEX.json`, `native1/REPORT.md` |
| `final-claims-public-command.json` | `native1/AUDIT_PACKET_INDEX.json` |
| `final-claims-public.json` | `native1/ACCEPTANCE_MATRIX.md`, `native1/AUDIT_PACKET_INDEX.json`, `native1/REPORT.md` |
| `final-metadata-checks.json` | `native1/commands/final-metadata-checks.json`, `native1/commands/metadata-checks-before-public-blob.json` |
| `final-static-command.json` | `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`, `native1/ACCEPTANCE_MATRIX.md`, `native1/AUDIT_PACKET_INDEX.json`, `native1/REPORT.md`, `native1/commands/final-claim-surface-inventory.json`, `native1/commands/final-claims-process.json`, `native1/commands/final-claims-public.json`, `native1/commands/final-text-claims-process.json` |
| `final-text-claims-command.json` | `native1/AUDIT_PACKET_INDEX.json` |
| `final-text-claims-process.json` | `native1/AUDIT_PACKET_INDEX.json`, `native1/REPORT.md` |
| `metadata-checks-before-public-blob.json` | none |

Every file that referred to an original name at the base, recomputed by `git grep` at the base and pinned per entry in the manifest:

- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `docs/internal/extensions/native1/ACCEPTANCE_MATRIX.md`
- `docs/internal/extensions/native1/AUDIT_PACKET_INDEX.json`
- `docs/internal/extensions/native1/COMMANDS.md`
- `docs/internal/extensions/native1/REPORT.md`
- `docs/internal/extensions/native1/commands/final-claim-surface-inventory.json`
- `docs/internal/extensions/native1/commands/final-claims-process.json`
- `docs/internal/extensions/native1/commands/final-claims-public.json`
- `docs/internal/extensions/native1/commands/final-metadata-checks.json`
- `docs/internal/extensions/native1/commands/final-static-command.json`
- `docs/internal/extensions/native1/commands/final-text-claims-process.json`
- `docs/internal/extensions/native1/commands/metadata-checks-before-public-blob.json`

None of these references is rewritten, and the manifest resolves each name to its archive. Six of the referring files are themselves archived receipts, so their references now sit inside archives. The pinned `AUDIT_PACKET_INDEX.json`, the NATIVE-1 `REPORT.md`, its matrix appendix, `COMMANDS.md`, `final-claim-surface-inventory.json` and the WDD ledger keep the original names. The BV-1 precedent at `codex/bv-1-fully-charged-rank-select` tip `38325028` has 34 `.gz` receipts under `bv1/commands/` and one `.md.gz` beside them, 35 in total; the prompt counts 35 `.json.gz` receipts. This repair follows the format and does not depend on the count.

## Verifier and registered controls

`docs/internal/extensions/native1/repair-r1/run_receipt_archive_controls.ps1` ran on the committed repaired tree under Windows PowerShell 5.1: exit 0, 446.0 s, `RESULT: PASS executed 19 of 19 selected cases (registry NATIVE1-R1-RECEIPT-ARCHIVE-CONTROLS-V1, 19 cases)`. It records HEAD `d0b4cef57e87540f4e333d15a5564bda8834227d`. The receipt is committed as `docs/internal/extensions/native1/repair-r1/CONTROLS_RECEIPT_d0b4cef.json`. Each negative runs on a disposable copy outside the repository and must produce its exact failure-code set. Before and after every case the runner compares repository-state digests (HEAD, porcelain status and the bytes of the manifest, verifier, helper, runner and every commands-root archive), and it checks that the copy was removed.

| Case | Kind | Exits (helper/verifier) | Expected codes | Observed codes | Durations (s) | Deadlines (s) | Restored | Verdict |
| --- | --- | --- | --- | --- | --- | --- | --- | --- |
| `positive-worktree` | verify-worktree | 0 | none | none | 30.737 | 900 | True | PASS |
| `positive-committed` | verify-committed | 0 | none | none | 35.579 | 900 | True | PASS |
| `positive-copy` | verify-copy | 0 | none | none | 35.629 | 900 | True | PASS |
| `changed-archive-header-byte` | mutate | 0/1 | archive-sha256-mismatch | archive-sha256-mismatch | 1.249/30.651 | 300/900 | True | PASS |
| `changed-archive-trailer-byte` | mutate | 0/1 | archive-gzip-invalid, archive-sha256-mismatch | archive-gzip-invalid, archive-sha256-mismatch | 0.797/26.364 | 300/900 | True | PASS |
| `missing-archive` | mutate | 0/1 | archive-missing | archive-missing | 0.911/25.939 | 300/900 | True | PASS |
| `extra-archive` | mutate | 0/1 | archive-extra | archive-extra | 0.818/25.208 | 300/900 | True | PASS |
| `duplicate-manifest-entry` | mutate | 0/1 | manifest-duplicate-entry | manifest-duplicate-entry | 0.859/23.419 | 300/900 | True | PASS |
| `wrong-base-blob-id` | mutate | 0/1 | base-blob-id-mismatch | base-blob-id-mismatch | 0.747/24.101 | 300/900 | True | PASS |
| `decompressed-byte-mismatch` | mutate | 0/1 | decompressed-bytes-mismatch | decompressed-bytes-mismatch | 0.752/22.861 | 300/900 | True | PASS |
| `original-restored` | mutate | 0/1 | original-present | original-present | 0.857/21.87 | 300/900 | True | PASS |
| `manifest-entry-removed` | mutate | 0/1 | archive-extra, manifest-missing-entry | archive-extra, manifest-missing-entry | 0.714/20.781 | 300/900 | True | PASS |
| `deadline-descendant-cleanup` | hold | -1 | none | none; held root/child [33300, 9504] absent after timeout | 10.095 | 10 | True | PASS |
| `selector-empty` | selector | 2 | none | none | 1.307 | 300 | True | PASS |
| `selector-whitespace` | selector | 2 | none | none | 1.061 | 300 | True | PASS |
| `selector-malformed` | selector | 2 | none | none | 1.087 | 300 | True | PASS |
| `selector-unknown` | selector | 2 | none | none | 1.178 | 300 | True | PASS |
| `selector-duplicate` | selector | 2 | none | none | 1.102 | 300 | True | PASS |
| `selector-valid` | selector | 0 | none | none | 25.657 | 1500 | True | PASS |

The contract's positive and six negatives map to `positive-worktree`/`positive-committed`, `changed-archive-header-byte` (plus `changed-archive-trailer-byte`), `missing-archive`, `extra-archive`, `duplicate-manifest-entry`, `wrong-base-blob-id` and `decompressed-byte-mismatch`. `original-restored`, `manifest-entry-removed`, the deadline control and the selector controls are extra. Two rehearsal defects, found in a disposable clone before the repaired commit, were fixed there (bracket wildcards in `-like`; 5.1 JSON serialization of a generic list). Both made cases fail closed, never pass.

## Claim scan and self-test on the repaired commit

Both ran on the clean worktree at `d0b4cef57e87540f4e333d15a5564bda8834227d` in the same mutex session, pwsh 7.6.6, with the unchanged scanner (SHA-256 `5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7`) and policy (SHA-256 `4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9`).

| Command | Exit | Duration (s) | Deadline (s) | Summary |
| --- | --- | --- | --- | --- |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 0 | 1265.16 | 10800 | `CLAIM-DRIFT: scan complete (1907 hits, 0 strict failures)` |
| `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -SelfTest` | 0 | 2312.494 | 21600 | `CLAIM-DRIFT SELFTEST: ok -- 6 protected probes rejected and 2 attributed probes accepted`; `CLAIM-DRIFT SELFTEST: ok -- no emitted line cites a process-record path`; `CLAIM-DRIFT SELFTEST: ok -- exclusion removed 431 hits (2338 -> 1907)`; `CLAIM-DRIFT SELFTEST: RESULT: PASS` |

No scanner descendant survived either run: strict none, self-test none. Porcelain status was empty and HEAD unchanged before and after. The control runner and the static ledger checks below ran during the strict scan, inside the same mutex session and read-only on the worktree, so the scan's wall time includes that load.

Why the archives leave the scan corpus. This ran on `d0b4cef` in 12.0 s, exit 0, from a scratch script whose rg commands are described below. Its first attempt inside the ledger runner exited 1 on a JSON line-splitting bug in the script (`str.splitlines` splits inside JSON strings), not on a finding. It was fixed and rerun directly.

- E1 default traversal: gz files with match events: 0 ; end events (files opened): 0
- E1 --binary traversal: gz files with match events: 13 of 13 gz files
- E2 policy terms with any match inside a .gz under the commands root: none (35 terms)
- E3 archives containing b'CLAIM-DRIFT': 0
- E3 archives containing the failing term's power-of-two numeral: 0
- E3 archives containing b'canonical': 0
- E4 required attribution required-current-readword-only-theorem-attribution selects archives: 0
- exit=0 sec=11.9677061

E1 queried the commands root with pattern `.` twice. The default traversal produced no match event in any `.gz` file. With `--binary`, all 13 `.gz` files matched: the twelve new archives plus the base `claim-drift.json.gz`. So the archives are enumerated and then skipped by ripgrep's binary detection, not by an ignore rule. E2 ran every policy term with the scanner's own flags and found no match inside a `.gz` under the commands root. E3 shows that the archive bytes do not contain the scanner prefix or the failing term's text, so skipping does not hide text that a binary-aware search would find. E4 shows that the required-attribution pass, which reads files itself, selects no archive path.

## Preservation

`PRES-01`..`PRES-07` were computed from Git objects of `4edb1e1` and `d0b4cef`; `PRES-08` is the committed-HEAD verifier run (exit 0).

- PRES-01 PASS 31 entries {'D-receipt': 12, 'A-archive': 12, 'A-repair-r1': 5, 'M-gitattributes': 1, 'M-WDD': 1, 'M-DD': 0} unexpected=[]
- PRES-02 PASS git diff --quiet BASE..HEAD -- RMQ native scripts lakefile.toml lean-toolchain lake-manifest.json RMQExamples VerifiedDS .agents .claude .codex .github artifact paper README.md exit 0
- PRES-03 PASS 293 non-evidence native1 blobs compared; changed=[]
- PRES-04 PASS matrix blob 42c5ce5ade2640d21cf459520f3cb19fed7312db prefix sha256 0A5D2313CCEC30DE81AAB3B19439247C612CE4B8FC6C19C0BF51F6C3809D103E
- PRES-05 PASS 44 pinned public paths; differing=[]
- PRES-06 PASS 260 other receipts compared; altered=[] new=[] originals-removed=True
- PRES-07 PASS WDD 678307->685933 prefix=True; DD identical; gitattributes 795->1476 exact-archive-lines=True
- PRESERVATION PASS d0b4cef57e87540f4e333d15a5564bda8834227d

## Design, whitespace and trust hygiene, with the command ledger

Every command below ran through `Invoke-RMQOwnedBoundedProcess` from Windows PowerShell 5.1 with a 600 s deadline, on the clean committed tree `d0b4cef`. `rg` exit 1 means no match.

| Check | Role | Command | Duration (s) | Deadline (s) | Exit |
| --- | --- | --- | --- | --- | --- |
| `diff-check-worktree` | final | `git diff --check` | 1.433 | 600 | 0 |
| `diff-check-base-head` | final | `git diff --check 4edb1e14f607a809c018d569c3d4be99c0c54959..d0b4cef57e87540f4e333d15a5564bda8834227d` | 1.289 | 600 | 0 |
| `design-strict-base` | final | `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 4edb1e14f607a809c018d569c3d4be99c0c54959` | 3.126 | 600 | 0 |
| `design-strict-commit-5d3bc54` | final (per commit) | `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 4edb1e14f607a809c018d569c3d4be99c0c54959 -Head 5d3bc54fb3c81027f21d908a46cc99b31dc4f233` | 3.125 | 600 | 0 |
| `design-strict-commit-d0b4cef` | final (per commit) | `pwsh -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 5d3bc54fb3c81027f21d908a46cc99b31dc4f233 -Head d0b4cef57e87540f4e333d15a5564bda8834227d` | 2.866 | 600 | 0 |
| `trust-hygiene-keywords` | final | `rg -n \b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib RMQ lakefile.toml` | 5.436 | 600 | 1 |
| `trust-hygiene-native-decide` | final | `rg -n native_decide\|Lean\.ofReduceBool RMQ` | 1.347 | 600 | 1 |
| `preservation` | final | `python <scratch>\preservation.py . d0b4cef57e87540f4e333d15a5564bda8834227d` | 19.555 | 600 | 0 |
| `verifier-committed-head` | final | `python docs/internal/extensions/native1/repair-r1/verify_receipt_archives.py --committed d0b4cef57e87540f4e333d15a5564bda8834227d` | 37.725 | 600 | 0 |

The design checks printed `checked 31 changed files (0 code, 29 workflow, 2 neutral)` (aggregate), `checked 2 changed files (0 code, 1 workflow, 1 neutral)` for `5d3bc54`, and `checked 30 changed files (0 code, 28 workflow, 2 neutral)` for `d0b4cef`. Both trust hygiene scans have no matches, as expected: no Lean file changed (`PRES-02`).

## Findings for the coordinator (outside this repair's write scope)

1. Process ownership on this host. The kill-on-close job in `scripts/owned_process_tree.ps1` does not hold descendants started under the MSIX-packaged pwsh 7.6.6, whether that pwsh is the bootstrap or the launched tool. Probes with 6 s and 8 s deadlines left both a timed-out root and its child alive. Two focused claim scans left an orphaned `rg` after their deadlines; this task identified both by their root argument and stopped them. Under Windows PowerShell 5.1 with a non-packaged child, the same probe removed both processes, and the runner's `deadline-descendant-cleanup` case passed. The aggregate gate launches the packaged pwsh, so its deadlines may not reach descendants on this host. The runner here refuses a packaged host with INCONCLUSIVE (exit 3). This task ran its own scans through a wrapper that records the scanner PID and removes any surviving descendants; none survived.
2. Scan cost. The policy-v28 multiline term `required-pq1-fully-charged-attribution` restarts a lazy paragraph expansion at every line. On a JSON receipt without blank lines it costs roughly lines times bytes: 136.5 s for the 970,501-byte `commands/build-20260912T091755276.json` alone. With the rest of the corpus, a strict default-root scan took 1703.225 s on the base and 1265.16 s on the repaired commit, and a self-test took 2291.572 s and 2312.494 s. The expected 171-412 s came from other trees. None of the slow files is an archived receipt.

## Requirement status

| ID | Evidence on `d0b4cef` | Worker status |
| --- | --- | --- |
| `REQ-NATIVE-R1-CLAIM-SCAN` | Base reproduction: strict exit 1 with 17 = 14 + 3 fails; self-test exit 1 with the quoted line. Repaired commit: strict exit 0 with the scan-complete summary and 0 strict failures; self-test exit 0 with a positive exclusion delta. Scanner and policy digests are unchanged, `scripts/` is identical (`PRES-02`), and no path was added under `audit_reports` or with a `WORKLOG` name (`PRES-01`). Binary skip evidence E1-E4. | Evidence complete; the coordinator aggregate gate is pending. |
| `REQ-NATIVE-R1-HISTORY` | Verifier exit 0 on the worktree and at the committed HEAD; 12 of 12 archives recover exact base blobs, with blob ids recomputed from bytes. The manifest carries every required field plus result-line counts and referring files. The references listed above are not rewritten. | Evidence complete. |
| `REQ-NATIVE-R1-PRESERVATION` | `PRES-01`..`PRES-08` pass. | Evidence complete; the continuation check is pending. |
| `CHK-NATIVE-R1-VERIFICATION` | Runner 19/19 with restoration digests; strict scan, self-test, both diff checks, the strict design check against the base and per commit, and both hygiene scans each have a recorded command, duration, deadline and exit. | Evidence complete. |
| `REPLAY-EXACT-REGISTRY` (new runner) | Versioned registry with a pinned count of 19; the run reports `executed 19 of 19`; a selected child run reports `executed 1 of 1`. | Evidence complete. |
| `REPLAY-SELECTOR-NONVACUITY` (new runner) | Omitted selects all 19 cases. A valid selector runs exactly `positive-copy`. Bound empty, whitespace, malformed, duplicate and unknown selectors exit 2 through a real child PowerShell before any case runs. | Evidence complete. |
| `REPLAY-SUBPROCESS-DEADLINE` (new runner) | Every subprocess is owned and bounded, and exits and stderr are recorded. Mutations touch only disposable copies, which are removed in `finally`; restoration digests match. The deadline control observed both held processes absent. A packaged host is refused as INCONCLUSIVE. | Evidence complete for Windows PowerShell 5.1 on this host; POSIX was not exercised. |
| 31 inherited rows and 4 continuation obligations | Preserved by byte identity of all non-evidence paths: `PRES-01`, `PRES-02`, `PRES-03`, `PRES-04`, `PRES-05`, `PRES-06`, `PRES-08` as mapped in the frozen matrix. | Preserved; the independent audit of `4edb1e1` still applies, and the coordinator continuation check is pending. |

## Limits and unexecuted checks

- Not run by this task (coordinator-owned): `scripts/gate.ps1`, the full default `lake build`, the continuation check and acceptance. No Lean build is needed, because no Lean, native, script or build input changed.
- The strict scan and self-test ran under pwsh 7.6.6 only, the gate's host; neither ran under Windows PowerShell 5.1 or on Ubuntu/WSL. The control runner ran under Windows PowerShell 5.1 only; under packaged pwsh it reports INCONCLUSIVE by design, and its POSIX path was not exercised.
- Commit `d0b4cef` carries the certifying scans. The report commit adds scanned prose (this file, the matrix appendix and the WDD note), and focused strict scans of those paths passed before that commit. The strict scan, self-test, verifier and diff and design checks on the exact branch tip are reported in the submission message; the coordinator gate should repeat them.
- The scan-evidence scripts (session driver, scanner wrapper, preservation checks, binary-skip evidence) are scratch tooling outside the repository. Their commands and outputs are recorded here; they are not committed replays.
- The controls rehearsal in a disposable clone and the pre-freeze host probes are development evidence only.

## Proof digestion

- What changed conceptually: the historical NATIVE-1 receipts that quote claim-scanner output now sit in a binary container, so the claim scan reads only maintained text. Exact recoverability stops depending on the working copy and becomes a checked property of Git objects: manifest, raw blob bytes, recovered bytes.
- Plain English: the gate stopped failing on the lane's own old scanner logs. The scanner rules did not get weaker, and the old logs are still byte-for-byte available.
- Live assumptions: ripgrep keeps skipping NUL-containing files during directory traversal, which E1 measures on this tree; Git keeps storing `binary` archives unconverted; the base commit stays reachable for the verifier.
- Downstream consumer: the coordinator aggregate gate and continuation check on the branch tip; then acceptance of the NATIVE-1 node.
- Skeptical question: could a future receipt quote scanner output again and fail the same way, or could a new maintained claim hide inside a `.gz` under a scanned root? The first needs a process rule (archive scanner output when it is recorded, WDD-20260913-NATIVE1-R1-001). The second is a real residual: the scanner does not read archives, so any future archive under a scanned root needs its own review. This repair adds only receipts whose recovered bytes are the exact base blobs.
