# PRE-1-R1 frozen acceptance matrix: claim-scan evidence repair

Frozen before any repository edit on 2026-09-14 (UTC). Handle PRE-1-R1; title
`(PRE-1-R1) Repair preprocessing claim-scan evidence lines`; worktree
`C:/Users/poin/Documents/RMQ/.claude/worktrees/pre1-r1-claim-receipts`; branch
`codex/pre-1-r1-claim-receipts`; exact base
`84ae12f6f6bad99fd3215c5bdd5b2a93e3779897` (PRE-1 final candidate); contract
candidate `c1c970b8bfbae03163633365e512d487ae1c98f2`; frozen PRE-1 matrix commit
`26d6b5c2b10ed06ae4f72d9075d746ede987bdab`; proof base and workflow-governance
ref `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Governing prompt
`PRE1_R1_CLAIM_RECEIPTS.md`, 18,738 bytes, SHA-256
`4E2B4CE3DCEB27074797B1FB5517F082ED59F2F61410835ACE8C6CA8949963D2`.

This uses `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`. The verbatim
requirement sections and the frozen row cells below do not change after this
commit; evidence, status and an explicitly approved coordinator amendment may
be appended. Startup: the initial HEAD equals the base, `git status --porcelain`
was empty, and `scripts/project_skill_preflight.ps1 -GovernanceRef
0e6a00f654abc64f8b68988fa9675b9a839dca2f -RequiredSkills rmq-proof-sprint
-RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"`
printed PASS (exit 0, 1.4 s); `git diff 0e6a00f654abc64f8b68988fa9675b9a839dca2f
-- .agents/skills` is empty.

Text convention for this file and every R1 file: the scanner's summary text is
never written verbatim. "The summary pattern" means the case-insensitive regular
expression built from the words scan and complete, a space, an escaped opening
parenthesis, one or more ASCII digits, a space and the word hits, which is the
hit-count regex of the unchanged self-test. "A result line" means a line that
begins with the scanner prefix followed by three bracketed fields.

## Verbatim R1 requirements

### REQ-PRE-R1-SELFTEST

On the repaired tip, the unchanged scripts/claim_drift_scan.ps1 -SelfTest exits 0 and prints an exclusion line whose two parsed counts equal the final summary counts of separate -Strict -IncludeProcessRecords and -Strict runs on the same tree, and the unchanged -Strict default-root scan exits 0 with 0 strict failures. In the stdout of both separate runs, an order-independent detector finds zero emitted result lines (lines beginning with CLAIM-DRIFT and three bracketed fields) that contain the scanner summary pattern (the words scan complete, an opening parenthesis, digits and the word hits), and exactly one summary line, the scanner's own last line. First reproduce the failure on 84ae12f with the same scanner and record both observed forms: the coordinator measured "exclusion removed nothing (1609 hits with records, 1609 without)" while standalone -Strict reported 1612 hits and -Strict -IncludeProcessRecords 2056; the PRE-1 author measured "(11 hits with records, 1609 without)" on the same tree family. The detector on the coordinator's runs found two emitted hit lines citing BUILDER_STAGE_LOG.md:488 in the default run, and those two plus two citing docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md:911 in the records run; the parser takes the first matching line anywhere, and which trigger comes first depends on ripgrep's file emission order. Recompute this inventory yourself.

### REQ-PRE-R1-ARCHIVE

(a) docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md (committed at 5f325ddb856b9095d1ad2aacc0bc69eda571d447, the byte-exact PRE-1-A1 contract audit report) is removed from audit_reports and archived at docs/internal/extensions/pre1/evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz; (b) every committed file under docs/internal/extensions/pre1/ at 84ae12f that contains a claim-scanner result line is replaced by a gzip archive at the same path with the suffix .gz; the coordinator measured exactly one such file, evidence/author-final-checks-summary.json, and you must recompute the inventory from Git blobs. Each archive decompresses to the exact Git blob bytes at 84ae12f. RECEIPT_ARCHIVES.json records original path, base blob id, blob SHA-256 and length, archive path, archive SHA-256 and length; the archive verifier recomputes every value, rejects missing, duplicate, extra and mismatching entries and exits nonzero on any mismatch. The report lists every file that refers to an archived original path.

### REQ-PRE-R1-REWORD

Each line of lane-authored Markdown under docs/internal/extensions/pre1/ (archives excluded) that contains the scanner summary pattern is reworded to state the same counts and outcome without the pattern. The coordinator measured BUILDER_STAGE_LOG.md lines 427, 428 and 488 and REPORT.md lines 245-246 at 84ae12f; recompute the set from Git blobs and reword exactly that set. No other byte of those files changes except text appended after the last base line. REWORDS.json records for every reworded line the path, base line number, base blob id, SHA-256 of the exact base line bytes and of the new line bytes, and the ordered list of integers in each; the reword verifier checks base line hashes against the base blob, checks that the new tip file equals the base file with only the recorded lines replaced plus the appended tail, checks the integer lists are equal, and checks that no line of any lane-authored Markdown file under docs/internal/extensions/pre1/ at the tip matches the pattern. Append to BUILDER_STAGE_LOG.md an R1 section recording each command and the rewording, and append to REPORT.md a short R1 section pointing to repair-r1/REPORT.md. No new committed text anywhere, including repair-r1/**, may contain the pattern verbatim; write counts as prose.

### REQ-PRE-R1-PRESERVATION

git diff --name-status --no-renames 84ae12f6f6bad99fd3215c5bdd5b2a93e3779897..HEAD lists only the paths in the write scope. Zero diff under RMQ/, scripts/, lakefile.toml, lean-toolchain, RMQ.lean, every other file under docs/internal/extensions/pre1/ outside the write scope (including CONTRACT.md, AMENDMENTS.md, ACCEPTANCE_MATRIX.md, ATTACK_TABLE.md, BUILDER_PLAN.md, builder_manifest.json and every registry), docs/DIGESTION_LOG.md and docs/FAMILY_SUMMARY.md; appended ledgers have no removed lines. Show with grep evidence and by reading scripts/preprocessing_builder_gate.ps1, scripts/preprocessing_builder_replay.ps1, scripts/preprocessing_builder_firewall.ps1, scripts/preprocessing_contract_gate.ps1 and scripts/preprocessing_contract_replay.ps1 that no builder, contract or validation checker reads any archived or reworded file. Run the cheap non-campaign modes of those checkers that exist (for example the builder replay -RegistrySelfTestOnly mode on pwsh 7.6.6 and Windows PowerShell 5.1 and the builder firewall) on the tip and record their pinned registry hashes as unchanged from 84ae12f.

### CHK-PRE-R1-VERIFICATION

Commit both verifiers with an exact case registry of their own controls. Archive verifier: positive, and negatives for a changed archive byte, a missing archive, an extra archive not in the manifest, a duplicated manifest entry, a wrong base blob id, a decompressed-byte mismatch and the original file restored beside its archive. Reword verifier: positive, and negatives for a changed integer, a line changed outside the recorded set, a missing recorded line, a reintroduced pattern and a wrong base line hash. Each negative runs on a disposable copy and restores exactly. Run: both verifiers and all controls; the reproduction on 84ae12f; the self-test, both strict scans and the detector on the tip; the preservation proof; git diff --check; git diff --check 84ae12f6f6bad99fd3215c5bdd5b2a93e3779897..HEAD; scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit> for EVERY new commit individually (each commit must pass on its own, so each commit carries its own design-ledger entries) and once for the whole range from 84ae12f; both trust hygiene scans. Record command, host, duration, deadline, mutex wait and exit for each.

## Verbatim REPLAY requirements governing the new verifiers

The three inherited REPLAY rows also govern the R1 verifiers and control runner;
the prompt restates them verbatim.

### REPLAY-EXACT-REGISTRY

any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

### REPLAY-SELECTOR-NONVACUITY

omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

### REPLAY-SUBPROCESS-DEADLINE

run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.

## R1 requirement-to-evidence rows

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-PRE-R1-SELFTEST | Verbatim section above | Local rung (claim-scan evidence repair) | On the one repaired tip: unchanged `scripts/claim_drift_scan.ps1 -SelfTest` exit 0 with exactly one PASS result; its exclusion line is the ok form and its with-records and without-records counts equal the final summary hit counts of separate `-Strict -IncludeProcessRecords` and `-Strict` runs on the same clean tree; `-Strict` exit 0 with 0 strict failures; `claim_scan_detector.py` over both separate stdout logs finds zero result lines containing the summary pattern and exactly one pattern line per log, the scanner's own summary on the last nonempty line (verdict CLEAN, exit 0). Base reproduction with the same scanner and detector records both observed failure forms and the mechanism. | Scanner and policy blobs identical to the base -> `run_claim_scans.ps1` owned runs on the clean tip -> detector counts -> the coordinator aggregate gate's `-SelfTest` and `-Strict` checkers on the same tip | (a) The base must reproduce DEFECT with the same tools, or the detector is vacuous. (b) An order-dependent pass: the detector counts every emitted line, so a trigger that happens to be emitted after the summary still fails. (c) A pass bought by a scanner, policy or exclusion change: preservation shows those blobs unchanged. (d) Self-test counts from a different tree: all three runs share one clean HEAD and state digest. | None at freeze | OPEN |
| REQ-PRE-R1-ARCHIVE | Verbatim section above | Local rung | `verify_receipt_archives.py --committed <tip>` exit 0: the named audit report and every base blob under `docs/internal/extensions/pre1/` with a raw result line (recomputed from Git objects, prefix-guarded) have exactly one manifest entry; each archive is a single gzip member with the pinned header whose decompressed bytes hash to the base blob id; recorded SHA-256 and lengths recompute; originals absent; no extra archive; exact `binary` attribute lines; the named original is the blob added by `5f325ddb856b9095d1ad2aacc0bc69eda571d447`. The report lists every file referring to an archived original name at the base. | Base blobs -> gzip archives -> manifest -> verifier -> recovery by `gzip -dc` or the verifier | Registered negatives on disposable copies: changed archive byte, missing archive, extra archive, duplicated manifest entry, wrong base blob id, decompressed-byte mismatch, original restored beside its archive; each must exit 1 with its exact failure-code set, and the unmutated copy must pass. | None at freeze | OPEN |
| REQ-PRE-R1-REWORD | Verbatim section above | Local rung | `verify_rewords.py --committed <tip>` exit 0: the set of (path, base line) pairs of lane Markdown under the root whose base line matches the summary pattern equals the manifest set; every base line hash recomputes from the base blob; the tip blob equals the base blob with only the recorded lines replaced plus a tail after the last base line; base and new integer lists are equal (and so are the digit runs); no line of lane Markdown under the root at the tip matches the pattern, and no line added anywhere in the committed range does. | Base blobs -> REWORDS.json -> tip blobs -> verifier | Registered negatives: changed integer, line changed outside the recorded set, missing recorded line, reintroduced pattern, wrong base line hash; each exits 1 with its exact code set. | None at freeze | OPEN |
| REQ-PRE-R1-PRESERVATION | Verbatim section above | Local rung and inherited-row preservation | `check_preservation.py` exit 0 on the tip: the name-status list of the range is inside the pinned write scope and contains every required change; tree and blob ids unchanged for `RMQ/`, `scripts/`, `lakefile.toml`, `lean-toolchain`, `RMQ.lean`, every base blob under the lane root outside the write scope, `docs/DIGESTION_LOG.md`, `docs/FAMILY_SUMMARY.md`; ledgers append-only; all checker input paths unchanged and outside the write scope; token scan of the six checker scripts (the five named and the contract firewall they invoke) finds no code reference to an archived or reworded file; the 31 frozen rows byte-identical. Cheap checker modes on both hosts record the same pinned registry and surface hashes as on the base. | Changed paths -> checker inputs -> checker modes and registry pins | A write outside the scope, a removed ledger line, a changed registry byte or a code-level read of an archived or reworded file each must fail the checker; the reading of the five named scripts is recorded line by line. | None at freeze | OPEN |
| CHK-PRE-R1-VERIFICATION | Verbatim section above | Verification | Exact commands in the coverage plan below, each with command, host, duration, deadline, mutex wait and exit. | All R1 rows | A setup failure, timeout or partial scan is recorded as incomplete, never PASS; the design check runs per commit and over the range. | None at freeze | OPEN |
| REPLAY-EXACT-REGISTRY (R1 verifiers) | Verbatim section above | New control runner | `repair_controls.json` is a nonempty exact versioned registry pinned by version and ordered IDs in the runner; the runner reports executed and expected cases and fails when they differ. | Registry -> `run_repair_controls.ps1` -> receipt | Registry version change, missing, extra or reordered IDs must fail before any case. | None at freeze | OPEN |
| REPLAY-SELECTOR-NONVACUITY (R1 verifiers) | Verbatim section above | New control runner | Omitted selects the full registry; a valid ID executes exactly that case; bound empty, whitespace, malformed, unknown and duplicate selectors exit 2 before any case, tested through real child invocations. | `-Case` binding state -> selected IDs -> verdict | A child that selects nothing must not exit 0. | None at freeze | OPEN |
| REPLAY-SUBPROCESS-DEADLINE (R1 verifiers) | Verbatim section above | New control runner and scan runner | Every subprocess through `Invoke-RMQOwnedBoundedProcess` with a positive deadline and output ceiling; exits and stderr retained; disposable copies removed in `finally`; repository state digests equal before and after each case; a descendant-spawning sleeper removed at its deadline. | `scripts/owned_process_tree.ps1` -> runners -> receipts | Under the MSIX-packaged pwsh 7.6.6 the kill-on-close job does not hold descendants (NATIVE-1-R1 host finding); there the deadline case must report INCONCLUSIVE, and the PASS must come from a host that can create the condition. | None at freeze | OPEN |

## Inherited frozen rows (31)

Frozen source: the row-content byte strings of
`84ae12f6f6bad99fd3215c5bdd5b2a93e3779897:docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md`
(blob `166a048000d4f5de9d19b7a3bd9f1a3f270efae1`, 125,544 bytes), frozen at
`26d6b5c2b10ed06ae4f72d9075d746ede987bdab`. Each ID has two rows at the base:
the frozen row (byte-identical to the row at the same line of the frozen matrix
commit, checked at freeze) and the author's final-candidate review row appended
later. The whole matrix file may not change. SHA-256 values are of the exact
UTF-8 row bytes without the line feed.

Checks named in the last column:

- P-MATRIX: `check_preservation.py` compares the matrix blob id at the tip with
  the base and extracts both rows of every ID from both blobs as strict UTF-8,
  rejecting missing or duplicate IDs.
- P-TREES: `check_preservation.py` compares the tree or blob ids of `RMQ/`,
  `scripts/`, `lakefile.toml`, `lean-toolchain` and `RMQ.lean` (Lean sources,
  scripts, validators, typed consumers, runners, firewalls and gates).
- P-LANE: `check_preservation.py` compares every base blob under
  `docs/internal/extensions/pre1/` outside the write scope (registries,
  manifests, `CONTRACT.md`, `AMENDMENTS.md`, `ATTACK_TABLE.md`, `BUILDER_PLAN.md`,
  design notes, evidence zips and JSON), plus `docs/FAMILY_SUMMARY.md` and
  `docs/DIGESTION_LOG.md`.
- P-LOGS: `verify_rewords.py` shows that every base line of
  `BUILDER_STAGE_LOG.md` and `REPORT.md` other than the recorded claim-scan lines
  is byte-identical at the tip; the command rows these rows cite (for example
  R-7, R-8, R-11g, R-14) are not in the recorded set.
- P-ARCHIVE: `verify_receipt_archives.py` shows the PRE-1-A1 contract audit
  report cited by the contract row decompresses to its exact base blob.
- P-MODES: `run_checker_modes.ps1` on pwsh 7.6.6 and Windows PowerShell 5.1
  records the same registry, manifest and frozen-surface hashes on the tip as on
  the base.

| ID | Frozen source rows at the base (line: SHA-256) | Preservation | Proving checks |
| --- | --- | --- | --- |
| REQ-PRE-CONTRACT | 66: `3B62C7B8B5097FE118F5CBD0B315C9C7635C590D99964460B96D0DEC85CE2289`; 732: `EBCF5A8FC946288E69A7199EA98EA2890E452ADAEA7ED2FB279DC9FCC3400B68` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-ARCHIVE, P-MODES |
| REQ-PRE-INPUT | 67: `9C14FEF0E4CA9FE8B1F20B9C5F5A1589038486B4D8A5370B50A1DC706B729F79`; 733: `E6E18985966D6D4770C0129CC9F793EBB8A49332CD94889F8FC3ED4942CCA1A5` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| REQ-PRE-MACHINE | 68: `F47A6CE5264E3F56FC8986F5540F6B6DE6C3A393E090B7BCFCA7E80873AF9E39`; 734: `2C83EA02740168500A71C4874EFFB41466D63AF186057A899B6C2163A0720E13` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| REQ-PRE-EXACT | 69: `34D9F1690D377345D7613934E266879FF110937F8FBD482F93D06A145D6B65F4`; 735: `96168E27E7066D680D8130061F3071B80B84153A2D20FCA9556763C433250D1E` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| REQ-PRE-COST | 70: `CE9AFA3D7C2F159240D359B84DE80A73E0C5B61E419FE70DCB2D719A1B951C61`; 736: `F623DB22B105F99D734CE29AE531922D60FE411523BAF50C0F11D75F85DB4900` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| REQ-PRE-JOIN | 71: `87E11BBB79F9EF2099F207EC895144C5ED7C9B25A769BAF64B561A8707D95DAE`; 737: `2010323B12472E4AE52A26B84D70C07E33E1921D5C8B154F6DD7DCBFBD5E9928` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| CHK-PRE-CONTROLS | 72: `D7DBA36F66B516F62C335623974F76273F15CD07AA937FE97BE064B0EFCE2F9E`; 738: `EB57BBC971CF821996A48137F026134E5683C0180634D455E670ECA0AD24E493` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-MODES |
| REPLAY-EXACT-REGISTRY | 73: `339E05378F56C3C3DC82379933A11851FD162C62DD5F911B2BCF439FD547BA22`; 760: `B215E8E4830F5FDF1B2D35605931706EC9A8A75E3028F116CBAE4B12803987C4` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-MODES |
| REPLAY-SELECTOR-NONVACUITY | 74: `233B5DB369277E4D01FA134FBBE28D28332D7557E888344A66F6451AA833FC68`; 761: `5FDC44753B3494B218DCAE4B38A95A75AE29D0B9F9F2AF869DFB828E7499BE73` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-MODES |
| REPLAY-SUBPROCESS-DEADLINE | 75: `6EAA02BC5ADC3D90FCA47AD2D3F98D4F1F71769C26FFB7E5C7EBA8802086B8EA`; 762: `2924B56080E324080865EA2BC65755221EBA321DA12612561AFB2EFD93665C74` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-MODES |
| INV-STORE-IDENTITY | 117: `C0DB752A84EE43870793AE4F71A07F6B5ED2753AA0A93EA3F478DC07FF819B73`; 739: `1A8D7E0A29AFAA3959D690E05C9CD4650ECE168B5EE276A3ADB15B21A8CF7B32` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-VALUE-DEPENDENCY | 129: `DEFD35955CA28FADBBE8F97E05A64ACD919075D1C10A139497B7204838F93D95`; 740: `F0566F1BF174772460CF83AB5056AA5205453D48819175972D8F97AFB7B71842` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-SEMANTIC-NONVACUITY | 141: `08E9F72489FFB1261E9979E57FB651001F4C68F1D6C7B46187B78C77F02CDFFB`; 741: `9E47F4895280925BB383F83C30873F9CBD3D1ADA08F27390F25AA47F77F4AC5D` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-TRACE-EXECUTION | 150: `5292424C3ECFD99F1ED9F13AE07619BB4C55088F1BFC188EDA522EC2CBB560C9`; 742: `9095A50EB8E980BBED8353063FF2DFAF72F0D259D6213DC0BA36B1909F4F5272` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-STORE-AGREEMENT | 159: `B58230F088D9ED4C7B7481AC37EA6207D72A9814670EEF6046B9513D59DA92C7`; 743: `428E67D59558107367CF5408FC19AB0419A3797576509D03422EC2766DF22598` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-READ-BACKING | 168: `84D1CC23C85A5F9E3B5B83CA03555A900A3B6DBBEC954B2E8EEC3C28E8BB7EAC`; 744: `E05D7A779CB58AD0EEE04940E7E225C6CC8F08075E0E5AD60F9DBBE86B73FC6C` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-WORD-WIDTH | 177: `214C287B2BAB64A0A793713766B58E19344C7C7C659B42879B40A0282B532007`; 745: `935285DE6DFC8C2DC30536FB76F29CA19FC6DBDE9C873BD44CD8933D5A9040CF` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-ADDRESS-WIDTH | 188: `6BE8FDDDBBCB3FF3C70C23DC003165B0F90A05B3BDF5A5FC43C3AA03D0A8C06D`; 746: `944AD7BBCC35E8656F458F7514A6933AE0B7F9272FED0882374E39D90C90FD6D` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-INSTRUCTION-ATOMICITY | 200: `50AA4C05D1B22DBE127738457F2453197C663817F0DA26F0C137C0A0650BF504`; 747: `5715E32EABEE1C0C3AC4D6991244F340E2AB2CE1BCFE8CF32059DF45C586A2C9` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-PROGRAM-ACCOUNTING | 211: `DEC1293C910F26C895E98C66E2CBB3F184F8AD37047E202E73B71AA068F37DF1`; 748: `088C559CFCD3B0420813192ECDBF1049E35D61D5B1AC099F96CFB6773481A8B9` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-ORACLE-INDEPENDENCE | 221: `A902941BDBB00A5254DC87F3A3CC703E5D19A9AE5CC66FB18E3478BB87EC3EE4`; 749: `0D70E9D392DA28C3B1F3552A288BCA08E0223A660BFA36FCB5480B049B7A07E9` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-VALIDATION-REACH | 231: `95B8F20BE080E9043CEDD8503BD32E01B8A1C40EBB63FC51E59FE6267A696A7C`; 750: `A7406C1813F7EDFB72A85B15C3AC432C992362BD712E76B106B5914CA75026F5` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-ALL-SIZE | 240: `EAF33C70429627AEEC5AC4081F4027F6DDFDDA3497575DA2D328F7BFA188914F`; 751: `1543F4B3EF311ACECB17B7F54E73877B3D80F9029847B81655194B0C4EDAD380` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-PROOF-SEPARATION | 249: `4DB21972BA5ACAA4AA706DEDF9C985FAA1381EDF1342925A0844BC59D820A9DB`; 752: `B27A428138C200E9F718253149A31AF1B02ACD67B950BC42B105D5481B5C1107` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-NO-SYNTHETIC | 258: `F553CDCEC5C5431BE0B97DA460D0B2ADA819F5FECC0479B7C7A0A8E7E5F7F048`; 753: `564C676E2BEA9F4464A48B23F09E24544AED96AB25ED85D4469FCFF5804757B3` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-CATEGORY-SEPARATION | 267: `770F13D28993D6D27690D063CFFB3FE9ED89917B6995AF6711E8B1436EEF85D0`; 754: `0DF3749B620C1298518F15A299000CC6EE21889ECCF93B0B6CB10D52F13409CB` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-PUBLIC-COMPOSITION | 278: `F7242FF4B8DF07F133AEA94930D16E5BE98369CB0A40C1167412751A2701C286`; 755: `73E05E6AFBF41E14A7CD974B52A1F2B3BC1CC56601B3E6D491A04E161D7C4E01` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-CERTIFICATE-ANTI-BYPASS | 290: `A11C37A91C02824611DA6636D7B179116E00B0CBBDDA636126BFBA0338B08CE6`; 756: `43E1BA48DC5B26BA64EBD9152C86CD0A04ED3AC853E8C732E78CF79A20F9FF6C` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-MUTATION-REPRODUCIBILITY | 305: `7BABCEDE16EE7695C50A21801E4E1B0579A36297F5CD0D3CD0C2D75FFC0C5FE7`; 757: `F74DC08CF773F0B1F47B35C3D95AA0ADA686BA40B129B627D0917738E255C2EB` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS, P-MODES |
| INV-GLOBAL-PHYSICAL-MACHINE | 316: `ABE5789CDDE4E0615400B428C478FB3F2B55EBFF4B1998301D48FA15E0635EB8`; 758: `2146E7C76B2A1EB9CFA9ADC847F5423FA13ADB8E53B237082EF5CA34CFE412B2` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |
| INV-WIDTH-SCALING | 328: `A69B27F0C6EBF10D6B7B45847EE396F72FC5B17314CFC5B0A276A8C14FDFD0FC`; 759: `7D830CDEB2773EF157FE1EA511D8E7842ED07DB0B6E4662195C035DAB3DBEFED` | preserved by byte identity of every input the row's evidence consumes | P-MATRIX, P-TREES, P-LANE, P-LOGS |

## Verification coverage plan (frozen before repository edits)

Mutex policy: every command expected to exceed five minutes blocks on
`Global\RMQHeavyVerification` in a pwsh wrapper and records its wait; the
commands below are expected well under that and run without it unless the host
is loaded, which is then recorded.

| Role | Command | Rows | Unique failure mode | Tree | Expected runtime / deadline |
| --- | --- | --- | --- | --- | --- |
| Development | `run_claim_scans.ps1` on the base, plus repeated `-SelfTest` runs on pwsh and 5.1 and one run over an export of the author's R-11i tree `babfbef` | SELFTEST | the defect and both forms must reproduce with the same tools | base, clean | 20-30 s per run; 3600 s strict, 7200 s self-test |
| Development | Inventory recomputation from Git blobs (archive and reword sets) | ARCHIVE, REWORD | a set taken from a checkout or from the coordinator's count | base objects | seconds |
| Development | `run_checker_modes.ps1` on the base, pwsh and 5.1 | PRESERVATION | base reference for pinned hashes | base, clean | 150-220 s; 1200 s per mode |
| Final-required | `verify_receipt_archives.py --committed <commit>` and `verify_rewords.py --committed <commit>` | ARCHIVE, REWORD | recomputation from Git objects | each repair commit and the tip | under 60 s; 900 s |
| Final-required | `run_repair_controls.ps1` full registry on Windows PowerShell 5.1, and on pwsh 7.6.6 | CHK, REPLAY-* | negatives, selectors, deadline, restoration | committed repaired tree | minutes; 900 s verifier, 300 s helper per case |
| Final-required | `run_claim_scans.ps1` on the repaired tree | SELFTEST | the actual gate commands and the detector | clean repaired commit, then the tip | 20-30 s per run |
| Final-required | `check_preservation.py --head <commit>` | PRESERVATION | scope, protected ids, ledgers, checker inputs, frozen rows | repaired commit and the tip | seconds; 300 s |
| Final-required | `run_checker_modes.ps1` on the tip, pwsh and 5.1 | PRESERVATION | pinned registry and surface hashes unchanged | tip | 150-220 s; 1200 s per mode |
| Final-required | `git diff --check`; `git diff --check 84ae12f6f6bad99fd3215c5bdd5b2a93e3779897..HEAD` | CHK | whitespace in working and committed bytes | tip | seconds |
| Final-required | `scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit>` for every new commit, and `-Strict -Base 84ae12f6f6bad99fd3215c5bdd5b2a93e3779897 -Head <tip>` | CHK | each commit carries its own ledger entry | each commit, range | seconds; 300 s |
| Final-required | `rg -n "\b(sorry\|admit\|axiom\|unsafe\|opaque\|implemented_by\|partial\|extern\|noncomputable)\b\|import Mathlib" RMQ lakefile.toml`; `rg -n "native_decide\|Lean\.ofReduceBool" RMQ` | CHK | trust hygiene over unchanged sources | tip | seconds |
| Coordinator-owned, not run | `scripts/gate.ps1`, full `lake build`, builder and contract replay campaigns | node closure | aggregate certification | tip | coordinator schedule |

## Explicitly deferred work (verbatim from the prompt)

Anchoring the scanner self-test hit-count parser to the scanner's own final summary line is a shared-tooling fix for the coordinator's integration governance commit, not for this lane. Restoring the readable audit report under docs/internal/audit_reports after that fix lands is an integration step. The aggregate gate, the audit disposition and acceptance are coordinator steps.

## Freeze-time reproduction and inventory (evidence, appended as observed)

Recorded before this matrix was written, with scratch copies of the detector
(SHA-256 `CDBCBC8816E094A9BA20D49410EB78F9C724F40153267D36697615AD087C8C76`), the
scan runner (`0A3CE98812903458B103008FD519DE3A8CE72D2F87F3D5CD9646AD14C7B97AF8`) and the
checker-mode runner (`578E9779BFFBF7BCF65EB7886E8379E702B7E3AD05A78540FC2AB8C9398B3DB5`);
the evidence appendix states whether each committed copy is byte-identical. The
scanner blob was `62badf7e071447a3f3a3f8db0d47a3970b918ad5` (live SHA-256
`5310DBA1242B3ED4A0B054A15B1B6911C056C228B2711F3D958EAB539BB3F6F7`) and the policy blob
`491791898dca137d2a7d94126b87402545ccaa9d` (`4096C7A708DF686F0AC7B62D935B22C13C1F1212494A3B39FD2ADD127AD43CD9`).

- Base scans (`run_claim_scans.ps1`, pwsh 7.6.6, clean base, repository state
  unchanged): the strict run exited 0 with a final summary of 1612 hits and 0
  strict failures in 18.3 s; the records run exited 0 with 2056 hits and 0
  strict failures in 18.4 s; the self-test exited 1 in 26.0 s with its
  removed-nothing form reading 1609 with records and 1609 without. The detector
  verdict was DEFECT: two result lines with the summary pattern in the strict
  log, both citing `docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md:488`
  (rules `fast-regime-118` and `live-compatibility-352`), and four in the
  records log, the same two plus two citing
  `docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md:911`
  (rules `principled-charged-trace-76` and `historical-silent-sparse-level-207`).
  In both logs the first-match parser reads 1609 from the stage-log quote.
- Repeated base self-tests: six on pwsh 7.6.6 and three on Windows PowerShell
  5.1, all exit 1 with the same form (1609 and 1609). The coordinator's form
  therefore reproduces deterministically on this tree.
- The author's form reproduced on an export of `babfbefe9e1b047480921bdad31de4e4e77624c5`
  (the tree of the author's R-11i run, before line 488 existed): the strict run
  exited 0 with 1609 hits, the records run exited 0 with 2053 hits, and the
  self-test exited 1 reading 11 with records and 1609 without. The only
  pattern-bearing result lines were the two audit-report quotes, so the parser
  took the quoted 11 in the records run.
- Mechanism, refined: the self-test parser takes the first matching line
  anywhere. The scanner runs one ripgrep process per policy term, in policy
  order, so a line matched by an earlier term is always emitted first; at the
  base the stage-log line is matched by term index 8 and the audit-report line
  by term index 12, which makes the stage-log quote first on every run. Ripgrep's
  file order decides only among lines that one term matches in several files.
  The two observed forms differ because the trees differ, not because of
  emission order. Any order-dependent argument is unnecessary: the repair must
  leave no emitted pattern line at all.
- Archive inventory from Git blobs at the base: 55 blobs under the lane root;
  exactly one has a raw result line (`evidence/author-final-checks-summary.json`,
  blob `f52767d9b690ecc444b9e181e56fb6a411f93dbd`, 4,453 bytes, one result line,
  one summary-pattern line at line 137); every scanner prefix occurrence begins
  a full result line. Three zip containers (`aggregate-gate.zip`,
  `author-final-checks.zip`, `postgate-final-checks.zip`) hold result lines only
  inside compressed members, which the scanner does not read; they are recorded,
  not archived. The named audit report is blob
  `b8a7abc83d9347f00198836ac2c011805b0ec6e3`, 88,646 bytes, SHA-256
  `2B35DD0386D202EA7D73D28C4754791B43232D4E6CE591E6DAB7C543393EEA52`, added
  unchanged by `5f325ddb856b9095d1ad2aacc0bc69eda571d447`; it has no result line
  and summary-pattern lines 909 and 911.
- Reword inventory from Git blobs at the base: lane Markdown lines matching the
  summary pattern are `BUILDER_STAGE_LOG.md` lines 427, 428 and 488 and
  `REPORT.md` lines 245 and 246, the coordinator's set. `REPORT.md` is blob
  `b3d07015f9aa4150578c7db26a9fc8ff2d33f13c`, 143,433 bytes, SHA-256
  `77C15AB7A581C4E9D7146CD15D8A1DDAF53C4B26138A4B11C26E6A40645F029E`, as the prompt states.
- Base checker modes (`run_checker_modes.ps1`): all ten modes PASS on pwsh
  7.6.6 (215 s) and on Windows PowerShell 5.1 (151 s); builder registry content
  SHA-256 `0bc1fba4b974e05cd94830ff0d6038d6927d33b5928bb65587fc9a2dc166ffe7`
  with 42 registry self-tests; contract registry content SHA-256
  `aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e` with 16.

## Status at freeze

Every R1 row is OPEN. No inherited row is re-evaluated here; the inherited rows
are preserved, not re-proved. Acceptance, the aggregate gate and the audit
disposition are coordinator steps.

## Evidence appendix (worker review, 2026-09-14)

Appended; nothing above changed. Evidence for the frozen R1 rows on `3264da7`, `e977053` and `ece8ae5`, reviewed by the worker against the verbatim requirements; the worker record `repair-r1/REPORT.md` holds the inventories, tables and command ledger, and `repair-r1/receipts/` the receipts. "Met in worker review" is not acceptance: the coordinator aggregate gate on the exact tip, the audit disposition and coordinator acceptance remain.

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
