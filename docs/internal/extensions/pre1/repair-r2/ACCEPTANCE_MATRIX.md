# PRE-1-R2 frozen acceptance matrix: builder consumer markers and controls

Frozen before any repository edit on 2026-09-14 (UTC-7 host clock). Handle
PRE-1-R2; title `(PRE-1-R2) Repair builder consumer markers and controls`;
worktree `C:/Users/poin/Documents/RMQ/.claude/worktrees/pre1-r2-consumer-markers`;
branch `codex/pre-1-r2-consumer-markers`; exact base
`a0c93e9cf4d3c93856f5756ff6a7271da2b821ff` (verified PRE-1-R1 tip, an
evidence-only child of the PRE-1 final candidate
`84ae12f6f6bad99fd3215c5bdd5b2a93e3779897`); contract candidate
`c1c970b8bfbae03163633365e512d487ae1c98f2`; frozen PRE-1 matrix commit
`26d6b5c2b10ed06ae4f72d9075d746ede987bdab`; proof base and workflow-governance
ref `0e6a00f654abc64f8b68988fa9675b9a839dca2f`. Governing prompt
`PRE1_R2_CONSUMER_MARKERS.md`, 18,929 bytes, SHA-256
`60499BD23101670392C011EA08B4D4B78C23FF9B6B629C655940CD43C9267C2B`. Audit report
PRE-1-A2, 53,979 bytes, SHA-256
`bda5f41450dddaf4cec8fc898e63d99881a12fece96f4ccc476b3fa2f82ed180`.

This uses `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`. The verbatim
requirement sections and the frozen row cells below do not change after this
commit; evidence, status and an explicitly approved coordinator amendment may
be appended. Startup: the initial HEAD equals the base, `git status --porcelain`
was empty, and `scripts/project_skill_preflight.ps1 -GovernanceRef
0e6a00f654abc64f8b68988fa9675b9a839dca2f -RequiredSkills rmq-proof-sprint
-RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"`
printed PASS (exit 0, 2.2 s; the runtime catalog exposes exactly those three RMQ
skills); `git diff 0e6a00f654abc64f8b68988fa9675b9a839dca2f -- .agents/skills` is
empty and the governance ref is an ancestor of the base.

Text conventions for this file and every R2 file. The scanner's summary text is
never written verbatim: "the summary pattern" means the case-insensitive regular
expression built from the words scan and complete, a space, an escaped opening
parenthesis, one or more ASCII digits, a space and the word hits, and "a result
line" means a line that begins with the scanner prefix followed by three
bracketed fields; scan outcomes are stated in prose. "The hygiene words" means
the nine words of the gate's step-2 pattern; no R2 edit writes one of them into a
comment or string under the gate roots (`RMQ`, `RMQExamples`, the eight root
`.lean` files and `lakefile.toml`).

## Verbatim R2 requirements

### REQ-PRE-R2-HYGIENE

At the tip, the exact scripts/gate.ps1 step-2 hygiene command (rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" over RMQ RMQExamples RMQPaper.lean RMQHub.lean RMQRankSelect.lean RMQBPNavigation.lean RMQUnionFind.lean VerifiedDS.lean RMQArchive.lean RMQExamples.lean lakefile.toml) and the native_decide/ofReduceBool command both return no match. The docstring rewording keeps the line count of RMQ/Validation/PreprocessingContract.lean unchanged, so every registered consumer line number stays valid, and no new text anywhere under those roots matches the hygiene pattern.

### REQ-PRE-R2-MARKER

Each typed consumer whose verdict marker the replays or gate checkers read (scripts/preprocessing_builder_check.lean, RMQ/Validation/PreprocessingContract.lean) prints its marker if and only if the whole file elaborated with no error-severity message and the existing witness and guard conditions hold. Establish the mechanism empirically on Lean 4.22.0 with a committed control matrix run in disposable copies: for each of these consumers, the marker is absent and the exit is nonzero for (a) a failing anonymous example, (b) a failing run_cmd or #guard-style check, (c) a declaration that fails with a maximum-recursion-depth error (the CAB2/CAB4 class), (d) an unknown identifier inside a checked theorem, and (e) a failure in a declaration the witness does not reference; and the marker is present with exit 0 on the unchanged file. Run the same five failure classes against scripts/preprocessing_contract_check.lean and scripts/preprocessing_spec_check.lean and scripts/preprocessing_stage_check.lean; for any of them that prints its marker on failure, apply the same mechanism (for the contract consumer, record the change as a contract amendment entry). Record the mechanism, the Lean API it relies on and why it sees errors from earlier commands in the same file.

### REQ-PRE-R2-HALTS

Add registered builder replay mutation cases that (i) weaken the halts field of BuilderRunFacts to a strictly weaker proposition that every program's run satisfies at some fuel or that no longer names the halted status, and (ii) replace the fuel in halts by a larger literal budget; each must be rejected at the capstone consumer with an exact registered line set. Record in repair-r2/REPORT.md and the appended REPORT.md section that work is fuel-trivial and that halts together with work at the pinned linear fuel is the linear-work content of REQ-PRE-COST.

### REQ-PRE-R2-RUNSAFE

Add a registered builder replay mutation case that weakens Run.Safe (for example by dropping the post-state fit conjunct) and is rejected at the exact builder or capstone consumer line set. The foundation-case re-hash mechanism may be used exactly as for B35-B42.

### REQ-PRE-R2-RECORDS

Append to the end of the Version 3 section of CONTRACT.md and to AMENDMENTS.md a dated amendment entry recording that the Cw and Dw numeral cases (B50, B51) are consumer cases in RMQ/Validation/PreprocessingContract.lean rather than scripts/preprocessing_builder_check.lean, with the reason, citing PRE-1-A2 P3-1; quote the superseded V3-7 (ii) text. Correct BUILDER_REPLAY_DESIGN.md in the four stale places and in every place the R2 runner or registry change makes stale. The builder replay runner's rejection verdict for consumer-stage cases additionally requires the profile's verdict marker to be absent from that stage's output, with matcher self-tests for rejection-with-marker (verdict false) and rejection-without-marker (verdict true); B16, B17 and B18 then serve as regression controls. The registry version increases, its content pin is updated in every place that pins it, and the report lists old and new content hashes.

### CHK-PRE-R2-VERIFICATION

Reproduce P1-1, P2-1 (every class above on the unchanged base) and P2-2 before any edit. On the tip run, under the mutex where required: the builder firewall; builder replay registry, selector-boundary and deadline self-tests on pwsh 7.6.6 and Windows PowerShell 5.1; the complete builder replay (every case, including the new ones, with executed/expected IDs); the complete 18-case contract replay; lake build of the capstone, consumers and rmq_preprocessing_validate and lake exe rmq_preprocessing_validate; all five typed consumers with exit 0 and markers; the marker control matrix; both hygiene commands; the R1 archive and reword verifiers; claim_drift_scan.ps1 -Strict, -Strict -IncludeProcessRecords and -SelfTest with the order-independent detector showing zero emitted result lines that contain the scanner summary pattern; git diff --check; git diff --check a0c93e9cf4d3c93856f5756ff6a7271da2b821ff..HEAD; scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit> for every new commit individually (each commit must pass on its own) and once for the whole range from the base. Record command, host, duration, deadline, mutex wait and exit for each.

## Verbatim REPLAY requirements governing the runner change and the new control runner

The three inherited REPLAY rows govern the builder replay runner change and the
new marker control runner `repair-r2/run_marker_controls.ps1`; the prompt
restates them verbatim.

### REPLAY-EXACT-REGISTRY

any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure.

### REPLAY-SELECTOR-NONVACUITY

omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing.

### REPLAY-SUBPROCESS-DEADLINE

run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed.

## Audit findings to repair (verbatim from the prompt)

P1-1, line 12 of RMQ/Validation/PreprocessingContract.lean is docstring prose containing the word sorry, which the gate's step-2 hygiene command matches, so scripts/gate.ps1 records a soft failure and ends in GATE FAIL. P2-1, the typed consumers print their PASS markers while failing: in registry cases B16_PROGRAM_PARAMETER, B17_PROGRAMWORD_PARAMETER and B18_EFFICIENTBUILD_RELOCATION the builder consumer exits 1 and prints its marker, because the V3-2 `@` examples and the V3-1 run_cmd check are not referenced by consumerWitness; auditor probes CAB2 (queryOnEmitted restated over buildMemory xs) and CAB4 (headerUseWord : HeaderUse builderProgram) make the capstone consumer exit 1 with maximum-recursion-depth errors and still print its marker. P2-2, BuilderRunFacts.work bounds steps by exactly the fuel, so it holds for every program; the load-bearing linear-work content is halts at that fuel, and no registered case weakens or deletes halts (B45 weakens only work). P3-1, the Cw and Dw numeral cases (B50, B51) live in the capstone consumer contrary to V3-7 (ii) with no amendment. P3-2, BUILDER_REPLAY_DESIGN.md is stale in four places (stage order lists three producer targets, the runner has four including Proof.Constants; the registry schema lists an old closed path set, the runner admits 15 paths; the gate default is given as 1800 s, the checker's is 10800 s; the validator is said to run after the cases, the runner runs it before). P3-4, no registered case mutates Run.Safe, whose Iff.rfl pin safety_run_safe_definition is unexercised.

## Non-goals and explicitly deferred work (verbatim from the prompt)

Non-goals: P3-3 (reach of the stage and spec consumers), P3-6 (named objects in consumer types), P3-7 (packaging the address translation), P3-8 (substring matchers at producer stages and in the contract runner), P3-9 (DIGESTION_LOG wording); tightening any constant; changing the capstone structure or any theorem; the claim scanner or its policy.

Explicitly deferred work: The findings listed under Non-goals are coordinator follow-ups for integration hardening. The continuation audit, aggregate gate and acceptance are coordinator steps.

## R2 requirement-to-evidence rows

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge attempted and outcome | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-PRE-R2-HYGIENE | Verbatim section above | Local rung (audit P1-1) | On the tip: the `scripts/gate.ps1` line-374 command over its eleven roots prints nothing (rg exit 1), and the line-377 command over its ten roots prints nothing (rg exit 1), also with `lakefile.toml` appended as the prompt spells the roots. `RMQ/Validation/PreprocessingContract.lean`: the docstring edit replaces lines 11-12 only and changes no line count, so lines 1 to the verdict section are the base lines with their base numbers except lines 11 and 12, and every registered capstone surface line (at most 428) is unchanged; every line added under the gate roots in the range is free of the hygiene words. | gate.ps1 step 2 (`SoftFail "hygiene scan hit"`) -> `GATE FAIL` at the base; no hit at the tip -> the coordinator aggregate gate's step 2 | (a) The base must reproduce the hit on line 12, or the scan is vacuous. (b) A rewording that moves lines would silently invalidate registered consumer lines: line-by-line comparison of the pre-verdict region and every registered line. (c) The new marker code under `RMQ/` could itself introduce a hygiene word (for example the placeholder name in a comment): added-line scan with the same pattern. | None at freeze | OPEN |
| REQ-PRE-R2-MARKER | Verbatim section above | Local rung (audit P2-1) | Committed control registry `repair-r2/marker_controls.json` and runner `repair-r2/run_marker_controls.ps1`, run on disposable copies outside the repository through `lake env lean` with LEAN_NUM_THREADS=1: on the tip, for the builder and capstone consumers, classes (a) failing anonymous example, (b) failing `#guard` (and, for the builder consumer, failing V3-1 `run_cmd`), (c) witnessed declaration failing with a maximum-recursion-depth error, (d) witnessed theorem with an unknown identifier, (e) failing unreferenced declaration each exit nonzero with zero marker lines and an error at the injected line (and the class diagnostic), plus a failing check after the marker command; the unchanged copy exits 0 with exactly one marker line and no error. The same classes on the contract, spec and stage consumers, observed on the base first; every consumer that prints its marker on a failing run at the base receives the mechanism and passes the same matrix on the tip. The mechanism, its Lean 4.22.0 API and the reason it sees earlier commands' errors are recorded, with the per-command message-log reset (`Lean.Language.Lean.process.doElab` sets `messages := .empty`) shown to blind a naive check. | consumer file -> `lean` frontend exit code and printed marker -> builder replay consumer stage (`Test-CaseVerdict` marker absence) and the builder and contract gate checkers (exit 0 plus marker) | (a) Base reproduction of every class on every consumer: a class for which the base prints no marker is recorded as non-discriminating for that consumer. (b) A mechanism that also suppresses the marker on the unchanged file would pass every negative: positive control per consumer. (c) An error after the marker command (trailing check). (d) An injected edit that does not actually fail as intended would make a negative vacuous: each negative requires an error at the injected line and its class diagnostic. (e) The registered line sets must stay exact: B16-B18 and every consumer case replayed with the marker-absence matcher. (f) An explicit placeholder in an unreferenced declaration is a warning, not an error, so the marker may print: recorded boundary. | None at freeze | OPEN |
| REQ-PRE-R2-HALTS | Verbatim section above | Local rung (audit P2-2) | Registry cases (i) `halts` replaced by a proposition that every program's run satisfies at fuel 0 and that no longer names the halted status, with the producer proof adjusted in the same fragment, and (ii) `halts` at the literal budget `2000000000 + 2000000000 * xs.length` with a proof through `RunsTo.fuel_extension`; both `profile: capstone`, both producers build, both rejected at the capstone consumer with an exact registered line set (expected at the two `check_*_halts` proof lines). Reproduction on the base of P2-2 by a probe: `work_literal_is_fuel` for every program and state, `empty_program_work`, `empty_program_never_halts`. The fuel-triviality of `work` and the reading "halts together with work at the pinned linear fuel is the linear-work content of REQ-PRE-COST" recorded in `repair-r2/REPORT.md` and the appended REPORT.md section. | `BuilderRunFacts.halts` -> `comparisonRunFacts`/`wordRunFacts` -> `ConstructionAndQueryCapstone.comparisonRun`/`wordRun` -> capstone consumer `check_comparisonRun_halts`, `check_wordRun_halts` | P (accepted): `∃ outBase, (run program (builderBudget xs.length) s0).final.status = .halted outBase`. Q1 (mutant i): a proposition true of every program at fuel 0 without the halted status; Q2 (mutant ii): the same halting at a strictly larger literal fuel (implied by P through fuel insensitivity, not implying P). The consumer types pin P at `builderBudget xs.length`, so each mutant must fail at those lines while its producer builds; a mutant rejected at the producer would not exercise the consumer. | None at freeze | OPEN |
| REQ-PRE-R2-RUNSAFE | Verbatim section above | Local rung (audit P3-4) | A registered `Safety.lean` case with `"manifest": "rehash"` whose mutant `Run.Safe` is a strictly weaker proposition, whose producer closure still builds, and which is rejected at the exact builder consumer line set of `safety_run_safe_definition` (the `Iff.rfl` pin). If dropping the post-state fit conjunct stops at the producer, the reason is recorded and a different genuine weakening is registered. | `Run.Safe` (`Safety.lean`) -> `Run.Safe.of_transitions`, `Run.Safe.not_fault`, `Run.Safe.final_fits` (`Compiler.lean`) -> builder consumer `safety_run_safe_definition` | P: `∀ t ∈ r.transitions, Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W`. Q: a strictly weaker body. A definitionally equal restatement is not a weakening and would pass the pin; a weakening that the producer rejects never reaches the consumer; both are checked. | None at freeze | OPEN |
| REQ-PRE-R2-RECORDS | Verbatim section above | Local rung (audit P3-1, P3-2) | Dated amendment entries appended at the end of CONTRACT.md (the Version 3 section is the last section) and of AMENDMENTS.md quoting the superseded V3-7 (ii) text and citing PRE-1-A2 P3-1, plus the contract consumer marker change; BUILDER_REPLAY_DESIGN.md corrected in the four stale places and everywhere the R2 runner or registry change makes stale; `Test-CaseVerdict` requires the profile marker absent for consumer rejections, with self-tests rejection-with-marker (false) and rejection-without-marker (true); registry version 2, content pin updated in the runner (the only live pin; historical records at 84ae12f and a0c93e9 are not pins) and listed old and new. | registry -> runner pins -> `Assert-Registry` -> full replay | (a) The matcher change must fail a rejection that prints the marker: self-test fixture and B16-B18 on the tip. (b) A stale pin anywhere: `git grep` of the old content hash at the tip shows only historical records. (c) The amendment must not edit earlier text: CONTRACT.md and AMENDMENTS.md base blobs are prefixes of the tip blobs. | None at freeze | OPEN |
| CHK-PRE-R2-VERIFICATION | Verbatim section above | Verification | Exact commands in the coverage plan below, each with command, host, duration, deadline, mutex wait and exit. | All R2 rows and the inherited rows' preservation | A setup failure, timeout or partial run is recorded as incomplete, never PASS; the design check runs per commit and over the range; the aggregate gate is not claimed. | None at freeze | OPEN |
| REPLAY-EXACT-REGISTRY (runner change, marker controls) | Verbatim section above | Runner change and new control runner | Builder replay: version 2 registry, ordered IDs and content pin in the runner; the full replay reports executed = expected in registry order. Marker controls: `marker_controls.json` version, ordered IDs and CRLF-normalized content pin in the runner; receipts report executed and expected IDs; registry cases (removed case, reordered cases, changed version, changed content) exit 1 before any case. | Registry -> runner -> receipt | A registry change without the pins, or a lost case, must fail before any case runs. | None at freeze | OPEN |
| REPLAY-SELECTOR-NONVACUITY (runner change, marker controls) | Verbatim section above | Runner change and new control runner | Builder replay selector-boundary self-test on both hosts (nine fixtures, unchanged). Marker controls: omitted selects every case, a valid ID executes exactly that case, bound empty, whitespace, malformed, unknown and duplicate selectors exit 2 before any case, tested through real child invocations. | `-OnlyCase` / `-Case` binding -> selected IDs -> verdict | A child that selects nothing must not exit 0. | None at freeze | OPEN |
| REPLAY-SUBPROCESS-DEADLINE (runner change, marker controls) | Verbatim section above | Runner change and new control runner | Every Lean, Git and child invocation through `Invoke-RMQOwnedBoundedProcess` with a positive deadline and output ceiling; exits and error lines kept in receipts; copies outside the repository removed in `finally`; repository state digests equal before and after each case; the builder replay deadline self-test on both hosts and the marker controls descendant sleeper. | `scripts/owned_process_tree.ps1` -> runners -> receipts | Under the MSIX-packaged pwsh 7.6.6 the kill-on-close job does not hold descendants (NATIVE-1-R1 and PRE-1-R1 host finding): there the marker-controls deadline case reports INCONCLUSIVE and the PASS must come from Windows PowerShell 5.1. | None at freeze | OPEN |

## Inherited rows

### The 31 frozen PRE-1 rows

Frozen source: the row-content byte strings of
`a0c93e9cf4d3c93856f5756ff6a7271da2b821ff:docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md`
(blob `166a048000d4f5de9d19b7a3bd9f1a3f270efae1`, 125,544 bytes, SHA-256
`3DFAEA0A658DAA54F68BE197A1614DAB65D6B14B1BD5C73027027229C5021C87`), frozen at
`26d6b5c2b10ed06ae4f72d9075d746ede987bdab` (that commit's 37,510-byte blob is a
byte prefix of the base blob, and the first row of every ID below is
byte-identical in both). Each ID has the frozen row and the author's
final-candidate review row. SHA-256 values are of the exact UTF-8 row bytes
without the line feed. The whole matrix file does not change in R2.

| ID | Rows at the base (line: SHA-256) |
| --- | --- |
| REQ-PRE-CONTRACT | 66: `3B62C7B8B5097FE118F5CBD0B315C9C7635C590D99964460B96D0DEC85CE2289`; 732: `EBCF5A8FC946288E69A7199EA98EA2890E452ADAEA7ED2FB279DC9FCC3400B68` |
| REQ-PRE-INPUT | 67: `9C14FEF0E4CA9FE8B1F20B9C5F5A1589038486B4D8A5370B50A1DC706B729F79`; 733: `E6E18985966D6D4770C0129CC9F793EBB8A49332CD94889F8FC3ED4942CCA1A5` |
| REQ-PRE-MACHINE | 68: `F47A6CE5264E3F56FC8986F5540F6B6DE6C3A393E090B7BCFCA7E80873AF9E39`; 734: `2C83EA02740168500A71C4874EFFB41466D63AF186057A899B6C2163A0720E13` |
| REQ-PRE-EXACT | 69: `34D9F1690D377345D7613934E266879FF110937F8FBD482F93D06A145D6B65F4`; 735: `96168E27E7066D680D8130061F3071B80B84153A2D20FCA9556763C433250D1E` |
| REQ-PRE-COST | 70: `CE9AFA3D7C2F159240D359B84DE80A73E0C5B61E419FE70DCB2D719A1B951C61`; 736: `F623DB22B105F99D734CE29AE531922D60FE411523BAF50C0F11D75F85DB4900` |
| REQ-PRE-JOIN | 71: `87E11BBB79F9EF2099F207EC895144C5ED7C9B25A769BAF64B561A8707D95DAE`; 737: `2010323B12472E4AE52A26B84D70C07E33E1921D5C8B154F6DD7DCBFBD5E9928` |
| CHK-PRE-CONTROLS | 72: `D7DBA36F66B516F62C335623974F76273F15CD07AA937FE97BE064B0EFCE2F9E`; 738: `EB57BBC971CF821996A48137F026134E5683C0180634D455E670ECA0AD24E493` |
| REPLAY-EXACT-REGISTRY | 73: `339E05378F56C3C3DC82379933A11851FD162C62DD5F911B2BCF439FD547BA22`; 760: `B215E8E4830F5FDF1B2D35605931706EC9A8A75E3028F116CBAE4B12803987C4` |
| REPLAY-SELECTOR-NONVACUITY | 74: `233B5DB369277E4D01FA134FBBE28D28332D7557E888344A66F6451AA833FC68`; 761: `5FDC44753B3494B218DCAE4B38A95A75AE29D0B9F9F2AF869DFB828E7499BE73` |
| REPLAY-SUBPROCESS-DEADLINE | 75: `6EAA02BC5ADC3D90FCA47AD2D3F98D4F1F71769C26FFB7E5C7EBA8802086B8EA`; 762: `2924B56080E324080865EA2BC65755221EBA321DA12612561AFB2EFD93665C74` |
| INV-STORE-IDENTITY | 117: `C0DB752A84EE43870793AE4F71A07F6B5ED2753AA0A93EA3F478DC07FF819B73`; 739: `1A8D7E0A29AFAA3959D690E05C9CD4650ECE168B5EE276A3ADB15B21A8CF7B32` |
| INV-VALUE-DEPENDENCY | 129: `DEFD35955CA28FADBBE8F97E05A64ACD919075D1C10A139497B7204838F93D95`; 740: `F0566F1BF174772460CF83AB5056AA5205453D48819175972D8F97AFB7B71842` |
| INV-SEMANTIC-NONVACUITY | 141: `08E9F72489FFB1261E9979E57FB651001F4C68F1D6C7B46187B78C77F02CDFFB`; 741: `9E47F4895280925BB383F83C30873F9CBD3D1ADA08F27390F25AA47F77F4AC5D` |
| INV-TRACE-EXECUTION | 150: `5292424C3ECFD99F1ED9F13AE07619BB4C55088F1BFC188EDA522EC2CBB560C9`; 742: `9095A50EB8E980BBED8353063FF2DFAF72F0D259D6213DC0BA36B1909F4F5272` |
| INV-STORE-AGREEMENT | 159: `B58230F088D9ED4C7B7481AC37EA6207D72A9814670EEF6046B9513D59DA92C7`; 743: `428E67D59558107367CF5408FC19AB0419A3797576509D03422EC2766DF22598` |
| INV-READ-BACKING | 168: `84D1CC23C85A5F9E3B5B83CA03555A900A3B6DBBEC954B2E8EEC3C28E8BB7EAC`; 744: `E05D7A779CB58AD0EEE04940E7E225C6CC8F08075E0E5AD60F9DBBE86B73FC6C` |
| INV-WORD-WIDTH | 177: `214C287B2BAB64A0A793713766B58E19344C7C7C659B42879B40A0282B532007`; 745: `935285DE6DFC8C2DC30536FB76F29CA19FC6DBDE9C873BD44CD8933D5A9040CF` |
| INV-ADDRESS-WIDTH | 188: `6BE8FDDDBBCB3FF3C70C23DC003165B0F90A05B3BDF5A5FC43C3AA03D0A8C06D`; 746: `944AD7BBCC35E8656F458F7514A6933AE0B7F9272FED0882374E39D90C90FD6D` |
| INV-INSTRUCTION-ATOMICITY | 200: `50AA4C05D1B22DBE127738457F2453197C663817F0DA26F0C137C0A0650BF504`; 747: `5715E32EABEE1C0C3AC4D6991244F340E2AB2CE1BCFE8CF32059DF45C586A2C9` |
| INV-PROGRAM-ACCOUNTING | 211: `DEC1293C910F26C895E98C66E2CBB3F184F8AD37047E202E73B71AA068F37DF1`; 748: `088C559CFCD3B0420813192ECDBF1049E35D61D5B1AC099F96CFB6773481A8B9` |
| INV-ORACLE-INDEPENDENCE | 221: `A902941BDBB00A5254DC87F3A3CC703E5D19A9AE5CC66FB18E3478BB87EC3EE4`; 749: `0D70E9D392DA28C3B1F3552A288BCA08E0223A660BFA36FCB5480B049B7A07E9` |
| INV-VALIDATION-REACH | 231: `95B8F20BE080E9043CEDD8503BD32E01B8A1C40EBB63FC51E59FE6267A696A7C`; 750: `A7406C1813F7EDFB72A85B15C3AC432C992362BD712E76B106B5914CA75026F5` |
| INV-ALL-SIZE | 240: `EAF33C70429627AEEC5AC4081F4027F6DDFDDA3497575DA2D328F7BFA188914F`; 751: `1543F4B3EF311ACECB17B7F54E73877B3D80F9029847B81655194B0C4EDAD380` |
| INV-PROOF-SEPARATION | 249: `4DB21972BA5ACAA4AA706DEDF9C985FAA1381EDF1342925A0844BC59D820A9DB`; 752: `B27A428138C200E9F718253149A31AF1B02ACD67B950BC42B105D5481B5C1107` |
| INV-NO-SYNTHETIC | 258: `F553CDCEC5C5431BE0B97DA460D0B2ADA819F5FECC0479B7C7A0A8E7E5F7F048`; 753: `564C676E2BEA9F4464A48B23F09E24544AED96AB25ED85D4469FCFF5804757B3` |
| INV-CATEGORY-SEPARATION | 267: `770F13D28993D6D27690D063CFFB3FE9ED89917B6995AF6711E8B1436EEF85D0`; 754: `0DF3749B620C1298518F15A299000CC6EE21889ECCF93B0B6CB10D52F13409CB` |
| INV-PUBLIC-COMPOSITION | 278: `F7242FF4B8DF07F133AEA94930D16E5BE98369CB0A40C1167412751A2701C286`; 755: `73E05E6AFBF41E14A7CD974B52A1F2B3BC1CC56601B3E6D491A04E161D7C4E01` |
| INV-CERTIFICATE-ANTI-BYPASS | 290: `A11C37A91C02824611DA6636D7B179116E00B0CBBDDA636126BFBA0338B08CE6`; 756: `43E1BA48DC5B26BA64EBD9152C86CD0A04ED3AC853E8C732E78CF79A20F9FF6C` |
| INV-MUTATION-REPRODUCIBILITY | 305: `7BABCEDE16EE7695C50A21801E4E1B0579A36297F5CD0D3CD0C2D75FFC0C5FE7`; 757: `F74DC08CF773F0B1F47B35C3D95AA0ADA686BA40B129B627D0917738E255C2EB` |
| INV-GLOBAL-PHYSICAL-MACHINE | 316: `ABE5789CDDE4E0615400B428C478FB3F2B55EBFF4B1998301D48FA15E0635EB8`; 758: `2146E7C76B2A1EB9CFA9ADC847F5423FA13ADB8E53B237082EF5CA34CFE412B2` |
| INV-WIDTH-SCALING | 328: `A69B27F0C6EBF10D6B7B45847EE396F72FC5B17314CFC5B0A276A8C14FDFD0FC`; 759: `7D830CDEB2773EF157FE1EA511D8E7842ED07DB0B6E4662195C035DAB3DBEFED` |

### The five PRE-1-R1 rows

Source: `a0c93e9cf4d3c93856f5756ff6a7271da2b821ff:docs/internal/extensions/pre1/repair-r1/ACCEPTANCE_MATRIX.md`
(blob `8afedb2a3cfbb6d8ae159d0aef4b57827cf13ca4`, 40,623 bytes, SHA-256
`305A35019DF93CDECB13E1D2F8AB252DBBFE40F2CD06A4E78DC6317A5D77630E`). For each ID:
the verbatim requirement paragraph (line and SHA-256), the frozen row and the
evidence-appendix row. The file does not change in R2.

| ID | Requirement paragraph (line: SHA-256) | Rows (line: SHA-256) | Still-holds check at the R2 tip |
| --- | --- | --- | --- |
| REQ-PRE-R1-SELFTEST | 35: `35801526FA2D0CED23A4C438F27F58476A6B8D51A31FC7B9791DFB6E7E45AA1A` | 74: `F3C7C9E22EE5B3A3A4FB8B8B049A4FD5F884B4617BFE4D7693F686FE09470A18`; 253: `F7B7EEFB6E430F847C2145C1F09019BC91061E5C9E4290051CA23680F2BC9BD6` | `repair-r1/run_claim_scans.ps1` on the clean tip: strict and records scans exit 0 with 0 strict failures, self-test exit 0 with its exclusion counts equal to the two summaries, detector CLEAN |
| REQ-PRE-R1-ARCHIVE | 39: `ACFB436151169D1D74E638BCAC5AE9D9E8F19E0DC5BC7A3638576AFF0822C9B6` | 75: `C498D29286D18C6E8B9994489A84310F3A62A0C6BCADC3E0DD2D508B1CD8550E`; 254: `D0572DC49B3F24E20A3B390061E8E27CECDB18837ED8D1C90DE1C4DBB1AC410D` | `verify_receipt_archives.py --committed <tip>` exit 0 |
| REQ-PRE-R1-REWORD | 43: `E811FA9C4041C5681C2C28BD1309EA8A201018F4DD716024C31A0C691DBDAEDD` | 76: `D55359499848385E3D7429B9DAAEEEC830143DBA720812FEE2A601A289E90851`; 255: `AD8F8F011E575A66E9928E2171FFD7A4CB0AABCD811F0D992EB56ADD0261F2EF` | `verify_rewords.py --committed <tip>` exit 0 (R2 only appends after the last base line of BUILDER_STAGE_LOG.md and REPORT.md) |
| REQ-PRE-R1-PRESERVATION | 47: `6999F7046BACCAE3E500293A19F284E69C3292F3472AF02193BA9E22378E030F` | 77: `E892A23892200FB01053274AD5294AB674DCE50C3F3371D3C8FEC065D170B988`; 256: `6146C2B05471B4F110D37203B17C09DC43942C7C67486D3CE99AD1F424F2CA46` | `check_preservation.py --head a0c93e9cf4d3c93856f5756ff6a7271da2b821ff` exit 0 (the R1 range); at the R2 tip the R1 files, receipts and matrices are unchanged (`git diff --name-only a0c93e9..<tip> -- docs/internal/extensions/pre1/repair-r1` empty) |
| CHK-PRE-R1-VERIFICATION | 51: `4FC2C5AA8289DF7C4D7A3C5BE17B3BD071C983601B93AB36322ADEF650D6CFB4` | 78: `00B7C578D214A0F962946F6613AEA676893CE3E32AC3F94076AC7370CA546978`; 257: `2C529E16F58605B90501C96FE7CC5E1933A36778A07E104C8B8E483C9A757BDB` | the two verifiers and the detector rerun on the tip; the R1 control registry and receipts unchanged |

## Scope reading recorded at freeze

- The prompt's file list names the verdict-marker command of
  `scripts/preprocessing_contract_check.lean` conditionally and does not name
  `scripts/preprocessing_spec_check.lean` or `scripts/preprocessing_stage_check.lean`,
  while REQ-PRE-R2-MARKER requires the same mechanism for any of the three that
  prints its marker on failure. The frozen requirement governs: for each of them
  that the base reproduction shows printing its marker on a failing run, R2
  changes that file's verdict-marker command (and its explanatory comment) only,
  at the end of the file, so no earlier line moves. This reading is reported to
  the coordinator.
- REQ-PRE-R2-HYGIENE's line-count sentence is read as a property of the
  docstring rewording: the rewording replaces two lines and moves nothing. The
  verdict-marker command at the end of the same file grows, which moves no line
  before the verdict section and no registered surface; the old-to-new line
  mapping is the identity up to the verdict section and is recorded.
- REQ-PRE-R1-PRESERVATION constrains the R1 range `84ae12f..a0c93e9`; at the R2
  tip it is re-established by rerunning `check_preservation.py` with head
  `a0c93e9`, while the R1 archive and reword verifiers and the claim-scan
  detector are rerun on the R2 tip.

## Verification coverage plan (frozen before repository edits)

Mutex policy: every command expected to exceed five minutes blocks on
`Global\RMQHeavyVerification` in a pwsh queue and records its wait; the
queue script `r2tools/queue.ps1` (scratch) runs each step as an owned bounded
process and records command, host, start, duration, deadline and exit.

| Role | Command | Rows | Unique failure mode | Tree | Expected runtime / deadline |
| --- | --- | --- | --- | --- | --- |
| Development (reproduction) | both gate hygiene commands | HYGIENE | the base must show the line-12 hit | base, clean | seconds |
| Development (reproduction) | `run_marker_controls.ps1 -Observe` (scratch copy, byte-identical to the committed one) under Windows PowerShell 5.1 | MARKER | which consumers print the marker on which failure classes before any edit | base, clean | about 45 min; per consumer 900-3600 s, queue 10800 s |
| Development (reproduction) | `scripts/preprocessing_builder_replay.ps1 -OnlyCase B16_PROGRAM_PARAMETER`, `B17_PROGRAMWORD_PARAMETER`, `B18_EFFICIENTBUILD_RELOCATION` (pwsh) | MARKER, RECORDS | the in-registry marker-on-failure outputs the audit reported | base, clean | about 300 s each; 3600 s |
| Development (reproduction) | CAB2 and CAB4 producer mutations in a disposable clone at the base (`.lake/r2-copy`, build copied, no-op rebuild checked) | MARKER | the audit's capstone probes with maximum-recursion-depth errors | clone at base | about 300 s; 7200 s |
| Development (reproduction) | `lake env lean` of the P2-2 work probe; registry scan for `halts` and `Run.Safe` cases | HALTS, RUNSAFE | `work` true of every program; no case touches `halts` or the `Run.Safe` definition | base | seconds |
| Development | focused `-OnlyCase` runs of every new or changed case, and B16-B18, on the repaired tree | HALTS, RUNSAFE, RECORDS, MARKER | exact surfaces and restoration before registration | repaired commit | 300-700 s each; 3600 s |
| Development | `-RegistrySelfTestOnly` on pwsh 7.6.6 and Windows PowerShell 5.1 | RECORDS, REPLAY-EXACT-REGISTRY | matcher fixtures and registry pins | repaired tree | seconds; 300 s |
| Final-required | `scripts/preprocessing_builder_firewall.ps1`; builder replay `-RegistrySelfTestOnly`, `-SelectorBoundarySelfTestOnly`, `-DeadlineSelfTestOnly` on pwsh 7.6.6 and Windows PowerShell 5.1 | CHK, REPLAY-* | firewall and self-tests on both hosts | tip | minutes; 300-600 s |
| Final-required | full builder replay (pwsh, no selector) | HALTS, RUNSAFE, MARKER, RECORDS, REPLAY-* | every registered case with executed = expected, validator stage | tip, clean | 5,000-9,000 s; 14,400 s queue deadline |
| Final-required | full contract replay (pwsh) | CHK, inherited contract rows | the 18-case contract registry with the changed contract consumer | tip, clean | 290-400 s; 3600 s |
| Final-required | `lake build` of the capstone, `RMQ.Validation.PreprocessingContract`, the producer targets of the five consumers and `rmq_preprocessing_validate`; `lake exe rmq_preprocessing_validate` | CHK | build and validator on the tip | tip | incremental minutes; validator 270-460 s; 3600 s |
| Final-required | all five consumers `lake env lean` (exit 0, one marker line) | MARKER, CHK | the committed consumers themselves | tip | 10-600 s each; 3600 s |
| Final-required | `run_marker_controls.ps1` full registry on Windows PowerShell 5.1, and the non-Lean cases on pwsh 7.6.6 | MARKER, REPLAY-* | the committed control matrix | tip | about 90 min; queue 14,400 s |
| Final-required | both hygiene commands; `verify_receipt_archives.py --committed HEAD`; `verify_rewords.py --committed HEAD`; `check_preservation.py --head a0c93e9` | HYGIENE, inherited R1 rows | trust hygiene and R1 preservation | tip | seconds to a minute |
| Final-required | `claim_drift_scan.ps1 -Strict`, `-Strict -IncludeProcessRecords`, `-SelfTest` and `repair-r1/claim_scan_detector.py` over the two strict logs | CHK, REQ-PRE-R1-SELFTEST | zero emitted result lines with the summary pattern | tip, clean | 20-30 s each; 3600 s |
| Final-required | `git diff --check`; `git diff --check a0c93e9cf4d3c93856f5756ff6a7271da2b821ff..HEAD` | CHK | whitespace in working and committed bytes | tip | seconds |
| Final-required | `scripts/design_decision_check.ps1 -Strict -Base <parent> -Head <commit>` per new commit and `-Strict -Base a0c93e9cf4d3c93856f5756ff6a7271da2b821ff -Head <tip>` | CHK | each commit carries its own ledger entries | each commit, range | seconds; 300 s |
| Coordinator-owned, not run | `scripts/gate.ps1`, full default `lake build`, continuation audit | node closure | aggregate certification | tip | coordinator schedule |

## Status at freeze

Every R2 row is OPEN. The inherited rows are preserved, not re-proved, except
where the R2 change touches their evidence (the builder registry, runner and
consumers), which the tip's full replays and consumer runs re-establish.
Acceptance, the continuation audit and the aggregate gate are coordinator steps.

## Freeze-time reproduction (evidence, recorded before this matrix was committed)

All on the clean base `a0c93e9cf4d3c93856f5756ff6a7271da2b821ff` with the pinned
toolchain and LEAN_NUM_THREADS=1, after a cold `lake build` of the five
consumers' producer targets and `rmq_preprocessing_validate` in this worktree
(pwsh queue under `Global\RMQHeavyVerification`, mutex wait 0.0 s, 1964.7 s,
exit 0, 590 jobs). No repository file was edited; the reproduction tools were
scratch copies that the implementation commit adds byte-identical under
`repair-r2/` (SHA-256 below). Heavy steps ran in one pwsh queue (mutex wait
0.0 s, held 04:31:24-05:07:07 host time).

- P1-1 (hygiene). `rg` with the gate's line-374 pattern and eleven roots prints
  exactly one match, `RMQ\Validation\PreprocessingContract.lean:12` (the
  docstring word), exit 0; the line-377 command prints nothing (exit 1).
- P2-1 (markers), control matrix `run_marker_controls.ps1 -Observe` (runner
  SHA-256 `0114caf775dee83a150111b4246ad1543b082785516d53f2ca7547bd13e12dd2`,
  registry `11abd16938cbd0537a35460bdc203b50052bc5523b31847dc315aeec31aad81a`,
  33 consumer cases) under Windows PowerShell 5.1.26100.9444: 1273.5 s, exit 0,
  every case completed and exercised (its registered diagnostic and an error at
  the injected line), every copy removed and the repository state unchanged
  after every case. Observed on the base:

  | Consumer | unchanged | (a) example | (b) `#guard` | (b) `run_cmd` | (c) max recursion | (d) unknown identifier | (e) unreferenced | after marker |
  | --- | --- | --- | --- | --- | --- | --- | --- | --- |
  | builder | exit 0, marker | exit 1, marker | exit 1, marker | exit 1, marker | exit 1, marker | exit 1, no marker | exit 1, marker | exit 1, marker |
  | capstone | exit 0, marker | exit 1, marker | exit 1, marker | - | exit 1, marker | exit 1, no marker | exit 1, marker | exit 1, marker |
  | contract | exit 0, marker | exit 1, marker | exit 1, marker | - | exit 1, marker | exit 1, no marker | exit 1, marker | - |
  | spec | exit 0, marker | exit 1, marker | exit 1, marker | - | exit 1, marker | exit 1, marker | exit 1, marker | - |
  | stage | exit 0, marker | exit 1, marker | exit 1, marker | - | exit 1, marker | exit 1, no marker (one error at the marker line) | exit 1, marker | - |

  Every consumer prints its marker on a failing run in at least four classes,
  so REQ-PRE-R2-MARKER applies the mechanism to all five (the contract consumer
  by a contract amendment entry). Class (d) is non-discriminating on the base
  for the four witnessed consumers: the witness already collects the placeholder
  constant from a recovered unknown identifier. Durations per run: builder about
  4 s, capstone about 38 s, contract about 3 s, spec about 28 s, stage about
  110 s.
- P2-1 in the registry: `scripts/preprocessing_builder_replay.ps1 -OnlyCase`
  (pwsh 7.6.6, runner SHA-256 `efb4666bc339f267...`, registry content
  `0bc1fba4...`): B16 252.0 s, B17 243.5 s, B18 245.6 s, each exit 0 with
  verdict PASS and restoration EXACT; in each the consumer stage exited 1 with
  exactly the registered line (370, 371, 352) and its output contained
  `PRE1-BUILDER-TYPED-CONSUMERS PASS` (evidence directories
  `.lake/preprocessing-builder-replay/20260914-045239-...`, `-045650-...`,
  `-050054-...`).
- P2-1 capstone probes (disposable clone `.lake/r2-copy` at the base with the
  worktree's build directory copied; `lake build` of the capstone was a no-op in
  8 s): CAB2 (`queryOnEmitted` over `buildMemory xs`, proof
  `packedQueryOn_of_eq xs _ rfl`) producer exit 0, consumer exit 1 in 39.9 s with
  error lines 485, 487, 494, 498, 503, 505, 511, 516, 522, 528, 535, 540, 548,
  554, 567, 569, 579, 591, 601, 609, 615, 621 and the witness at 1073, 17
  maximum-recursion-depth errors, and one marker line; CAB4
  (`headerUseWord : HeaderUse builderProgram`) producer exit 0, consumer exit 1
  in 36.4 s with error lines 146, 150, 154, 170, 190, 197 and 1073, six
  maximum-recursion-depth errors, and one marker line; both restored byte-exactly
  and rebuilt; the restored consumer exit 0 with its marker; clone status clean.
  These are the audit's line sets.
- P2-2 (work). `lake env lean` of the scratch probe `p2_2_work_probe.lean`
  (SHA-256 `ded5496470e92a5eb7faeccd17fa260277864430cceddef3e6ef3754f57fdd86`),
  1 s, exit 0: `work_literal_is_fuel` (every program, state and list: steps at
  fuel `builderBudget xs.length` are at most `1000000000 * xs.length +
  1000000000`) with axioms `[propext, Quot.sound]`, `empty_program_work` the
  same, and `empty_program_never_halts` (the empty program's run on
  `comparisonInputState xs` at that fuel never has status `.halted`) with
  `[propext]`. A scan of the 52 base cases finds no `before` or `after` text
  containing `halts`, no case touching `def Run.Safe` (B36 changes only the
  `compile_safe` statement), and B45 as the only `work :` case.
- Mechanism trials before the design was chosen (scratch, import-free toy file
  and scratch consumer copies): a final command reading `(← get).messages` sees
  no earlier command's error in any class (the naive check is blind); the
  witness-and-`sorryAx` check misses classes (a), (b), (c), (e) and a trailing
  error; an in-process re-elaboration of the file text with the marker command
  blanked sees every class, including CRLF input and an error after the marker,
  and leaves the unchanged file's marker. On scratch copies the builder consumer
  took 3 s unchanged and 9 s with the mechanism, the capstone consumer 36 s and
  73 s, and the builder copy with an injected maximum-recursion declaration
  exited 1 without the marker.
- `Run.Safe` weakening trial (scratch file importing `Compiler`): a copy of the
  definition with `Prim.Safe W (program.length + 1)`, a proved monotonicity
  lemma and a coercion lets the unchanged proof texts of `of_transitions`,
  `not_fault` and `final_fits` elaborate, and only the `Iff.rfl` pin shape fails
  (type mismatch).

## Evidence appendix (worker review, second session, 2026-09-17)

Appended; nothing above changed. Evidence for the frozen R2 rows on the repaired commit `341bc2803dc26a123c48b1b8d0566e5e1583de7a` and the receipt chain that follows it (every later commit changes only `docs/internal/` receipts, ledger entries and appended sections, plus one commit under coordinator ruling R-R2-1 raising the builder gate checker's deadline); the worker's command ledger is the R2 section of BUILDER_STAGE_LOG.md and the receipts are under `repair-r2/receipts/`. "Met in worker review" is not acceptance: the continuation audit, the coordinator aggregate gate and acceptance remain coordinator steps.

| ID | Evidence (repaired commit `341bc28`; verification on the receipt chain) | Worker status and residual |
| --- | --- | --- |
| REQ-PRE-R2-HYGIENE | At the tip both gate commands print nothing (rg exit 1) over the eleven and ten roots; the base reproduced exactly one match at `RMQ/Validation/PreprocessingContract.lean:12`. Lines 1-1070 of that file differ from the base only at lines 11 and 12 (the reworded docstring, two lines for two lines); the file grows from 1206 to 1246 lines only after line 1070 (the verdict section), so every registered capstone surface (at most 428) and every capstone-profile registry line (227, 231, 275, 290, 306, 349, 353, 397, 412, 428) is unchanged; the same pattern over every added line of the range under the gate roots finds nothing. | Met in worker review |
| REQ-PRE-R2-MARKER | Mechanism in all five consumers (DD-20260914-PRE1-R2-001; CONTRACT.md V3-10a): the marker command re-elaborates the file's own source text in-process with itself blanked (`Lean.Parser.parseHeader`, `Lean.Elab.processHeader`, `Lean.Elab.IO.processCommands`) and requires `MessageLog.hasErrors` false for the header and the returned command state, whose `messages` is the fold of `diagnostics.msgLog` over every snapshot of the tree (`Lean/Elab/Frontend.lean` lines 94-122 of the pinned toolchain; `Lean/Language/Lean.lean` line 749 resets `messages := .empty` per command, which is why a later command cannot see earlier errors from its own state). Control matrix on the tip (receipt `q3-marker-controls-26b175e-ps51.json`, Windows PowerShell 5.1, 45 of 45 PASS): for every consumer the unchanged copy exits 0 with exactly one marker line and no error, and classes (a) example, (b) `#guard` (plus `run_cmd` for the builder), (c) maximum recursion in a witnessed declaration, (d) unknown identifier in a witnessed theorem, (e) unreferenced failing declaration, and a trailing check after the marker exit 1 with zero marker lines and the class diagnostic at the injected line; the base observation table in the freeze section records the markers printed before the repair. Import-free toy variants on the tip (Q5, the eleven variants of `tools/mechanism_toy.lean`): the base and CRLF variants print the marker with exit 0, the eight failing classes including a wrong `end` suppress it with exit 1, and the unreferenced explicit-placeholder variant (a warning, not an error) prints it, the recorded boundary. | Met in worker review |
| REQ-PRE-R2-HALTS | B53 (`halts` becomes `∃ fuel, (run program fuel s0).final.status = s0.status`, proof `⟨0, rfl⟩`: true of every program at fuel 0, no halted status) and B54 (`halts` at the literal `2000000000 + 2000000000 * xs.length`, proof by `RunsTo.fuel_extension`) registered, capstone profile; focused runs and the full replay reject each at exactly `PreprocessingContract.lean` lines {227, 349} (`check_comparisonRun_halts`, `check_wordRun_halts`, which pin `∃ outBase, (run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status = .halted outBase` and its word twin) with the capstone marker absent while the mutant producer builds (Capstone target 16.7-19.9 s); restored consumers exit 0 with the marker. P2-2 probe on the tip (Q5, 1.6 s, exit 0): `work_literal_is_fuel` and `empty_program_work` on `[propext, Quot.sound]`, `empty_program_never_halts` on `[propext]`. The fuel-triviality of `work` and the reading of `halts` together with `work` at the pinned fuel are recorded in the appended REPORT.md section. | Met in worker review |
| REQ-PRE-R2-RUNSAFE | B55 (`Run.Safe` bounds each transition's `Prim.Safe` by `program.length + 1`; `Prim.SafeAt` bounds `.jump` and `.branchZero` targets by that length, so a jump to one past the program end is admitted: strictly weaker, and `Prim.Safe.succ_length` proves the forward implication) registered with `"manifest": "rehash"`; focused run and full replay reject it at exactly `preprocessing_builder_check.lean:457:` (the `Iff.rfl` pin `safety_run_safe_definition`) with the builder marker absent, the mutant producer closure builds (120-129 s), manifest and source bytes restored exactly. The prompt's example (dropping the fit conjunct) stops at the producer (`Compiler.lean` `of_transitions`, `not_fault`, `final_fits`), recorded in WDD-002 and BUILDER_REPLAY_DESIGN.md. | Met in worker review |
| REQ-PRE-R2-RECORDS | CONTRACT.md V3-7a/V3-10a appended at the end of the Version 3 section (its last section; base blob a byte prefix of the tip blob), AMENDMENTS.md entries appended likewise, both quoting the superseded V3-7 (ii) text and citing PRE-1-A2 P3-1. BUILDER_REPLAY_DESIGN.md corrected in the four stale places and in the places registry version 2 changes, and its gate paragraph follows the R-R2-1 deadline revision (`f7bdf20`). `Test-CaseVerdict` requires the profile marker absent for consumer rejections; fixtures `rejection-with-marker` (false) and `rejection-without-marker` (true) and their capstone twins are in the registry self-tests (58 self-tests PASS inside the full replay, 23 of them matcher fixtures; `-RegistrySelfTestOnly` PASS on both hosts in Q5); B16-B18 reject with the marker absent in the full replay. Registry version 2, content pin `3e27e7626f4af805820071777246d3a5c2ac101e7adbb3db028219b2f46ae495` replacing `0bc1fba4b974e05cd94830ff0d6038d6927d33b5928bb65587fc9a2dc166ffe7` (recomputed on the tip; the old value survives only in dated records). | Met in worker review |
| CHK-PRE-R2-VERIFICATION | Reproductions on the base recorded at freeze; on the tip: the builder firewall PASS; the registry, selector-boundary and deadline self-tests PASS on pwsh 7.6.6 and Windows PowerShell 5.1; the complete builder replay PASS 55 of 55 with executed = expected (8674.8 s wall); the complete 18-case contract replay PASS; `lake build` of the capstone, the capstone consumer module and `rmq_preprocessing_validate` and `lake exe rmq_preprocessing_validate` PASS (11 cases); all five typed consumers exit 0 with exactly one marker line; the marker control matrix 45 of 45 PASS on Windows PowerShell 5.1 and 12 of 12 on pwsh with the packaged-host deadline case INCONCLUSIVE by design (attempt 1 recorded as a setup failure); both hygiene commands with no match; the R1 archive and reword verifiers and the preservation checker PASS; `claim_drift_scan.ps1 -Strict`, `-Strict -IncludeProcessRecords` and `-SelfTest` through the R1 runner with the detector CLEAN (zero emitted result lines containing the summary pattern); `git diff --check` clean on the working tree and on `a0c93e9..HEAD`; `design_decision_check.ps1 -Strict -Base <parent> -Head <commit>` PASS for every new commit on its own except `3ce9b89` (two receipts committed without their ledger entry after an aborted assembly step; recorded in WDD-010 and BUILDER_STAGE_LOG.md R2-20) and PASS over the range from the base; every command with host, duration, deadline, mutex wait and exit in the R2 section of BUILDER_STAGE_LOG.md and the receipts. | OPEN in one clause: the per-commit design check fails for `3ce9b89` on its own (the range check passes and the following commit carries the entry); the coordinator-owned aggregate gate is not claimed; the closing commit's own checks are reported in the submission message |
| REPLAY-EXACT-REGISTRY (runner change, marker controls) | Builder replay: version 2, 55 ordered IDs and content pin in the runner; the full replay reports executed = expected in registry order (Q4: 55 of 55, `executedEqualsExpected` true in the digest); registry self-tests on both hosts PASS (Q5). Marker controls: version `PRE1-R2-MARKER-CONTROLS-V1`, 45 ordered IDs and content pin `11abd169...` in the runner; both attempt-2 receipts report executed = selected (45 and 12); the four registry mutations exit 1 before any case. | Met in worker review |
| REPLAY-SELECTOR-NONVACUITY (runner change, marker controls) | Builder replay selector-boundary self-test on both hosts PASS (Q5, nine fixtures). Marker controls (real child invocations on both hosts): omitted selects 45 (probe), `contract-unchanged` executes exactly that case, bound empty, whitespace, malformed, unknown and duplicate exit 2 before any case with no receipt or work directory. | Met in worker review |
| REPLAY-SUBPROCESS-DEADLINE (runner change, marker controls) | Every Lean, Git and child invocation through `Invoke-RMQOwnedBoundedProcess` with deadlines; exits and error counts in the receipts; copies removed in `finally` and the repository state digest equal before and after every case (45 of 45 and 12 of 12); the descendant sleeper's root and child absent after the 45 s deadline under Windows PowerShell 5.1; INCONCLUSIVE under the packaged pwsh host as pre-recorded. Builder replay deadline self-test on both hosts PASS (Q5, root and child absent on both hosts). Attempt 1 of the control run is recorded as a setup failure (work-root path length), not as a pass. | Met in worker review |

The 31 frozen PRE-1 rows and the five R1 rows: `docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md` and `repair-r1/` are byte-unchanged in the range; `verify_receipt_archives.py --committed`, `verify_rewords.py --committed` and `check_preservation.py --head a0c93e9` pass on the chain; the claim-scan runner's strict, records and self-test runs pass with the detector CLEAN on `341bc28` and on `9598f72` (rerun on the closing tip and reported in the submission message).
