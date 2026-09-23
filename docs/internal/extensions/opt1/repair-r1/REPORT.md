Status: INCOMPLETE
Phase: AWAITING_COORDINATOR_CERTIFICATION

# OPT-1-R1 repair report

Handle: OPT-1-R1. Task title: `(OPT-1-R1) Repair compiler replay certification`.
Exact base and proof frontier: `aecf4a580c591e8f694a3699e19e843198089194`.
Workflow governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Frozen requirement rows: `1f3a4199eaa95324cd1daaadbab89340ca8392c4`.
Branch: `codex/opt-1-r1-replay-certification`.
Worktree: `C:/Users/poin/.codex/worktrees/ccb1/RMQ` (`core.autocrlf=true`).
Durable mode: `WORKER_REPORT`.
Implementation-freeze commit (all production controls ran against it):
`f7cf20da8ae52c1f8295e5cedd4326bb8d44cbb3`. Evidence and this report follow in
the next commit(s) on the same branch; a report cannot name its own commit.

Every local implementation and replay obligation of the frozen contract has
executed evidence on the exact candidate. The remaining work is the expressly
external stage: the coordinator-scheduled aggregate `scripts/gate.ps1` slot,
the fresh exact-commit independent final audit, and coordinator acceptance.
No acceptance, merge readiness or publication readiness is asserted here.

## Identity of this continuation

The original Codex worker produced the uncommitted implementation, the frozen
matrix, the runtime repair leaf, the preservation checker and the canonical
build receipt, then stopped at a usage limit. The owner authorized a Claude
continuation in the same worktree and branch. The continuation ran the
project skill preflight against the exact governance commit (expected,
checkout, working and runtime RMQ skill sets all `rmq-audit-prompt`,
`rmq-coordinator`, `rmq-proof-sprint`; required `rmq-proof-sprint`; PASS),
re-read the frozen prompt (SHA-256
`38FD0E9E75A52CF37D2F4F0FD5A004506D5F3D1A1F38852255750E534BB408D9`), the
50,521-byte audit report (`4713191470F8795C83D16E3E62831D3348023691F58DA02227C54B4226A919E6`),
the coordinator disposition and the provenance review, and did not treat any of
them as authority to change the contract. It then verified every inherited
receipt before use. A second interruption occurred after the 49-case regression
had been launched under its own owned deadline; that campaign completed
unattended and was re-verified from its receipts before any later step.

## Changed paths (relative to `aecf4a58...`)

Production scripts (owned):

- `scripts/packed_optimized_runtime.ps1` (blob `aef90cc7...`, checkout SHA-256
  `69494710c3aaa873fdc3f915ba0dd67cfa449f40e2a9890dca126f9eade0f347`):
  `Assert-OPT1Rejected` repaired; `Invoke-OPT1RegistryTests` fixture gains both
  stream fields; `Invoke-OPT1Lean` sets `LEAN_SYSROOT` explicitly beside its
  private `LEAN_PATH`.
- `scripts/packed_optimized_certificate_replay.ps1` (blob `e1b38040...`):
  `Get-CImportSnapshot` rejects duplicate import records and module/source/
  artifact mapping drift; `Assert-CImportProvenance` consumes the pinned profile
  library and the literal receipt pin
  `$buildReceiptSHA256 = 'eed1ecee4a031a9c3cfcadea445307d8e15e70e732e6ffdd5b166d135292b64e'`
  (line 30), keeps the live raw hash map only for restoration, records
  `ReplayIdentity`, and rechecks the profile in `finally`; case libraries pass
  `LEAN_SYSROOT`; artifact roots moved to short `.lake/oc/<12 hex>` names.
- `scripts/packed_optimized_replay_profile.ps1` (new library, blob
  `5100f803...`): `Read-OPT1ReplayProfile`, `Assert-OPT1ProfileSourceEntries`,
  `Assert-OPT1ProfileToolchain`, `Read-OPT1ReplayBuildReceipt`,
  `Assert-OPT1ProfileArtifacts`, `Assert-OPT1ReplayProfile`,
  `Install-OPT1ReplayArtifacts`, `Build-OPT1ReplayProfile`.
- `scripts/packed_optimized_replay_regression.ps1` (new, blob `481cb967...`):
  49-case production regression, registry `opt1-r1-production-v4`.
- `scripts/packed_optimized_build.ps1`: in scope, unchanged.

Ledgers and public prose: `docs/internal/DESIGN_DECISIONS.md`
(DD-20260912-OPT1-R1-001 and follow-ups), `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
(WDD-20260912-OPT1-R1-001 and follow-ups), `docs/FAMILY_SUMMARY.md` and
`docs/DIGESTION_LOG.md` (one dated appended entry each).

Repair directory `docs/internal/extensions/opt1/repair-r1/`: `ACCEPTANCE_MATRIX.md`
(35 frozen rows + 4 repair rows, appended evidence and executed ledger),
`PROOF_IDENTITY.md`, `README.md`, `REGISTRY.json` (v4), `freeze-integrity.json`,
`prepare-checkouts.ps1`, `run-command.ps1`, `profile/`, `runtime/`,
`preservation/`, `provenance-reproduction/`, `final/` and local `.gitattributes`
files that enumerate only these artifacts. Nothing else changed:
`git diff --name-status aecf4a58...HEAD` outside `repair-r1/` lists exactly the
four scripts, the two ledgers and (in the evidence commit) the two public prose
files; `git diff --stat aecf4a58...HEAD -- RMQ lakefile.toml` is empty. All Lean
sources, the validator, `lakefile.toml`, shared scripts, accepted roots, the
original OPT-1 matrix and its evidence are byte-identical Git blobs
(preservation receipt, 510/510 protected entries).

## The two defects and the repaired production predicates

### P1-01: exclusive runtime rejection

Pre-repair `Assert-OPT1Rejected` (Q) searched the combined output for one
trimmed line equal to `uncaught exception: <surface>`, excluded `OPT1 CASE`/
`OPT1 PASS` prefixes and a finite error blacklist, and therefore admitted an
unrelated second uncaught exception. The counterexample was reproduced pre-edit
from the unique production AST extents with real owned children
(`runtime/frozen-reproduction/RESULT.json`, `runtime/evidence/frozen-raw-reproduction.json`).

Repaired predicate P, stated as the admitted output grammar: for the caller's
fixed surface `s`, accept an owned bounded result iff `TimedOut=false`,
`OutputLimitExceeded=false`, `ExitCode=1`, and the retained
`StandardOutput ++ StandardError` is the singleton `["uncaught exception: " ++ s]`
under ordinal case-sensitive equality without padding. The unchanged owned reader
drops empty transport lines, so blank separators are admitted; whitespace-only
lines, any second line, a success record, a resource failure, a wrong or
padded surface, exit 0/7, timeout or overflow all reject. The repaired function
is called unchanged by the four production negatives (`N01-JUMP`,
`N02-COUNTER`, `N03-BUDGET`, `N04-FRESH-COLLISION`, surface
`<id>: compiler observation mismatch`) and by the five Lean selector rejections.

Evidence: `runtime/REGISTRY.json` (53 cases; 31 classifier, 2 actual timeouts
with descendant death, 2 actual overflows with flushed witnesses, 12 real script
boundary cases, 6 registry controls) replayed by `runtime/replay.ps1` against the
frozen production script: `final/runtime-53/RESULT.json` PASS 53/53 in 173.98 s
(descendant PIDs 31220/10956 and 34940/36664 absent after the owned barrier).
The full 27-case production run then exercised the real consumers (below).

### P1-02: reproducible source identity for the certificate replay

Pre-repair `Assert-CImportProvenance` compared live raw source hashes with the
historical runtime receipt, which encoded undocumented mixed checkout newline
bytes (251/261 raw Git sources differed; `BranchBound.lean` needed 178 CRLF and
160 LF terminators). Reproduced pre-edit on a raw detached checkout
(`provenance-reproduction/`, exit 1 in 22.3 s at `RMQ/Core/Backend.lean`).

Repaired predicate P is the versioned canonical profile (`profile/README.md`):
strict UTF-8 without BOM or bare CR, CRLF replaced by LF only, every other byte
significant, anchored to the raw Git blobs at `aecf4a58...` for 263 sources
(261 transitive imports of `RMQ.Validation.PackedOptimized`, the validator and
`RMQ.Core.WordRAM.Optimization.Consumers`) and 4 configuration files, the
complete pinned Windows x86-64 Lean 4.22.0 distribution (4823 files,
1,983,374,857 bytes, compiler commit `ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`),
the frozen build driver, and a build receipt of actual one-job compilation whose
SHA-256 is a literal in the certificate runner. The cache must contain exactly
the 263 declared `.olean` files and their ancestor directories. A live input
never supplies its own expected hash: the manifest is pinned in the library, the
receipt is pinned in the runner, the driver is pinned in the library, and the
raw hash map is used only to verify restoration.

Canonical compilation (`profile/BUILD_RECEIPT.json`, verified here with the
production API against the private build cache `.lake/r1/b1` before pinning):
263 modules in dependency order, `lean -j1 -o <relative .olean> <relative .lean>`
in a materialized LF tree, started 2026-09-12T15:46:44Z, 3060.405 s total, every
exit 0, no timeout (600 s per module, 14400 s total) or 4 MiB overflow, ownership
`kill-on-close-job`, before/after canonical source hashes and direct dependency
artifact hashes (including `Init`/`Std` from the toolchain inventory) recorded per
module; the slowest module was `RMQ.Core.SuccinctFinalRAM` (100.1 s); eight
modules emitted Lean linter warnings only. `BUILD_ATTEMPT.json` in that tree is
byte-identical to the committed receipt.

Fresh checkouts (`final/prepare-r1/RESULT.json`): `prepare-checkouts.ps1`
created detached private clones of `f7cf20da...` under `.lake/r1/r1-lf`
(`core.autocrlf=false`, BranchBound.lean 338 LF / 0 CRLF) and `.lake/r1/r1-windows`
(`core.autocrlf=true`, 338 CRLF / 0 LF), installed independent copies of the 263
artifacts through `Install-OPT1ReplayArtifacts` with the literal pin, and found
both clean (154.4 s). No historical newline layout was reconstructed.

## Registries and executed counts

| Registry | Version | Expected | Executed | Duration | Receipt |
| --- | --- | ---: | ---: | ---: | --- |
| Original runtime (production `scripts/packed_optimized_runtime.ps1`, LF fixture) | `v1` | 27 | 27 | 643.491 s | `final/runtime-27/RESULT.json` |
| Original certificate (production `scripts/packed_optimized_certificate_replay.ps1`, LF fixture) | `opt1-certificate-replay-v3` | 80 | 80 | 3363.929 s | `final/certificate-80/RESULT.json` |
| Runtime repair (`runtime/replay.ps1`) | `opt1-r1-runtime-v1` | 53 | 53 | 173.98 s | `final/runtime-53/RESULT.json` |
| Production provenance/boundary/verdict repair (`scripts/packed_optimized_replay_regression.ps1`) | `opt1-r1-production-v4` | 49 | 49 | 1040.47 s (adapter), 1037.7 s (runner) | `final/regression-49/RESULT.json`, `final/regression-49/runner/` |

Registry v4 differs from v3 only in the corrected `R01-OMITTED` definition text
(46 to 49) and its repinned SHA-256
`59db124f0a3b42057977e2613bc0fb841ec62c8cebd2e0e5bfd5003cfe4f9c0e`; no case was
added or removed (v3 had added P19-P21 after an independent review noted that
an extra artifact in the import search path could shadow a pinned library
without changing any expected hash).

Regression-49 per-group results (all exact sole diagnostics, all restorations
verified): P01/P02 library positives on LF (197.9 s) and Windows (132.8 s);
P03/P04 `W28-stepBound` typed rejections on LF (119.7 s) and Windows (119.8 s)
after both mutated producers compiled, diagnostic
`Consumers.lean:267:2: error: type mismatch` (`True` versus the exact
`stepBound` proposition); P05-P21 setup rejections (source token, non-newline
whitespace, artifact byte, missing artifact, stale artifact, manifest bytes,
receipt bytes, toolchain text, omitted/duplicated import record, invalid UTF-8,
BOM, bare CR, wrong executable, extra `Init.olean`, empty `Init` directory,
`Backend.olean.server` sidecar) with nested causes checked for P07/P08/P15;
C01-C10 and R01-R09 selector/registry boundaries at the real entry points
(omitted 80/49, valid 1, empty, whitespace, padded, malformed, unknown,
contradictory, omitted/duplicated middle rows); V01/V05 accept and
V02-V04/V06-V09 reject the repair wrapper's own output grammar.

Full runtime 27 (`final/runtime-27/`): adapter exit 0, 643.491 s (2026-09-12T23:47:38Z to 23:58:27Z) of the 3600 s deadline, no timeout or overflow, all 8 input hashes and the LF fixture's tracked status/index unchanged, actual HEAD `f7cf20da...`; production receipt `OPT1-REPLAY PASS executed=27 expected=27 registry=v1`, 30 stages totalling 607.1 s: startup C01 34.8 s and C05 40.4 s, positive-cases 215.5 s with all 23 case markers (C06 steps=40 reads=6, C08 steps=4 reads=1, Q06 steps=13942 reads=263, Q09 steps=6321 reads=215) and `OPT1 PASS executed=23 expected=23 registry=v1`; N01-JUMP 34.7 s, N02-COUNTER 43.3 s, N03-BUDGET 54.0 s, N04-FRESH-COLLISION 44.9 s, each exit 1 with empty stdout and exactly one stderr line `uncaught exception: <id>: compiler observation mismatch`, i.e. the repaired exclusive classifier accepted the genuine intended exceptions; 16 host selector boundary cases (present/absent inherited selector) and 5 Lean selector rejections each with a sole `uncaught exception: OPT1 ...` line; `OPT1-SOURCE PASS exact source/import SHA256 before=after; tracked byte mutations=0`. RESULT.json SHA-256 `aa3d8d9ce004e0736e0aa0a9ba004e736236c03e388f96f522c886e42666d97a`.

Full certificate 80 (`final/certificate-80/`): adapter exit 0, 3363.929 s (2026-09-12T23:58:43Z to 2026-09-13T00:54:52Z) of the 7800 s deadline, no timeout or overflow, all 16 input hashes and the LF fixture's tracked status/index unchanged, actual HEAD `f7cf20da...`; production receipt `OPT1-CERT-REPLAY PASS executed=80 expected=80 registry=opt1-certificate-replay-v3`, 243 stages totalling 2893.2 s (80 Certificate compiles avg 6.9 s, 80 Capstone compiles avg 21.0 s, 80 Consumers checks avg 8.0 s). Independent re-check of all 80 `case.json` records by this worker: `ConsumerVerdict == Expected`, `ProducersCompiled=true`, `OriginalHashes == RestoredHashes`, and `ReplayIdentity.BuildReceiptSHA256 == eed1ecee...` for every case; both accept controls exit 0/0/0; every one of the 78 mutants has producer exits 0/0 and consumer exit 1 with a located `RMQ/Core/WordRAM/Optimization/Consumers.lean:<line>:2: error:` that names the selected field (e.g. W28-stepBound: `267:2: error: type mismatch / certificate.stepBound`; D34-positionalReadBacking: `361:2: error: Invalid field positionalReadBacking`). 259 read-only dependency snapshots were hardlinked per case; the profile recheck in `finally` passed. RESULT.json SHA-256 `bf5a0c0a008c7bb0f57264e759b0985b16479208f721327e8a2d249f5fa17d6b`.

## Preservation

`final/preservation-c1/result.json` (final mode against `f7cf20da...`): PASS,
17/17 controls; the original `docs/internal/extensions/opt1/ACCEPTANCE_MATRIX.md`
blob is byte-identical to the base; all 35 inherited complete row byte strings
equal the freeze commit in both the original and the repair matrix (per-row
SHA-256 recorded; the mojibake scan is a negative control only); the four repair
IDs are the only additions; 510 protected path/mode/blob entries (12
Optimization, 55 Packed, the validator, 3 axiom scripts, 439 original history
files) are unchanged; the 39 field `ExpectedType` payloads and 78 consumers are
exact; 93 axiom roots. Preserved theorem types are quoted in the matrix
appendix and `PROOF_IDENTITY.md`, including
`branchSensitiveQueryBound : (queryRun memory n left right).steps <= 150739`,
`reducedFuel_queryRun_eq : run memory queryProgram 150739 (initialState n left right) = queryRun memory n left right`,
`compactPackedQueryCapstone_holds : CompactPackedQueryCapstone` (39 fields), and
the complete-capacity field
`((buildMemory xs).length + (compactQueryProgram.map Instruction.encoding).flatten.length + (compactQueryRegisterCount + 3)) * wordWidth xs.length <= 2 * xs.length + compactQueryCompleteRho xs.length`.
The constants 150739, 151978, 212964, 722339, 8273 and 8276 live in unchanged
blobs. The first preservation run against the evidence commit
`d766e84b22c933a852d90cdb44ac123819fe75a4` FAILED with `ROW_DUPLICATE` for
`REQ-OPT-R1-EXCLUSIVE-REJECTION` (receipt kept as a recorded failure under
`final/preservation-c2/`): the evidence appendix this continuation had appended
to the repair matrix used the same `| \`ID\` |` first-cell format as the frozen
rows, so the checker correctly saw two rows with one ID. No protected object,
frozen row or field type was involved. The appendix rows were relabelled
`Evidence for \`ID\`` in the corrected commit, whose final-mode preservation
receipt is committed separately after that commit exists.

## Build, trust and final checks

- `lake build` (one job through `LEAN_NUM_THREADS=1`; Lake 5.0.0 has no `-j`/`--jobs` option, and the first attempt with `-j1` failed on that flag and is kept under `final/lake-build-attempt1-wrong-flag/`; owned job, 5400 s deadline) on this
  worktree after a byte-verified private copy of the author cache
  (`C:/Users/poin/.codex/worktrees/1580/RMQ/.lake/build`, 2995 files, 0
  mismatches; 23 tracked Lean/config files differ from that checkout only by
  CRLF/LF serialization and are LF-normalized equal): exit 0 in 36.183 s (2026-09-13T04:46:23Z to 04:47:01Z) of the 5400 s deadline, `Build completed successfully.`, no timeout or overflow, kill-on-close ownership, `LEAN_NUM_THREADS=1`. All 374 default-target (`RMQ`) jobs were up to date against the private byte-verified copy of the author cache: 0 files written, 2995 cache files before and after, 15 cached module logs replayed (Lean linter warnings only, 0 error lines). Lake's trace hashes are newline-normalized, so the 23 tracked Lean/config files that differ from the author checkout only by CRLF/LF serialization did not invalidate any trace; the tracked Lean/config tree is byte-identical to the base by `git diff`. The first attempt with `-j1` failed in 2.8 s on `error: unknown short option '-j'` because Lake 5.0.0-src+ba2cbbf accepts no `-j`/`--jobs` option; that failed receipt is kept under `final/lake-build-attempt1-wrong-flag/` and the one-job intent is enforced through `LEAN_NUM_THREADS=1`, the same plain `lake build` the coordinator ran on the base (1607.132 s, cold cache). This reuse of verified artifacts is recorded, not hidden; it is not a fresh full compilation, which the profile receipt separately supplies for all 263 modules of the replay closure.
  Receipt `final/lake-build/RESULT.json`.
- Explicit compilation of every capstone and typed consumer: the pinned receipt
  compiled `RMQ.Core.WordRAM.Optimization.Certificate`, `.Capstone`,
  `.Consumers` and `RMQ.Validation.PackedOptimized` (exit 0 each) in addition to
  their 259 dependencies; the default `RMQ` target does not import them.
- 93-root optimized axiom union (`scripts/packed_optimized_axiom_check.ps1`,
  run in the LF fixture so the lead checkout's historical
  `composition-development` directory is not written): PASS: `OPT1-AXIOMS: expected=93 found=93 pass=True`, `dependencies=Classical.choice,propext,Quot.sound`, no uncovered or unexpected roots, one union, both public standard prints (`branchSensitiveQueryBound`, `compactPackedQueryCapstone_holds`) present, 180 s deadline / 2 MiB ceiling not reached.
  Receipt `final/axiom-union/`.
- Hygiene: `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml`
  and `rg -n "native_decide|Lean\.ofReduceBool" RMQ` both exit 1 with empty
  output (no matches); no trust surface changed.
- `git diff --check` clean before each commit; `git diff --check aecf4a58..HEAD`
  clean after `f7cf20da...` (repeated after each later commit).
- `scripts/design_decision_check.ps1 -Strict -Base aecf4a58...` PASS on the
  worktree and per commit with `-Head` (175 files: 0 code, 169 workflow, 6
  neutral at the freeze commit); DD and WDD entries are in every commit that
  touches code- or workflow-sensitive paths.
- `scripts/claim_drift_scan.ps1 -Strict` with unchanged roots and policy:
  development-loop run 252.9 s, 1768 hits, 0 strict failures; final run after
  this report existed: run A on the report-bearing tree: 1807 hits, 0 strict failures, exit 0 in 283.752 s under a 1200 s owned deadline (`final/claim-scan-a/RESULT.json`, SHA-256 `260284c3b1416d6a13bff273d8abcf3dfc4a65ef95a8ecf81d6a3ccfbfa5cfbf`); after these numbers were inserted, run B FAILED strictly (exit 1, 307.8 s, `strict mode found 7 unapproved sensitive matches`, receipt kept as a recorded failure in `final/claim-scan-b/RESULT.json`): all seven were `forbidden-2pow128-canonical-activation` hits inside `final/claim-scan-a/stdout.log`, i.e. the raw scanner output that had been stored under `docs/` became a new claim surface whose quoted hit lines re-trigger strict terms outside their allowed contexts; no hit came from the report or matrix text. The raw hit logs were moved to untracked scratch (`.lake/r1/claim-scan-logs/`, SHA-256 recorded in each receipt) and the wrapper now writes them there; run C on the final report bytes is recorded in `final/claim-scan-c/RESULT.json` (its own hit count and 0 strict failures are in that receipt; the report cannot quote a scan of its own final bytes without changing them).
- `scripts/constant_sync_check.ps1` PASS (210 and 427 surfaces agree).
- Not executed anywhere in this task: `scripts/gate.ps1` (coordinator-owned),
  any POSIX process-ownership branch, any non-Windows compiler build.

## Failures, interruptions and limits recorded

- Pre-repair counterexamples for both defects are retained as failures, not
  hidden (`runtime/frozen-reproduction/`, `provenance-reproduction/`).
- Development failures of the original worker are retained
  (`runtime/evidence/development-overflow-failure.json`, the review wrapper
  defect and its fix under `runtime/review/`, the placeholder-pin failure noted
  in the WDD entry, the toolchain-version outer check noted in
  `profile/TOOLCHAIN_VERSION_CHECK.json`).
- The continuation's first Windows PowerShell 5.1 parse check was a harness
  invocation error (arguments bound to the first script); it was rerun as a
  file-based script and passed for all ten owned scripts.
- One staged whitespace finding (a blank line at the end of `PROOF_IDENTITY.md`)
  was fixed before the freeze commit.
- The receipt-only commit `8f2f9b091b92f0533d5fc9539528d3c6915513c2` recorded the
  failed C2 preservation run with an empty result string because its reader
  assumed a passing receipt; the corrected commit states the failure explicitly,
  and the failed receipt itself was never altered.
- The second report-bearing strict claim scan (run B) failed on the raw hit log
  of run A that had been placed under `docs/`; see the claim-scan bullet above.
- Library self-tests now take about 130 s (pwsh 7.6.6) and 465 s (Windows
  PowerShell 5.1) rather than the historical 45 s because the profile hashes the
  complete 1.98 GB toolchain inventory twice per invocation; this is a cost of
  the exactness the row requires, not a defect, and all deadlines carried 2x
  margin over these measurements.
- POSIX execution of the owned-process branch is UNEXECUTED on this Windows host
  and is recorded as such in every receipt; exact artifact equality is claimed
  only for the pinned Windows distribution; the historical receipt
  `full-runtime.json` (`a7eb5831...`) remains an immutable separate record.

## Design decisions

`DD-20260912-OPT1-R1-001` (canonical source identity distinct from compilation
artifacts; replayable registry/AST/receipt artifact design; no Lean change) and
`WDD-20260912-OPT1-R1-001` (exclusive runtime diagnostics, versioned source
profile, why the certificate-path exclusivity principle of WDD-OPT1-006/007 had
not reached the runtime path, the v2/v3/v4 registry evolution and the wrapper
verdict defect found by review) are in the two ledgers, with dated follow-up
paragraphs in each commit. No Lean fixture was added, so no proof-model decision
was needed beyond recording that the model is unchanged.

## Proof digestion

Conceptually, nothing about the compiler theorems changed. What changed is the
evidence contract around them: a rejection is now accepted only when the
process produced exactly the intended diagnostic and nothing else, and the
compiled inputs of the certificate replay are identified by a declared canonical
serialization of the exact Git source, the exact toolchain distribution and an
actual compilation receipt, rather than by whatever newline bytes an editor once
left on disk. In plain English: a known failure message can no longer hide a
second failure, and a reviewer who clones the commit on either newline profile
can install the pinned artifacts and run the same replay without archaeology.

Live assumptions: the unchanged Nat-valued primitive machine model and its
representable-endpoint guards; the pinned Windows Lean 4.22.0 distribution as
the sole supported compiler for exact artifact equality; the trusted pins
(manifest in the library, receipt in the runner, driver in the library); the
shared owned-process helper's line representation and overflow discard; and the
Lean kernel trust base. Downstream consumer: the production replay of the same
inhabited `compactPackedQueryCapstone_holds` through its 78 exact generic and
canonical consumers, and the coordinator's aggregate certification and fresh
audit. A skeptical graduate student would next ask whether a compiler artifact
produced by another Lean build could be smuggled past the profile (answer: it is
rejected, and reproducibility across distributions is explicitly not claimed),
whether the singleton grammar could reject a genuine rejection whose diagnostic
legitimately spans two lines (it would, and the four production surfaces are
single-line by construction), and whether POSIX ownership behaves like the
Windows job (unexecuted here).

## Hashes and identities

| Object | SHA-256 |
| --- | --- |
| `profile/SOURCE_PROFILE.json` (pinned in the library) | `b83ada3baa438d812da076b48422c0a92f88ce686cd48ef982f39de7701699c9` |
| `profile/BUILD_RECEIPT.json` (pinned literal in the certificate runner) | `eed1ecee4a031a9c3cfcadea445307d8e15e70e732e6ffdd5b166d135292b64e` |
| `profile/BUILD_DRIVER.ps1` (pinned in the library) | `a14f1205c57ac4d475c38e3d73179fc1645eaf1d5bc4962dad9f3c42655588a9` |
| `REGISTRY.json` v4 (pinned in the regression runner) | `59db124f0a3b42057977e2613bc0fb841ec62c8cebd2e0e5bfd5003cfe4f9c0e` |
| `runtime/REGISTRY.json` (pinned in `runtime/replay.ps1`) | `35dee68d8efbb972fb35276bc03b1ec18071048d83e0bfac0334daa9364ade4d` |
| `scripts/packed_optimized_runtime.ps1` checkout bytes / LF blob | `69494710c3aaa873fdc3f915ba0dd67cfa449f40e2a9890dca126f9eade0f347` / `312c16b883b5a50fde8251c57926c24d5c56975baff05247e8fe234bfcb3ed10` |
| `scripts/packed_optimized_certificate_replay.ps1` LF blob | `c64ad401a1236dea7c9638fcf59709728a397b489b5f08ca00942b4d6f7a15e3` |
| `scripts/packed_optimized_replay_profile.ps1` | `33104c7a7392b7710743765b3eb9513430bd3389fd175d9efb2dcf48f331956b` |
| `scripts/packed_optimized_replay_regression.ps1` | `445a0bad0e38d006840498ec6aaed33f8dffb23cea4384c3a9b1878102392e12` |
| `final/regression-49/RESULT.json` / `runner/RESULT.json` | `0ab69a10bb6caf5453ad0ba7dcfe4b49ba5d6824f2a887c6be16c091ae23ec9c` / `246f53054f8dd081edfec90874534fea2e133489872dabd9ca01664f01156192` |
| `final/runtime-53/RESULT.json` | `aa71e8d2e2c411bffe031e2fb7b0ab86f0b87ab5429a414c795d0522f937eb00` |
| `final/preservation-c1/result.json` | `0f80fec5e49d0fae83c498c87b6d30a1973abaac955070e22b3addb11290cd58` |
| `final/prepare-r1/RESULT.json` | `33712034a1c59b72d7b35d9907284113b3d3768165e3ec9e6dc159e1fcf25ff2` |
| `final/runtime-27/RESULT.json` | `aa3d8d9ce004e0736e0aa0a9ba004e736236c03e388f96f522c886e42666d97a` |
| `final/certificate-80/RESULT.json` | `bf5a0c0a008c7bb0f57264e759b0985b16479208f721327e8a2d249f5fa17d6b` |
| `final/lake-build/RESULT.json` | `ccfa0c741f0962c634a741df1e059bafcce26ed2aa3fee5ee15713fbe5fe1499` |
| Historical receipt `runtime-replay/evidence/full-runtime.json` (unchanged) | `a7eb5831a88a7431607d5fe1d7189318d41978391e0a10be3ed336c014563661` |

Hosts: Windows 11 Pro 10.0.26200; pwsh 7.6.6 (production campaigns); Windows
PowerShell 5.1.26100.9444 (one library positive and parse checks); Python
3.14.4 (preservation checker); Lean 4.22.0 / Lake 5.0.0-src+ba2cbbf.

## Requested lifecycle disposition

Requested next coordinator step: schedule the single aggregate `scripts/gate.ps1`
slot on the final evidence commit of this branch and launch the fresh
exact-commit blind audit of that commit with the frozen prompt; then record
acceptance or a repair disposition. Public integration is a separate later
operation. This report does not self-declare acceptance.
