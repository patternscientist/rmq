Status: BLOCKED
Open IDs: L1-18, L1-20, INV-MUTATION-REPRODUCIBILITY, CHK-FINAL, CHK-SCOPE, L1R1-CLEANUP. Required scope decisions remain pending; no coordinator acceptance is claimed.

The validator omission repair and independent dependency cleanup are implemented.
Both actual production full16 validator runs pass. The remaining blockers are
the original contract files' inherited CRLF serialization and an existing hash
API that cannot execute in Windows PowerShell's .NET Framework. Neither protected
surface has been changed without the requested scope amendment. This report
records a blocked local repair, not a complete candidate or a mathematical
obstruction to the lifecycle theorem.

Worker LIFE-1-R1; task `01a0c23e-6fce-7542-b453-8fa7a741d7c9`; requested title
`(LIFE-1-R1) Repair lifecycle validator portability`. Worktree:
`C:/Users/poin/.codex/worktrees/e993/RMQ`; branch
`codex/life-1-r1-validator-portability`. Exact base:
`12bd7f0fc2c87f2c9bdef3825bd92477e48e3433`; governance:
`7b227c49ef2ec044b702126cc41c9add847eed01`. Actual runtime project skills were
`rmq-audit-prompt`, `rmq-coordinator`, and required `rmq-proof-sprint`; canonical
preflight passed before editing. [START.json](START.json) preserves launch facts.

Production source freeze is private commit
`122a6bedb086d1de1df8dec167c890f887a72cc2`. The final control-source freeze is
`7c406b15bdc12333d323c92641ab6c6dad6af7a2`, which repairs two harness portability
issues and leaves every production, Lean, tool and executable byte unchanged.
Evidence/report packaging follows in a
separate private commit. Its exact enclosing commit, this report's byte length
and SHA256, postcommit checks, and clean state are recorded in
`C:/Users/poin/.codex/worktrees/e993/RMQ/.lake/repair-r1/delivery.json` and the
terminal submission. This avoids embedding a commit or report hash into itself.
No push, merge, retirement, aggregate run, installation, publication, roadmap
closure, or acceptance occurred.

The two required decisions are concrete:

- Permit re-materializing only original `CONTRACT_REQUIREMENTS.json`,
  `ACCEPTANCE_MATRIX.frozen.md`, and `ACCEPTANCE_MATRIX.md` from the exact base
  Git blobs, preserving their content and producing no Git content diff. They
  were CRLF-converted by checkout. The original checker currently exits 1 with
  `CONTRACT_HASH: frozen source/requirements JSON changed`; it has not been
  weakened. The unchanged frozen working matrix is 43,514 bytes, SHA256
  `bc596cd8a4866cf8db7bd06360d1c2e797e389c92237c9ac3a0b5e4145cd22ab`;
  the required exact Git blob is 43,437 bytes, SHA256
  `8b08e2d7c7f284634d88bfa4262ee447f79a401c78b27dc346ea34d76ccba4a7`.
- Permit the narrow portable implementation of protected dependency `Hash-Bytes`
  using SHA256.Create/ComputeHash and BitConverter, preserving identical hashes,
  or explicitly amend the Windows dependency-control contract. The current
  `[SHA256]::HashData` and `[Convert]::ToHexString` APIs are unavailable in .NET
  Framework. A replacement predicate in the harness would not establish the
  required same-production-source intact-pin positive. No such substitution was
  made. The allowed dependency write scope currently covers finalizer guards
  and faithful error/status recording only.

The production validator now consumes
`scripts/lifecycle_validator_environment.ps1`. Its selector is an object:
null means absence, and a string means that exact intentional environment value.
The adapter snapshots key presence and value, sets/removes only the current
process key, invokes the unchanged owned-process helper without a selector
override, and restores and checks the previous state in finally. Registry,
startup, argument-selected, and full launches pass null. Intentional `id:`
values remain exact strings. The Stage/Case CLI, native selector, registry,
semantic assertions, and stdout/stderr/exit verdicts remain unchanged.

The dependency runner separately attempts `Assert-Restored` and `Remove-Shadow`
inside finally. Stage, integrity, and cleanup errors have separate fields and
remain nonzero failures. Failed integrity sets `restored=false`; cleanup still
uses the unchanged resolved-descendant and exact `shadow` basename guards.
The runner never repairs a changed original file. The shared helper, registry,
typed consumers, compiler ordering and diagnostic classifier are unchanged.

The exact 45-row contract preserves all 43 complete eight-column Git row bytes
and their historical Open cells, then adds the two requested requirements.
Its frozen SHA256 is
`ae991367ef537d61d5af0ef738aad3b7ee1693e22a1ed27469d83a3de65f6417`.
The strict verifier compares full UTF-8 rows, ordered IDs, nonempty columns,
complete requirement text and frozen prefixes, not just counts or hashes.
Its 20 controls include changed late cells, missing/duplicate IDs, mojibake,
and legitimate positives. Exact original prompt SHA256 is
`f82a24460dfa06602fc52e2c78b0fa8402fbb84a0d203b4abb95040fa56b0c18`.
[ROW_DISPOSITIONS.md](ROW_DISPOSITIONS.md) quotes every historical proposition
and object chain and records all 45 successor dispositions. It is appended to
the active matrix without rewriting its frozen prefix. Every inherited row
remains subject to the blocked final delivery requirements; historical
candidate-closed language is not adopted as current certification.

<!-- BEGIN-OBSERVED-CHECKS -->

| Check | Observed disposition | Outer exit | Seconds / deadline |
| --- | --- | --- | --- |
| Default build (`final-default-build-pinned`) | PASS; warm verified cache | 0 | 1.637 / 7200 |
| Named lifecycle builds (`final-named-build-pinned`) | PASS; five named targets | 0 | 1.661 / 7200 |
| Current PowerShell startup (`final-validator-pwsh-startup`) | PASS; registry/startup only | 0 | 9.126 / 2100 |
| Current PowerShell full16 (`final-validator-pwsh-full`) | PASS; nine owned child launches | 0 | 119.739 / 2100 |
| Windows PowerShell startup (`final-validator-winps-startup`) | PASS; registry/startup only | 0 | 13.305 / 2100 |
| Windows PowerShell full16 (`final-validator-winps-full`) | PASS; nine owned child launches | 0 | 109.269 / 2100 |
| Dependency self-test (`final-dependency-selftest`) | PASS; empty baseline limitation remains | 0 | 10.858 / 7200 |
| Dependency startup (`final-dependency-startup`) | PASS; D20/P06 positives | 0 | 57.674 / 7200 |
| Dependency focused D15 (`final-dependency-focused`) | PASS; exact expected rejection | 0 | 47.644 / 7200 |
| Dependency full26 (`final-dependency-full`) | PASS; 23 rejects, three accepts | 0 | 495.066 / 7200 |
| Final control revision, current PowerShell (`f2-controls-pwsh`) | PASS; exact 67 controls | 0 | 439.518 / 2700 |
| Current PowerShell registry campaign (`f2-registry-pwsh`) | PASS; 12 controls / 24 P-Q children | 0 | 56.673 / 2700 |
| Final control revision, Windows PowerShell (`f2-controls-winps`) | BLOCKED; 32 selector/wrapper controls pass, D01 HashData failure | 1 | 161.677 / 2700 |
| Windows PowerShell registry campaign (`f2-registry-winps`) | PASS; 12 controls / 24 P-Q children | 0 | 39.106 / 2700 |
| Windows intact-pin finalizer P (`f2-winps-finalizer`) | BLOCKED; exact protected HashData failure | 1 | 5.993 / 180 |
| Windows descendant timeout (`f2-winps-timeout`) | PASS; intended timeout, cleanup and restoration | 0 | 10.986 / 180 |
| Original contract integrity (`final-original-contract`) | BLOCKED; inherited contract serialization | 1 | 5.571 / 60 |
| Trust hygiene scan (`final-hygiene`) | PASS; rg exit 1 with zero matches/diagnostics | 1 | 3.025 / 180 |
| Native-decision scan (`final-native-trust`) | PASS; rg exit 1 with zero matches/diagnostics | 1 | 2.717 / 180 |

The table is a display of the bound receipts, not a replacement verdict
predicate. ROW_DISPOSITIONS.md generation checks the exact successful
prefixes, mappings, source pins and specific failure surfaces. EVIDENCE_INDEX.json
retains every attempt, including development and failed launches. All listed
outer checks completed without an unexpected timeout or output overflow.
The intentional inner sleeper timeouts are separate expected outcomes.

Final control source is 7c406b15bdc12333d323c92641ab6c6dad6af7a2.
Current PowerShell completes every frozen control; Windows full selection
remains all 66 applicable IDs, of which exactly S01-S23 and W01-W09 finish
before D01 fails. The remaining dependency/finalizer positives cannot run
through the protected hash implementation. They are not skipped passes.

The source-bound Windows F01 positive exits 1 with exactly:

```text
Method invocation failed because [System.Security.Cryptography.SHA256] does not contain a method named 'HashData'.
```

Its captured baseline is empty because capture itself fails; restored=true
there establishes no intact-pin result. The component is BLOCKED, not an
expected-reject success. The actual dependency boundary records the same
specific failure in its accepted P before any Q can be credited.

The final pwsh timeout observed child root PID 30392 and descendant PID 25092; all observed owned IDs were absent afterward and the ambient selector was restored.

The final winps timeout observed child root PID 26260 and descendant PID 27672; all observed owned IDs were absent afterward and the ambient selector was restored.

Current-pwsh finalizer F03 separately retains the prior stage failure and
the changed-pin integrity failure, exits 1, reports restored=false, removes
the valid shadow, and releases its mutex without abandonment. F10/F11
retain actual locked-file cleanup failures. All fixture cleanup is separately
recorded after the production verdict.

The changed paths relative to the exact base are:

```text
docs/internal/WORKFLOW_DESIGN_DECISIONS.md
docs/internal/extensions/lifecycle1/VERIFICATION_PLAN.md
docs/internal/extensions/lifecycle1/repair-r1/ACCEPTANCE_MATRIX.frozen.md
docs/internal/extensions/lifecycle1/repair-r1/ACCEPTANCE_MATRIX.md
docs/internal/extensions/lifecycle1/repair-r1/CACHE_PROVENANCE.json
docs/internal/extensions/lifecycle1/repair-r1/CONTRACT.json
docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.frozen.json
docs/internal/extensions/lifecycle1/repair-r1/CONTROL_REGISTRY.json
docs/internal/extensions/lifecycle1/repair-r1/EVIDENCE_INDEX.json
docs/internal/extensions/lifecycle1/repair-r1/INITIAL_WORKING_FILES.json
docs/internal/extensions/lifecycle1/repair-r1/PROMPT.md
docs/internal/extensions/lifecycle1/repair-r1/REPORT.md
docs/internal/extensions/lifecycle1/repair-r1/ROW_DISPOSITIONS.md
docs/internal/extensions/lifecycle1/repair-r1/SCOPE_VERIFICATION.json
docs/internal/extensions/lifecycle1/repair-r1/SOURCE_FREEZE.json
docs/internal/extensions/lifecycle1/repair-r1/START.json
docs/internal/extensions/lifecycle1/repair-r1/VERIFICATION_PLAN.md
docs/internal/extensions/lifecycle1/repair-r1/build_row_dispositions.py
docs/internal/extensions/lifecycle1/repair-r1/collect_evidence.py
docs/internal/extensions/lifecycle1/repair-r1/contract_verification.json
docs/internal/extensions/lifecycle1/repair-r1/deadline_control.ps1
docs/internal/extensions/lifecycle1/repair-r1/dependency_boundary_cases.json
docs/internal/extensions/lifecycle1/repair-r1/dependency_child.ps1
docs/internal/extensions/lifecycle1/repair-r1/finalizer_cases.json
docs/internal/extensions/lifecycle1/repair-r1/finalizer_control.ps1
docs/internal/extensions/lifecycle1/repair-r1/finish_report.py
docs/internal/extensions/lifecycle1/repair-r1/freeze_controls.py
docs/internal/extensions/lifecycle1/repair-r1/initialize_contract.py
docs/internal/extensions/lifecycle1/repair-r1/make_dependency_registry.py
docs/internal/extensions/lifecycle1/repair-r1/make_selector_registry.py
docs/internal/extensions/lifecycle1/repair-r1/old_environment_control.ps1
docs/internal/extensions/lifecycle1/repair-r1/preflight.txt
docs/internal/extensions/lifecycle1/repair-r1/prepare_cache.py
docs/internal/extensions/lifecycle1/repair-r1/prepare_old_root.py
docs/internal/extensions/lifecycle1/repair-r1/registry_control_cases.json
docs/internal/extensions/lifecycle1/repair-r1/registry_controls.ps1
docs/internal/extensions/lifecycle1/repair-r1/run_check.ps1
docs/internal/extensions/lifecycle1/repair-r1/run_controls.ps1
docs/internal/extensions/lifecycle1/repair-r1/runtime_profile.ps1
docs/internal/extensions/lifecycle1/repair-r1/selector_cases.json
docs/internal/extensions/lifecycle1/repair-r1/selector_child.ps1
docs/internal/extensions/lifecycle1/repair-r1/source_manifest.py
docs/internal/extensions/lifecycle1/repair-r1/verify_contract.py
docs/internal/extensions/lifecycle1/repair-r1/verify_scope.py
scripts/lifecycle_dependency_replay.ps1
scripts/lifecycle_validator.ps1
scripts/lifecycle_validator_environment.ps1
```

<!-- END-OBSERVED-CHECKS -->

The 67 ordered repair controls are frozen in
[CONTROL_REGISTRY.json](CONTROL_REGISTRY.json), identical to its frozen copy,
SHA256 `385c9bc95ac09b3cc046a7049e954cdf19361330c31f99bd83c9da0c822423f2`.
They comprise 23 adapter/native cases, nine actual wrapper cases, 22 actual
dependency boundaries, 12 source-bound finalizer cases (the old regression is
current-pwsh-only), and one real descendant timeout. Their component registries
pin each production path, P/Q guards and exact verdict. The separate 12-case
registry campaign checks full/focused selection, explicit empty/whitespace,
unknown selection, missing/duplicate/unknown middle entries, unused/mutated
mappings and two wrong-runtime identities. Every probe reaches the actual
driver; probes execute zero semantic fixtures.

Native rejection controls first execute an accepted P in the same ambient
environment, then Q through the same adapter and actual executable. Wrapper
negatives first run real startup and validate its production receipt. The
bounded exit fixture compares exit 0 and exit 7 through the same child source.
Dependency controls run the exact original registry as P at the same script
root before installing Q. The unused-edit challenge changes exactly one space
inside one JSON value; it cannot pass merely because serialization changed a
terminal newline. Captured Console.Error text retains its trailing newline.
PowerShell 7 can represent an empty environment value; Windows PowerShell's
setter removes it. Controls record the observed absence and do not pretend
that Windows tested a representable present-empty value.

Finalizer controls extract and pin the production AST spans for Hash-Bytes,
Hash-File, Write-Json, Assert-Restored, Remove-Shadow, the entire catch/finally
and terminal verdict. Only the main try body is replaced with owned fixture
setup. Real bounded children execute accepted/challenged pairs for intact
success/failure, changed pins after failure/apparent success, partial and empty
baselines, rejected paths, and actual FileShare.None cleanup failures. The old
exact component must fail and leave its valid shadow before harness cleanup;
the repaired component must retain failure while deleting it. Original files
are never mutated. Fixture pins and shadows are restored only by their own
finally/harness cleanup after the production verdict is recorded. Private mutex
observers distinguish normal release from abandonment and verify child/root
absence. An empty captured baseline proves equality over zero files only.

The full production validator checks the same 16 ordered IDs/models/kinds and
independent assertions. Its built-in focused fixture precedes full execution;
startup is independently checked first. The production dependency sequence is
SelfTestOnly, StartupOnly D20/P06, focused D15_CODE_FETCH_DROP, then full26.
Fresh producer elaboration must exit 0 without diagnostics before the unchanged
client can count as an expected rejection/acceptance. Exact diagnostic classes,
declaration intervals and counts are preserved; mixed/unrelated diagnostics,
contamination and false PASS records remain failures.

All expensive work uses `Local\RMQLifecycleImplementationHeavy20260920` without
recursive acquisition. Builds use 7200-second bounds; production compiler stages
retain 120 seconds; validator semantic children retain 1800 seconds and
registry/startup/reject children 30 seconds; control children are bounded at
30 seconds inside owned outer guards. The intentional sleeper/descendant uses
six seconds. Final evidence includes exits, elapsed time, timeout/overflow,
job ownership, observed PIDs and cleanup results. The protected helper exposes
nonempty returned lines, not complete original byte streams. Overflow or an
exceptional cleanup path can prevent output recovery; those limitations remain
disclosed failure/uncovered, never complete raw-output certification.

The formal proposition is unchanged:

```lean
continuousConstructionQuery_holds
    (model : InputModel) (xs : List Int) (left right : Nat)
    (domain : InputDomain model xs)
    (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) :
    ContinuousConstructionQuery model xs left right
```

The same `Continuous.continuousRun model xs left right`, `Layout.program model`,
`wordWidth xs.length`, constructed memory, retained owner and `retainedRho`
occur in all seven public fields. C01-C07 independently expand construction,
retained state, prefix safety, physical read/code backing, finite owner,
reusability and uniform bounds. C08-C12 pin word/comparison forms, constants,
valid `scanWindow+1` with `LeftmostArgMin`, and invalid packet zero. C13/C14 retain
initial state agreement and guarded replies at paired actual prefixes. P01
independently expands reservation, descriptor, indexed copy and release
occurrences with index, actual pre-state and actual step. No final answer or
Ready owner is an entry premise of the public construction theorem.

Word input still requires InputFits at the same query-independent width;
comparison input has a separate arbitrary-Int resource channel. Endpoints must
be represented. Input materialization and out-of-word endpoint admission remain
outside the theorem. A later query assumes a Ready halted owner and represented
endpoints, returns the reference packet, preserves the exact memory array,
restores Ready and costs at most 160257 modeled transitions. The logarithmic
width, `2*n+retainedRho n` numeric payload and LittleOLinear remainder concern
those same objects. Prefix physical backing uses the evolving modeled arena;
it proves neither native backing capacity/alias freedom nor an immutable
initial whole-run snapshot.

[SOURCE_FREEZE.json](SOURCE_FREEZE.json) binds the original source manifest,
historical evidence, source/tool/runtime bytes, Git blobs, consumer artifacts,
cache provenance and version/build receipts. The historical exact type/axiom
inventory is reused only after its retained output bytes and unchanged source
are verified. It reports subsets of propext, Classical.choice and Quot.sound;
the wrapper repair creates no Lean theorem. [SCOPE_VERIFICATION.json](SCOPE_VERIFICATION.json)
separates unchanged raw checkout bytes from Git identity and from the original
contract serialization failure. The copied build cache comprises independent
files from the exact base, with all source/artifact hashes recorded. Successful
warm default/named builds do not claim an independent cold build.

The immutable old helper/wrapper current-pwsh failure and legitimate old WinPS
full16 positive are preserved with the same executable SHA256
`4752591ec5a7d962e09440391aa38d0e2fc534b2f04775aab9c0c735e43ba99c`.
The first 67-control development pass preceded corrections to the registry
mutation, stderr and runtime guards; it is retained as development only. A
mistyped focused control ID rejected before semantic work and was corrected in
a new invocation. An initial elan-shim default-build attempt failed a download
lookup before building; the actual installed pinned Lean 4.22.0 Lake binary
subsequently completed the required builds. No installation occurred.

At the first control freeze, Windows PowerShell saw an empty `$PSScriptRoot`
while evaluating the optional RegistryPath default. Those launches failed before
cases and supply zero coverage. An explicit frozen registry path reached 23
passing native controls, then exposed a second harness issue: an outer array
expression counted the WinPS ConvertFrom-Json array as one object. The actual
production startup passed with two records and restored the inherited selector;
the harness correctly stayed non-passing until its reader was repaired.

The final control freeze resolves the default in the body only when the
parameter is absent, and assigns the parsed JSON value directly before the
unchanged exact two/three-process check. Explicitly bound empty still differs
from omission. A focused WinPS W01 control passed with the default after both
fixes. Complete control campaigns are replayed on this new source; earlier
control passes are retained as prior-revision evidence only. The unchanged
production full16/full26 and builds retain their source applicability.

WDD-20260921-LIFE-R1-001/002/003 record the production choice, rejected helper/empty
override shortcuts, independent cleanup, evidence controls and consequences.
No DESIGN_DECISIONS entry was needed or authorized because no theorem, machine,
representation or cost design changed. Final evidence packaging has a separate
append-only workflow entry. The unchanged strict design policy is checked on
each private commit and the exact-base range. Report-sensitive strict claim
coverage includes the new report and row dispositions explicitly; frozen quoted
requirements and historical reports are not promoted into new public claims.
No aggregate gate was assigned to this repair.

Conceptually this repair preserves environment absence and separates two
cleanup obligations that previously short-circuited. In plain English, an
inherited selector no longer contaminates an omitted-selector launch, and a
detected changed original cannot prevent an otherwise safe disposable-shadow
cleanup. The proofs, modeled payload, operation counts and retained owner are
unchanged. The skeptical next questions are whether the authorized portable
hash yields the same production finalizer positives on .NET Framework, whether
the exact original contract bytes pass after the approved serialization repair,
and whether the later independent native/campaign consumers establish their own
ownership and acceptance obligations. These questions are not credited as done.

An attempted message transferring the two blockers to the originating task was
rejected by automatic approval review because destination authorization was
not established. No message was delivered or retried through another route;
the questions remain in this task and the durable report is local.
