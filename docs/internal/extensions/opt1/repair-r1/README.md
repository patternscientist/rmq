# OPT-1-R1 replay repair

This directory contains the new repair evidence. The original OPT-1 requirement
rows, proof sources, field/consumer contract and historical receipts remain
unchanged. `ACCEPTANCE_MATRIX.md` freezes all 35 original complete rows and four
repair rows; current evidence is appended by row ID. `REPORT.md` is the worker
handoff, and `PROOF_IDENTITY.md` supplies all 39 literal expected field types,
their 78 consumers, object/guard chains and inherited row mapping.

## Output contract

The actual runtime function `Assert-OPT1Rejected` accepts exactly an owned,
bounded, non-overflowing process with exit 1 and one nonempty output line across
both stdout and stderr. That line must equal, case sensitively and without
padding, `uncaught exception: ` followed by the selected expected surface.
The unchanged owned-process reader removes empty transport lines; whitespace-only
lines remain output and reject. It is immaterial which stream carries the sole
intended diagnostic. Any additional diagnostic, duplicate, success record,
resource failure or unrelated text rejects. This is a complete admitted grammar,
not a list of forbidden exception phrases.

The separate repair runner also treats a failed production setup exclusively:
one exact stderr diagnostic, and only the optional, ordered production artifact,
stage and restoration records on stdout. Its nine `V` cases include genuine
accepts, mixed streams, success text, duplicate/reordered progress and near-match
holdouts. Nested runtime setup failures additionally require their exact actual
cause and sole runtime artifact-path record. A setup rejection never counts as
a certificate type rejection.

## Source, compilation and installation identity

Read `profile/README.md` for the complete reproducible build command and supported
compiler distribution. The fixed source profile binds raw Git objects at
`aecf4a580c591e8f694a3699e19e843198089194`, 263 actual compilation modules,
267 source/configuration entries, direct imports and the complete pinned
Windows Lean executable/library inventory. Strict UTF-8 with CRLF replaced by LF
is the sole admitted serialization. BOMs, bare CR, invalid UTF-8 and every other
byte change reject. No comment, space or trailing newline is discarded.

`profile/BUILD_RECEIPT.json` records actual fresh compilation, and its literal
SHA-256 is in `scripts/packed_optimized_certificate_replay.ps1`. The production
profile API checks the fixed source-manifest pin, actual loaded build-driver pin,
fixed build-receipt pin, every dependency link and every resulting artifact hash.
Live inputs never choose their expected hashes. The old runtime receipt remains
an independently pinned historical record; it is not relabeled as this build.

An installer copies independent artifact bytes and assigns a common current
installation timestamp so the existing runtime freshness check also passes in
a fresh checkout. This timestamp is returned as `InstallationUTC`; original
compilation timestamps/results remain in the immutable receipt. Exact artifact
equality is claimed only for the documented Windows Lean distribution and
canonical relative-source build. Other platforms and compiler builds are
unexecuted. Raw source hashes are retained separately for restoration.

## Fresh LF and Windows production checkouts

First complete the documented canonical build or obtain a private byte copy of
its artifact directory. Use the externally pinned receipt value from the
committed certificate runner. Do not replace that pin with a hash selected from
a supplied file. With an exact committed repair candidate, run:

```powershell
powershell -NoProfile -ExecutionPolicy Bypass `
  -File docs/internal/extensions/opt1/repair-r1/prepare-checkouts.ps1 `
  -CandidateRef <exact-candidate-SHA> -Name reviewer `
  -BuildReceiptSHA256 <literal-candidate-receipt-pin> `
  -ArtifactDirectory <private-canonical-build>/.lake/build/lib/lean
```

The script refuses existing target directories. It creates detached private Git
clones `.lake/r1/reviewer-lf` and `.lake/r1/reviewer-windows` from that exact ref,
with `core.autocrlf=false` and `true` respectively. It uses ordinary Git checkout,
installs independent verified artifact copies, checks clean status, and records
the actual LF/CRLF counts of the historical mixed-newline source as a concrete
serialization witness. No historical editor bytes are reconstructed.

Run actual bounded startup and `A01-UNCHANGED` before the full campaign. The
production `-LibrarySelfTestOnly` and `-OnlyCase W28-stepBound` must each succeed
in both checkouts; the latter succeeds only after both mutated producers compile
and the unchanged expected-type consumer gives the intended rejection. The
repair registry runs those controls automatically. The full semantic campaign
may use the LF checkout, which is the declared canonical production profile.

## Registries and actual entry points

There are four independent exact registries:

| Registry | Count | Production entry point |
| --- | ---: | --- |
| Original runtime | 27 | `scripts/packed_optimized_runtime.ps1` |
| Original certificate | 80: two accepts, 39 deletions, 39 weakenings | `scripts/packed_optimized_certificate_replay.ps1` |
| Runtime repair | 53 | `runtime/replay.ps1` |
| Production provenance/boundary repair | 49: 21 profile, 10 certificate boundary, 9 repair boundary, 9 output verdict | `scripts/packed_optimized_replay_regression.ps1` |

Each registry is versioned, nonempty and checked against independent literal
IDs/counts. Each runner records expected/executed IDs. Omitted selectors choose
the full suite; a valid selector chooses exactly one case. Explicitly empty,
whitespace, padded, malformed and unknown selectors reject at the actual
parameter boundary. The new controls also omit or duplicate a middle registry
entry. There is no success path that executes an empty selected suite.

```powershell
# Run from the task root; both fixtures must be private Git clones below .lake.
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_replay_regression.ps1 `
  -RawCheckout .lake/r1/reviewer-lf `
  -WindowsCheckout .lake/r1/reviewer-windows `
  -ArtifactDirectory .lake/r1/reviewer-regression

powershell -NoProfile -ExecutionPolicy Bypass `
  -File docs/internal/extensions/opt1/repair-r1/runtime/replay.ps1 `
  -ArtifactDirectory .lake/r1/reviewer-runtime-controls

# From the installed LF checkout, after bounded startup and a known case:
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_runtime.ps1
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_certificate_replay.ps1 `
  -StageDeadlineSeconds 300 -CampaignDeadlineSeconds 14000
```

The profile negatives change a real source token, non-newline source whitespace,
artifact bytes/presence/mtime, configuration, manifest/receipt bytes and actual
production import publication. They also cover invalid UTF-8, BOM, bare CR and
the wrong executable. Three further controls add a foreign `Init.olean`, an
empty `Init` package directory and a `Backend.olean.server` sidecar. The profile
requires an exact dedicated artifact cache: no additional files or directories
may shadow a builtin library or supply an opportunistically loaded sidecar.
Each controlled mutation uses a private clone, preserves
the original raw bytes and mtime, restores in `finally`, and verifies exact
source/index/status restoration. Certificate semantic mutations instead run in
isolated copies with private producer outputs and a read-only dependency
snapshot. Shared caches are never mutable aliases.

`run-command.ps1` is the outer final-evidence adapter. Its versioned JSON plan
names the exact candidate, command, cwd, environment, limits, covered rows and
input paths. It requires a clean tracked checkout at that ref, retains actual
owned-process results, and verifies before/after raw inputs, tracked state and
index bytes. It does not convert timeouts, output overflow or a partial campaign
into success. Raw child logs and failed development attempts remain evidence.

## Verification and lifecycle

Run the preserved exact 93-root optimized axiom checker in a private checkout:
that existing script writes under its historical `composition-development`
directory. Copy only the new receipt into this repair directory. Do not run it
against the lead checkout and overwrite old evidence. Default `lake build` and
the explicit profile/consumer checks serve different coverage obligations.
One heavy Lean/Lake process runs at a time per private build tree.

The final worker report must exist before strict claim/design checks. Preserve
the original scanner roots, policy and root attributes. Record strict checks at
both exact base and governance refs, both hygiene scans, byte/blob preservation
and committed range whitespace checks. Coordinator aggregate certification,
fresh exact-commit blind audit and acceptance remain external stages. Neither
a commit nor a green local campaign is coordinator acceptance.

The plain-English change is that an intended diagnostic can no longer hide an
unrelated failure, and a fresh checkout can reproduce the checked compiler
inputs without recovering historical newline accidents. The mathematical
theorems, same allocation/word-width guards, ordered observation relation and
modeled constants remain unchanged. Compiler proof checking, model ticks and
native elapsed performance remain separate.

## Final evidence directory

`final/` holds the receipts of the campaigns executed on the implementation
freeze commit `f7cf20da8ae52c1f8295e5cedd4326bb8d44cbb3`:

| Path | Content |
| --- | --- |
| `final/plans/*.json` | The three versioned `run-command.ps1` plans (regression-49 from the task root; runtime-27 and certificate-80 from the LF fixture). |
| `final/regression-49/` | Adapter receipt for the 49-case production regression and, under `runner/`, the runner `RESULT.json`, identity, verdict, restoration and nested-failure receipts. |
| `final/runtime-27/`, `final/certificate-80/` | Adapter receipts and stream logs for the full production campaigns in the LF fixture. |
| `final/runtime-53/RESULT.json` | The 53-case runtime repair replay against the frozen production script. |
| `final/prepare-r1/` | Creation of the LF and Windows fixtures and both artifact installations. |
| `final/preservation-c1/` | Final-mode preservation receipt against the freeze commit (a later receipt against the evidence commit is committed after it exists). |
| `final/smoke/` | Development-loop bounded startup, library positives on both fixtures (pwsh 7.6.6 and Windows PowerShell 5.1) and the known A01/W28 selectors that preceded the full campaigns. |
| `final/lake-build/`, `final/lake-build-attempt1-wrong-flag/`, `final/axiom-union/` | `lake build` (one job through `LEAN_NUM_THREADS=1`; Lake 5.0.0 has no `-j` option, and the first attempt with `-j1` is kept as a recorded failure) on the frozen Lean tree, and the 93-root axiom union on the 263-artifact fixture. |
| `final/claim-scan-a/`, `final/claim-scan-b/`, `final/claim-scan-c/` | Strict claim-drift scans on the report-bearing tree: A passed, B is a recorded strict failure caused by storing A's raw hit log under `docs/` (a new claim surface), C passed on the final bytes with raw hit logs kept only in untracked scratch. Receipts hold summary lines and the scratch log's SHA-256, never the hit lines. |

The registry is `opt1-r1-production-v4`; v4 only corrected the `R01-OMITTED`
definition text of v3 (46 to 49) and repinned the registry hash. The production
campaigns ran under pwsh 7.6.6; one library positive was also executed under
Windows PowerShell 5.1 (slower: about 465 s against about 130 s, because the
profile hashes the complete toolchain inventory twice per invocation).

Post-evidence receipts: `final/preservation-c2/` is the final-mode preservation run against evidence commit `d766e84b22c933a852d90cdb44ac123819fe75a4`; it FAILED with `ROW_DUPLICATE` because the matrix evidence appendix reused the frozen row-key cell format (fixed by relabelling the appendix rows `Evidence for`). The run against the corrected commit is committed separately as `final/preservation-c4/`, because a receipt cannot certify the commit that contains it.

`final/preservation-c4/` is the final-mode preservation run against the corrected evidence commit `2b229867b864e1e91da901bd3fcb728612209964` (result `PASS/17/510/True`).
