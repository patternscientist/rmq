# LIFE-NATIVE-1 command-to-row ledger

This is a local execution index, not coordinator acceptance. `PASS` below means
the named completed receipt reports success, integrity and cleanup. `PENDING`
does not infer success from an earlier source, discovery or command plan. Update
only the status/receipt cell after inspecting the complete actual result.

## Common invocation and frozen inputs

Working directory: `C:/Users/poin/.codex/worktrees/44d6/RMQ`.
Base: `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`.
Governance: `7b227c49ef2ec044b702126cc41c9add847eed01`.

Each command cell below gives `<script> <arguments>` for the exact common prefix
`& $Pwsh -NoProfile -File`. Variables expand from this block; no newest-directory
selection or implicit replacement receipt is used.

```powershell
$Pwsh = 'C:/Users/poin/.cache/codex-runtimes/codex-primary-runtime/dependencies/native/powershell/pwsh.exe'
$E = 'docs/internal/extensions/lifecycle-native1'
$L = '.lake/lifecycle-native1'
$LeanRoot = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0'
$RustRoot = 'C:/Users/poin/.rustup/toolchains/stable-x86_64-pc-windows-msvc'
$LeanReceipt = "$L/runs/build-20260927T062313663/RESULT.json"
$ClientReceipt = "$L/runs/build-20260927T064222779/RESULT.json"
$LeanWhy = 'Standard four-root refresh after Q10 fixed-proposition consumer proof-body repair; narrow consumer compiled with unchanged runtime sources.'
$NativeWhy = 'Prior actual native maximum 6.82s; 120s permits cold runtime and host scheduling margin; exact ordinary exit, complete streams, pins and cleanup remain required.'
$ControlWhy = 'Current refreshed native fixture maximum 8.15s; 120s permits cold runtime and host scheduling margin; exact ordinary exit, complete streams, pins and cleanup remain required.'
$ExportSHA = '8688e2089ff225de19b741327af451eef2c019f0997e4652dfccecd181b0c542'
$AxiomSHA = 'a9b0ffcd5c9527d18936d2f76a6afc4964d517c47743e895f86a1c6a59d78895'
$NativeSHA = 'e67348c7e631fb7facbd9b580a44d1b42729e9db0526a5ac09a2b804143e5466'
$RustSHA = '985835ed2ac39483dae006c327f656a0fd92546d60c91ef97122f67b6d795141'
```

The runners' omitted `LeanRoot`/`RustRoot` defaults are exactly those paths.
PowerShell executable SHA256 is
`362a356ce7f0940ec74f73a8fc2c990a2cc24a38a11c90bbd8eca947110ad139`.
The current clients receipt records Lean 4.22.0, commit
`ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`, Windows GNU x64; Rust 1.89.0,
commit `29483883eed69d5fb4db01964cdf2af4d86e9cb2`, Windows MSVC x64; and
Cargo 1.89.0, commit `c24e1064277fe51ab72011e2612e556ac56addf7`.
These labels supplement the actual executable/import hashes in the receipts.
The inherited native identity helper's version text uses returned lines; exact
raw Lean-version verification is separately required by `default_build.ps1`.

Native compiler defaults are Lean's `bin/clang.exe` for generated C,
`C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/Llvm/x64/bin/clang.exe`
for clients, and `C:/Program Files/Microsoft Visual Studio/2022/Community/VC/Tools/MSVC/14.44.35207/bin/Hostx64/x64/`
`lib.exe` / `link.exe` for import libraries / Rust linking. The clients receipt
binds the resolved tool closure; executable names alone are not provenance.

The frozen independent export consumer SHA256 is
`4075aa30a3587995091debe002aea8ca0b111dddbf210082f0e9a019fd6314c2`;
the 34-case registry SHA256 is
`15034dc9ce6e6077d27487bc4dddd7990cef6b39c66de39dff2d9be8a6825660`.
The standard Lean receipt SHA256 is
`c68286c3166128c0794f8ad9f790c37da7687f62d6a873a0dab4d3cd3eee99b1`;
the current clients receipt SHA256 is
`6dd359050473a2604ab6370ef65813ba90ef0f3b4acd3ffaa776a08118caf699`.
The Lean/native/compiler runners acquire
`Local\RMQLifecycleImplementationHeavy20260920`; execute those commands
sequentially under the assigned slot.

All receipt paths in the following tables are relative to `$L` and end in
`RESULT.json`. Full commands, child arguments, deadlines, ordinary exits,
timeout/overflow state, raw captures and finalizers are in those receipts.

## Current formal and native producers

| ID / acceptance rows | Script and arguments after the common prefix | Actual receipt / outcome |
| --- | --- | --- |
| L01 — CHK-LEAN, N1-01, N1-18 | `scripts/lifecycle_native_build.ps1 -Phase lean -LeanDeadlineSeconds 900 -LeanDeadlineRationale $LeanWhy` | PASS `runs/build-20260927T062313663/RESULT.json`; four default roots, 5,979 pins. |
| N01 — CHK-NATIVE, N1-11..12, N1-23 | `scripts/lifecycle_native_build.ps1 -Phase dll -LeanReceipt $LeanReceipt` | PASS `runs/build-20260927T063830290/RESULT.json`; five producer children, 7,091 pins. |
| N02 — CHK-NATIVE, N1-19, N1-23 | `scripts/lifecycle_native_build.ps1 -Phase clients -LeanReceipt $LeanReceipt` | PASS `runs/build-20260927T064222779/RESULT.json`; eight producer children, 7,143 pins. |
| N03 — N1-11..12, CHK-NATIVE | `scripts/lifecycle_native_replay.ps1 -Phase Startup -BuildReceipt $ClientReceipt -Variant production -CaseDeadlineSeconds 120 -DeadlineRationale $NativeWhy` | PASS `replay/20260927T064556967-9557393a/RESULT.json`; current startup/initialized closure. |
| N04 — N1-06, N1-18, CHK-NATIVE | `scripts/lifecycle_native_replay.ps1 -Phase Fixtures -Cases LN1-W-TIES -BuildReceipt $ClientReceipt -Variant production -CaseDeadlineSeconds 120 -DeadlineRationale $NativeWhy` | PASS `replay/20260927T064716438-5960f47b/RESULT.json`; exactly one fixture, both modes. |
| N05 — N1-06, N1-18, CHK-NATIVE | `scripts/lifecycle_native_replay.ps1 -Phase Fixtures -BuildReceipt $ClientReceipt -Variant production -CaseDeadlineSeconds 120 -DeadlineRationale $NativeWhy` | PASS `replay/20260927T064849543-b1d28b93/RESULT.json`; all 13 fixtures, 26 native processes, 142 requests/publications. |
| N06 — N1-03, N1-15, CHK-NATIVE | `scripts/lifecycle_native_replay.ps1 -Phase AbiBoundaries -BuildReceipt $ClientReceipt -Variant production -CaseDeadlineSeconds 120 -DeadlineRationale $NativeWhy` | PASS `replay/20260927T065401229-f97e3be7/RESULT.json`; one native process, all 23 internal ABI cases. |
| N07 — N1-19, CHK-NATIVE | `"$E/native_clients.ps1" -Phase Run -BuildReceipt $ClientReceipt -CaseDeadlineSeconds 120 -DeadlineRationale $NativeWhy` | PASS `clients/20260927T065517097-e55bf689/RESULT.json`; all ten C++/Rust clients. |

L01's four default roots are `RMQ.Core.WordRAM.Native.Lifecycle`, its
`Observations` and `AdmissionContract` modules, and
`RMQ.Validation.LifecycleNativeContract`. Its 900-second limit follows the
measured narrow proof repair; the actual refreshed Lean child took 0.890313 seconds,
with 3.113 seconds for its capture launcher.
Native producer defaults retain 300 seconds for compile/link/Rust stages,
with actual import-library stages at 60 seconds and C/C++ client stages at
120 seconds. No aggregate timeout replaces these per-stage bounds.
The fresh native fixture maximum was 8.148 seconds; the later controls use the
updated `$ControlWhy` while the original refresh commands retain `$NativeWhy`.
See `NATIVE_REFRESH_EVIDENCE.md` for exact source/derived-C/artifact comparisons.

## Cheap caller, stream, mapping and cleanup controls

These are caller/helper controls, not native or Lean semantic execution.
All ordinary caller deadlines are 30 seconds, based on measured roughly
2–5-second PowerShell calls. The owned descendant controls deliberately use
an 8-second inner / 30-second outer bound; the export selftest's owned descendant
uses 6 seconds. Only the export selftest acquires the shared heavy mutex.

| ID / acceptance rows | Script and arguments after the common prefix | Actual receipt / outcome |
| --- | --- | --- |
| C01 — N1-20..21 | `"$E/native_selector_controls.ps1"` | PASS 33 controls, `selector-controls/20260927T063333385-e85600e9/RESULT.json`. |
| C02 — N1-21 | `"$E/native_client_selector_controls.ps1"` | Retained PASS 13 controls, `client-selector-controls/20260923T093748354-584c85f0/RESULT.json`; unchanged-source applicability reviewed in `NATIVE_CLIENT_SELECTOR_EVIDENCE.md`. |
| C03 — N1-21 | `"$E/native_control_selector_controls.ps1"` | PASS 18 controls on the repaired runner, `control-selector-controls/20260927T070655548-bc3d2d0d/RESULT.json`. |
| C04 — N1-21 | `"$E/rust_misuse_selector_controls.ps1"` | PASS 15 controls, `rust-selector-controls/20260927T063015001/RESULT.json`. |
| C05 — N1-20..23 | `"$E/native_recipe_controls.ps1"` | PASS 11 complete-recipe controls, `native-recipe-controls/20260927T071017981-3341822f/RESULT.json`. |
| C06 — N1-20..22 | `"$E/export_mutation_replay.ps1" -Mode Discovery -SelfTestOnly` | PASS 15 controls, `export-mutations/20260927T062447298-5d548bf4/RESULT.json`; includes ordinal multi-selection and owned-descendant termination. |
| C07 — N1-20, CHK-REPORT | `"$E/final_stream_controls.ps1" -Mode Replay` | PASS 15 output-language controls, `final-stream-controls/20260927T064348259-8b9ba5b5/RESULT.json`. |
| C08 — N1-21 | `"$E/final_stream_mapping_controls.ps1"` | PASS five actual mapping callers, `final-stream-mapping/20260927T064730316-bd56c224/RESULT.json`; both full mappings independently hash-guarded. |
| C09 — N1-20, N1-22 | `"$E/owned_descendant_control.ps1"` | Retained PASS three timeout/partial-setup controls, `owned-controls/20260923T091922860-5b5f618f/RESULT.json`; Windows job barrier and exact applicability limits in `OWNED_DESCENDANT_CONTROL_EVIDENCE.md`. |

## Discovery and frozen semantic replay

Omitted selectors in these complete campaigns select the full frozen roster.
Discovery records observations; independent root review freezes manifests;
Replay must match their complete expected outcomes and raw diagnostics.
Changing source/tool/artifact identities requires explicit new applicability.

| ID / acceptance rows | Script and arguments after the common prefix | Actual receipt / outcome |
| --- | --- | --- |
| F01 — N1-01, N1-05..06, CHK-LEAN, INV-CERTIFICATE-ANTI-BYPASS | `"$E/export_mutation_replay.ps1" -Mode Discovery -BuildReceipt $LeanReceipt -DeadlineSeconds 180` | PASS all 34, `export-mutations/20260927T070116393-4514a722/RESULT.json`; 66 producer stages, 32 consumer rejections, two accepts, 5,618 pins. |
| F02 — same rows, INV-MUTATION-REPRODUCIBILITY | `"$E/export_mutation_replay.ps1" -Mode Replay -BuildReceipt $LeanReceipt -DiagnosticsPath "$E/EXPORT_DIAGNOSTICS.json" -DiagnosticsSHA256 $ExportSHA -DeadlineSeconds 180` | PASS all 34, `export-mutations/20260927T084110803-e9431c50/RESULT.json`, SHA256 `341c44469ecb17b4eebb2b45341a71ef8120a3b12fd0d2104496998b30d58866`; 66 ordinary-zero producers, 32 intended rejections, two accepts, all 50 diagnostic objects and complete raw streams match F01's root-frozen manifest; 5,619 pins and cleanup. |
| A01 — CHK-LEAN, N1-18 | `"$E/axiom_inventory.ps1" -Mode Discovery -BuildReceipt $LeanReceipt -DeadlineSeconds 600` | PASS all 21, `axioms/20260927T072200262/RESULT.json`; only permitted Lean axioms, 5,604 pins. Exact per-declaration sets in `PROOF_EVIDENCE.md`. |
| A02 — CHK-LEAN | `"$E/axiom_inventory.ps1" -Mode Replay -BuildReceipt $LeanReceipt -FrozenInventory "$E/AXIOMS.json" -FrozenSHA256 $AxiomSHA -DeadlineSeconds 600` | PASS all 21, `axioms/20260927T085337097/RESULT.json`, SHA256 `b298894304173a52874593ee066aea530c55574aa2897aa3a14f5cc9918a967f`; ordinary zero in 18.961109 seconds, all exact sets and complete 6,693-byte stdout match the frozen inventory, empty stderr; 5,605 pins and cleanup. |
| N08 — N1-05..06, N1-20..23, CHK-NATIVE | `"$E/native_controls.ps1" -Mode Discovery -Cases NC-NONE-BUILD -BuildReceipt $ClientReceipt -CaseDeadlineSeconds 120 -DeadlineRationale $ControlWhy` | PASS repaired-recipe focus, `native-controls/20260927T072450429-92e7bea9/RESULT.json`; exactly one case, not full registry completion. |
| N09 — same rows, INV-MUTATION-REPRODUCIBILITY | `"$E/native_controls.ps1" -Mode Replay -BuildReceipt $ClientReceipt -ExpectationsPath "$E/NATIVE_EXPECTATIONS.json" -ExpectationsSHA256 $NativeSHA -CaseDeadlineSeconds 120 -DeadlineRationale $ControlWhy` | PASS all 48, `native-controls/20260927T073240346-3c38ea74/RESULT.json`, SHA256 `a4545cfc2df8cfde3e92d27c4d7f6cc59c67946dbdae939d3e5c4739d60754e4`; 7638 integrity pins and cleanup. Full current recipe reproduces unchanged cases. Earlier collapsed-fingerprint runs are historical. |
| R01 — N1-19..23, CHK-NATIVE | `"$E/rust_misuse_replay.ps1" -Mode Discovery` | PASS current all 17, `rust-misuse/20260927T072740867/RESULT.json`; 111 pins. Root's current provenance rebind preserves all 17 complete diagnostic cases. |
| R02 — same rows, INV-MUTATION-REPRODUCIBILITY | `"$E/rust_misuse_replay.ps1" -Mode Replay -DiagnosticsPath "$E/RUST_DIAGNOSTICS.json" -DiagnosticsSHA256 $RustSHA` | PASS all 17, `rust-misuse/20260927T073749082/RESULT.json`, SHA256 `921ceca64185a1ed5950ec219ed5ff3c0c3451bdd14c6507205f71af38844f5d`; 15 expected rejections, two accepts, 112 integrity pins and cleanup. |

Export stages retain 180 seconds each. F01 took 1,202.241 seconds overall;
that duration informs scheduling and is not a child deadline or success rule.
F02's successful complete retry took 712.944 seconds. Its earlier attempt,
`export-mutations/20260927T074439300-7ff52e82/RESULT.json`, SHA256
`71d77f10e3eb6b8aace2c2f78e81ba41645628353567ed1f667ae06451e0ec06`,
failed at E05 after a recorded battery-triggered system sleep. Four cases had
passed, but E05 had no ordinary consumer exit; all 5,619 pins and cleanup passed.
That failed attempt is retained as failure evidence, not an accepted rejection.
After the battery-sleep interruption of the first F02 attempt, the same command
with `-OnlyCase EX-WEAK-E05-HALTED` passed at
`export-mutations/20260927T083821597-51bfd2c5/RESULT.json`, SHA256
`41ede20ddd3b154cfef2b1b041411164c3ebac42fe3bf709e62178d377bd5eab`.
Both producers returned ordinary zero with empty streams; the consumer returned
ordinary one in 7.050421 seconds with all four frozen diagnostics and complete
raw streams equal. All 5,619 pins and cleanup passed. The root independently
reviewed this focused recovery before the complete retry. The failed attempt's
`sleep-interruption/SYSTEM_EVENTS.xml`, SHA256
`671251f2530b39c0ebae3d4e0d50865cdc4d24db8d68a880f85218c06f34d696`,
records the battery sleep and resume; neither the deadline nor expected outcome
was relaxed. This one-case recovery is distinct from full F02 completion.
Axiom stages retain 600 seconds with warm-import/cold-host margin; A01's actual
compiler took 34.811 seconds. Rust producer and independent misuse compiles have
60-second ceilings. All use the existing owned-process facility and preserve
ordinary exit, timeout/overflow, complete raw stdout/stderr, pins and cleanup.

## Final certification and external delivery receipt

| ID / acceptance rows | Script and arguments after the common prefix | Actual receipt / outcome |
| --- | --- | --- |
| Z01 — CHK-LEAN, N1-22..23 | `"$E/default_build.ps1"` | PASS `default-build/20260927T074010540/RESULT.json`, SHA256 `3b4a40505c289403d28c71520a57c112a1a573ea7196ed13e31c1af8bf5a1eaf`; ordinary zero, 207.869-second build, 6,056 pins and cleanup. Executed after implementation, full discoveries and native/Rust replays, before final export/axiom Replay. Default 3,600-second ceiling; no target list supplied. |
| Z02 — CHK-SCOPE, CHK-REPORT, N1-20..23 | `"$E/final_checks.ps1"` before commit, then `"$E/final_checks.ps1" -Committed` after commit | The external delivery receipt is the authority for the actual outcomes, receipt paths and pins of both final invocations. Checks cover strict exact-base design, unchanged-policy changed-surface claims, scope/startup exception, hygiene, working/committed whitespace and, after commit, clean-tree state. |

Z02 gives each checker 600 seconds, from measured scope 91.142 seconds and
strict claim scan 178.106 seconds with margin for the final frozen JSON/prose.
Development component runs are not relabeled as Z02. Final HEAD, report hash,
source commits, commands/results and reused-evidence applicability must be
bound separately by the external delivery receipt, without recursive self-hashes.

The `.lake` receipts, binaries and raw logs are retained local evidence and are
ignored by Git. The replay scripts, literal mutation/selector registries,
root-reviewed expectation manifests and these evidence notes are candidate
versioned sources to include in the final commit. A receipt citation alone does
not replace committed replay sources. This ledger introduces no new theorem,
runtime guarantee, design decision or acceptance exception.
