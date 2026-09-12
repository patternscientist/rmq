# NATIVE-1 command and coverage ledger

Platform: Windows x64, OS build 10.0.26200. All work uses exact baseline
`0e6a00f654abc64f8b68988fa9675b9a839dca2f` plus the owned NATIVE-1 delta.
`NATIVE_BUILD_MANIFEST.json` pins the source bytes and delivered DLL/Rust
executable; `GENERATED_SOURCE_PINS.json` pins generated C and Lean artifacts.
Final implementation commit is recorded in REPORT.md. No shared mutable cache
was used. The compiler and executable children are owned by Windows jobs.

| Role / covered rows | Command or stage | Deadline and outcome | Durable evidence |
| --- | --- | --- | --- |
| Startup / governance | Exact project skill preflight requiring rmq-proof-sprint and actual three-skill runtime catalog | PASS at clean exact base; no stale/missing skill | ACCEPTANCE_MATRIX.md; FINITE_LEAF.md |
| Development / FINITE | Direct pinned Lean -j1 for six baseline imports and Native/Finite.lean | Six prerequisites pass, initial elaboration fixes then finite-leaf-04 exit 0 in 14.32s; 120/300s owned deadlines | FINITE_LEAF.md quotes each command/result |
| Development / trace erasure | Direct Lean -j1 Native/Thin.lean | First syntax/layout error; thin-02 exit 0, 21.283s/120s | commands/thin-01.json and thin-02.json |
| Development / source/encoding | Direct Lean -j1 Native/Route.lean | Initial source check exit 0, then final build checks current added declarations | commands/route-01.json; build records |
| Development / actual source toolchain | scripts/packed_native_build.ps1 | Four diagnosed build attempts: suffix-path bug; absent general C headers; initial-state field elaboration; undeclared runtime-init prototype. Each failed stage has nonzero exit. Final attempt succeeds, reusing only hash-verified task-local Lean/C outputs, linking DLL in 19.068s and Cargo release in 9.485s | commands/build-20260912T072514256.json through build-20260912T074238729.json |
| Startup / host boundary | Native smoke in sandbox; argument-only executable probe in sandbox | INCOMPLETE at 120.214s/120s and 15.146s/15s; almost no CPU, no output; recorded job descendants cleaned | commands/route-20260912T074345564.json; loader-emptyargs.json |
| Startup / host boundary | Unchanged argument-only probe outside sandbox | Expected exit 2 and usage stderr in 4.603s/15s; authorized host execution isolates environment difference | commands/loader-emptyargs-host.json |
| Development / CODE, CONTROLS | Host scripts/packed_native_route.ps1 -Case smoke; then -Case n9-full | Both PASS within owned 120s deadlines; known startup precedes full registry | commands/route-20260912T074851905.json; route-20260912T074921501.json |
| Phase registry / CODE, CONTROLS, replay invariants | Host scripts/packed_native_route.ps1 with selector omitted | PASS 14 expected / 14 executed, exact ordered IDs, no dropped cases. Core mutation fails at routeCore_source's exact proof line; bytes/diff restored | commands/route-20260912T075047091.json |
| Boundary controls / replay invariants | Host scripts/packed_native_controls.ps1 | PASS 8 expected / 8 executed: empty, whitespace, malformed, unknown; missing source/artifact/fixture; restored positive smoke | commands/controls-20260912T075336106.json and restored-smoke receipt |
| Exact typed consumers / trust | Direct pinned Lean -j1 scripts/packed_native_types.lean | PASS 6.105s/120s. Thirteen axiom inventories contain only propext, Quot.sound, Classical.choice; numeric instruction decode is axiom-free | commands/exact-types-01.json |
| C++ consumption / API phase evidence | MSVC lib.exe import library; Visual Studio clang C++17 example; host example on exact n9-full | Import library and C++ build pass; example exits 0 in 14.8s/120s and every reference output line compares equal | commands/cpp-import-library.json, cpp-build.json, cpp-n9-full.json |
| Trust hygiene | Both prescribed rg scans over RMQ and lakefile.toml | Exit 1 means zero matches in each scan, not failure. No new source trust token or native-decision shortcut | commands/hygiene.json |
| Conditional public prose | scripts/claim_drift_scan.ps1 -Strict | PASS, 1590 review/allowed hits, 0 strict failures, 79.016s/180s | commands/claim-drift.summary.json; exact complete receipt compressed losslessly in claim-drift.json.gz |
| Final phase policy | git diff --check; committed base..HEAD range; strict design policy with exact Base | Required before submission; final outcomes recorded in REPORT.md | Phase final command receipts |
| Full candidate / all rows | lake build; final Native/Capstone and PackedNative validator; full final campaign; aggregate certification; blind audit | NOT RUN in route phase: named capstone/limb/binary implementation remains open, broad gate requires coordinator host slot | No pass or acceptance inferred |

The full claim scan preceded evidence-only additions to the matrix/route packet;
the public FAMILY_SUMMARY/DIGESTION_LOG wording is the same source content.
Focused strict scans cover any later packet/native README edits. The source
implementation, DLL and Rust binary did not change after the successful native
registry. C++ example/import-description additions do not affect that runtime
or the Lean dependency closure. No unchanged full replay was repeated as final
certification.

The generic command wrapper preserves complete stdout/stderr in the receipt
and limits console display to its last twenty lines. The large claim receipt
was compressed losslessly, with raw/archive lengths and SHA-256 in its summary.
No diagnostic content was discarded from the durable record.

Uncovered: non-Windows native execution and process-tree behavior; final native
binary/limb limits and comprehensive controls; final canonical capstone audit.
The sandbox timeouts are neither semantic counterexamples nor passes. No broad
aggregate gate slot is requested for this route review.

Final source-byte normalization was followed by build receipt `build-20260912T080927170.json`; all Lean/C artifacts were reused only after their source-prefix and artifact hashes matched. The final native registry receipt is `route-20260912T081311355.json` (14/14), the final control receipt is `controls-20260912T081542413.json` (8/8), and `cpp-n9-full-final.json` records the exact C++ comparison against the current DLL. These supersede earlier successful native receipts for final phase artifact identity; earlier runs remain development evidence. `PHASE_RESULTS.json` is the compact index.

The focused packet claim scan passed with 31 review/allowed hits and zero strict
failures (`claim-drift-packet.json`). The focused native README scan first
rejected a runtime-lifetime sentence because its line did not state the modeled
cost distinction (`claim-drift-native-readme.json`). The sentence now explicitly
separates Lean runtime lifetime from modeled operation costs. The focused rerun
passed with one allowed hit and zero strict failures in 7.815s/120s
(`claim-drift-native-readme-fixed.json`). Both receipts are retained; this prose
repair changes none of the build-manifest source bytes.

The implementation-range whitespace check passed after commit 3329a6e
(`committed-diff-phase.json`). Strict design checking with the exact base failed
closed in 10.99s/120s: 28 new native paths have no classification rule
(`design-phase.json`). The shared classifier is outside this worker's write
scope; no design-policy pass or waiver is claimed. Coordinator disposition is
required. `phase-integrity.json` verifies the frozen prefix and all source and
artifact hashes against the implementation commit's current files.

The continuation packet review clarified that the eight selector/manifest
controls call the actual route script in-process. They cover PowerShell script
parameter binding, not OS command-line serialization. The stronger final
process-boundary check in the frozen replay requirement remains open.

The finished REPORT.md was scanned explicitly with `-Strict
-IncludeProcessRecords -Path docs/internal/extensions/native1/REPORT.md`:
PASS, one allowed hit and zero strict failures, 5.358s/120s
(`claim-drift-report.json`). All 31 frozen acceptance IDs appear in the report;
the initial matrix prefix was rechecked unchanged after its final appendix.

## Loaded-image continuation checkpoint

The first production binary build passed (`binary-build-20260912T111100924.json`).
`BINARY_BUILD_MANIFEST.json` preserves its exact 31-source, 19-generated-C and
three-artifact inventory, with `native1-toolchain-v2` identity digest
`8DF566C7330ED567CDBDE84504EC261D1FB26EA713E4BF6034ECA7B0A20751C7`.
The full identity enumerates 4856 Lean, 48 Rust, 6545 C++ dependency, 145 tool-runtime
and four external executable files. Its ordered effective search roots and
explicitly absent optional directories remain part of the identity.

The independent startup checks rehashed every source/generated-C/artifact pin
before execution. The Rust and C++ clients each loaded the same 146-byte,
168-bit image and produced exactly 24 bytes, including the final blank line:
`halted 8\n2\n0 1 0 0 0 1\n\n`. Their exit codes were zero and stderr was empty.
The owned native durations were 0.266s and0.453s. Exact input/expected bytes and
raw process receipts are in `binary-commands/startup-packed-rmq-native.exe.json`
and `binary-commands/startup-packed-rmq-native-cpp.exe.json`. These are bounded
startup checks, not the complete-path or mutation campaign.

The source 42-field capstone and all 42 independently written literal consumers
passed before this build. The executable Lean validator elaborated in 10.122s,
then ran its complete 16-case roster in 6.710s with 16/16 passing. The semantic
occurrence proofs and exporter also elaborate; their full witness export is
still running. Full certificate/native campaigns, the complete axiom inventory,
blind exact-commit audit and scheduled aggregate certification remain pending.
## Version-3 source and native verification

This section supersedes operationally pending statements in the earlier dated checkpoints; the older receipts retain their original source/toolchain identities. The current source snapshot includes the 42-field Capstone, all 42 literal field consumers, public exact-type consumer, seven operational witness fixtures and the new semantic validator. Exact final commits are recorded in the final report and audit packet.

| Role / requirement | Actual command or stage | Deadline and outcome | Durable evidence |
| --- | --- | --- | --- |
| Effective build identity | Version-3 actual identity predicates, selectors and ordinal cross-shell controls | PASS, 20 predicates plus six actual selectors; full wrapper 214.817s/600s; PS5/PS7 canonical digest equal | `binary-commands/identity-v3-final-wrapper.json` and the recorded control receipts |
| Production native compilation | `scripts/packed_native_binary_build.ps1` | PASS, all 19 Lean/C module stages plus DLL, Rust, import-library and C++ stages; initial identity collection slow but uninterrupted | `commands/binary-build-20260912T122050486.json` |
| Immutable build inventory | Rehash all 31 source inputs, 19 generated-C modules and three native artifacts | PASS, version-3 identity digest `2E1772C727BBEB16A0B65CFEA6902C74E8184A49CF483D65DF482A8177D84402` | `BINARY_V3_BUILD_MANIFEST.json`, `commands/binary-v3-integrity.json` |
| Actual startup selector | Binary replay `-Case query-smoke`, both clients | PASS, 86.639s/600s; each exact 24-byte stdout, zero exit, empty stderr | `binary-commands/binary-v3-calibration-query-smoke-20260912T125624257.json`, inner `binary-replay-20260912T125636041.json` |
| Actual complete-path calibration | Binary replay `-Case pq1-n9-full`, both clients | PASS, 164.828s/600s; each exact 4,523-byte stdout from the 70,854,686-byte image | `binary-commands/binary-v3-calibration-pq1-n9-full-20260912T125906228.json`, inner `binary-replay-20260912T125916442.json` |
| Default dependency preparation | `scripts/packed_native_hydrate.ps1 -DefaultRMQ` | PASS, 189.603s copying exactly 491 missing files/133,498,087 bytes; 997 existing artifacts preserved; all 372 source modules and copied hashes checked | `commands/hydrate-default-20260912T125020579.json`, `hydrate-default-command-03.json` |
| Dependency/output compatibility | Pinned Lake `--no-build build RMQ`, `LEAN_NUM_THREADS=1` | PASS, 20.956s/300s | `commands/default-cache-validation.json` |
| Required default build | Pinned Lake `build`, `LEAN_NUM_THREADS=1` | PASS, 3.980s/300s; default root has no Native imports | `commands/final-default-build.json` |
| Explicit Native closure | Pinned Lean `-j 1 scripts/packed_native_final_types.lean` with checked local library path | PASS, 7.734s; all 28 Native modules, literal consumers and axiom-inventory module imported | `commands/final-native-imports.json` |
| Explicit new validator | Pinned Lean `-j 1 scripts/packed_native_validator_import.lean` separately from witness global main | PASS, 6.128s | `commands/final-validator-import.json` |
| Stock trust inventory | Pinned Lean on `RMQ/Core/WordRAM/Native/AxiomChecks.lean` | PASS, 86 inventories in 141.177s/300s; only `propext`, `Classical.choice`, `Quot.sound` | `commands/native-axioms-02.json` |
| Semantic validator and process boundaries | Omitted `scripts/packed_native_validator_controls.ps1` | PASS, 24/24 in 257.464s; real empty argument/environment, exact bytes, malformed/oversized/UTF-8/newline controls; no timeout or output limit | `commands/validator-controls-20260912T130117776.json`, `validator-durable-all-02.json` |
| Fresh producer binding calibration | Contract `-Case baseline`, then `-Case field-n01` | PASS, 31.464s and 30.119s; baseline consumer accepts, weakened producer compiles and exact literal consumer rejects at line 12:2; all hashes and Git state restored | `binary-commands/contract-replay-20260912T132003337.json`, `contract-replay-20260912T132210348.json` |

The default-library preparation is a physical task-local copy, not a shared mutable cache or a change to another checkout. The original 249-module hydration route remains unchanged. Two zero-copy preparation failures are preserved: a whole-file import regex matched a documentation sentence, then PS5 progress formatting failed on an ordered dictionary. The source-derived import-header parser and progress computation were repaired before any successful copy, and Lake subsequently validated dependency/output compatibility.

The version-2 production selector rejected identical tool inventories serialized in different shell-dependent orders. Version 3 fixes unordered inventory ordering and checks stable command metadata while retaining ordered effective search roots. Neither that failure nor historical version-2 build/startup observations certify the version-3 binaries. The current manifest is exactly 2,779,460 bytes, SHA256 `A4C20BCAA5E35402293DB522CE8736A81BD84FBC67FC2648693475504E5E1069`.

The first full validator control attempt timed out on malformed fuel after earlier controls passed. Its cause was not established. Owned descendants were cleaned; focused PS5 and PS7 reruns produced the expected rejection, then the complete unchanged control roster passed. The initial stock axiom attempt also exceeded its short 45-second deadline; a capstone-only measurement informed the successful 300-second inventory deadline. All unsuccessful attempts remain separate from successful evidence.

The first contract baseline failed before its consumer because a partial RMQ import overlay shadowed the rest of that package. The complete private package repair preserves the frozen 44-case/nine-control semantics, uses one physical dependency copy per run, and binds each newly compiled producer by hash before and after the untouched consumer. The focused negative output differs from the shared baseline object; shared checked objects remain unchanged. Independent internal mechanism review found no concrete gap. Full-campaign outcomes are recorded in the next final ledger section after restoration.

## Final owned-candidate results

The full native campaign passed 128/128 controls in 2337.505 seconds within its
7200-second owned deadline. Its single omitted full109 child passed all214
ordered results in 1665.969 seconds within3600 seconds:208 ordinary observations
from104 cases in both clients, two actual FFI mutant observations and four
source challenges. The unchanged FFI baselines are nested evidence and do not
inflate that count. Runtime fuel, loader input and query argument mutations
failed at the exact Runtime44:2, Entry23:64 and Entry36:2 proof surfaces.
The isolated FFI build took47.977 seconds; both clients then matched the exact
independently expected swapped-argument fault. Every source/Git/artifact and
all19 generated-C restoration checks passed. The full receipts and byte hashes
are indexed in BINARY_VALIDATION.md and the final matrix appendix.

The certificate campaign passed nine/nine controls in816.151 seconds, including
one omitted44 replay in736.532 seconds. All44 producers compiled; the baseline
consumer accepted and all43 weakenings failed at their designated literal
consumer lines. Fresh/private-before/private-after producer hashes agree for
every case, and every negative differs from the shared baseline. The410-file
private copy, source/registry/Git restoration and unchanged shared objects are
recorded in CONTRACT_VALIDATION.md and its exact receipt/inventory files.

The independent final-integrity check rehashed all31 source inputs,19 generated
C files and three delivered artifacts, verified the unchanged matrix prefix,
reconstructed all214 ordered results from the frozen109 registry, compared all
210 raw stdout/stderr/exit observations (including both FFI mutants), and checked
all128 controls,44 contract cases/nine controls and fresh producer bindings.
It passed; commands/final-integrity.json retains its exact script, inputs and
output pins for replay.

Both required trust scans returned zero matches. Strict design against the exact
base passed in7.460 seconds; working, staged and committed whitespace checks
passed. The default-root claim attempt timed out at302.574 seconds while
rescanning prior scanner output in archived JSON. Its full unsuccessful receipt
and cleaned owned PIDs remain recorded. The unchanged production Strict rules
then passed all44 maintained public paths (403 hits, zero failures,10.380 seconds)
and26 process paths (415 hits, zero failures,7.856 seconds). The corpus includes
every changed authored claim document, all18 current-fact paths and all16
required-attribution paths; its exact list and source bytes are pinned in the
final claim receipts. No rule/allowlist changed and no default-root pass is
claimed. WDD-20260912-NATIVE1-012 records the source-based scope diagnosis.

The final report and appended matrix are checked again after their final text
is present. Fresh blind exact-commit audit and the single coordinator-scheduled
aggregate certification remain the external acceptance phase. The worker
records CANDIDATE_COMPLETE only; no branch was pushed or merged.
