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
