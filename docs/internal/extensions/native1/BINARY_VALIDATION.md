Status: CANDIDATE_COMPLETE
Phase: BINARY_REPLAY_RESTORED

This is the bounded binary-native validation leaf of NATIVE-1. It does not
rewrite the original 31-row acceptance matrix and cannot accept the full
native capstone. Worktree `C:/Users/poin/.codex/worktrees/1817/RMQ`, branch
`codex/native-1-packed-execution`, reviewed checkpoint
`c8c266f987d46284382cc93c5fa8e01bd7a9ffb9`, governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
The same canonical `rmq-proof-sprint` preflight and completion gate apply.
The earlier registry producer is recorded separately in `REGISTRY_REPAIR.md`.

## Current bounded outcome

The frozen 109-case binary registry passed in one omitted-selector execution:
all 214 expanded result rows matched the exact ordered expectation. The full
128-control campaign also passed in its exact order. This includes 104
ordinary cases in each client, two independently predicted FFI mutation
results, three source-proof failures and the correctly named stale-source
control. The two FFI unchanged baselines are retained inside their result
rows. They do not inflate the 214-result count. Full original 31-row capstone
acceptance remains the coordinator's decision.

| Bounded obligation | Final evidence and outcome |
| --- | --- |
| BVAL-INDEPENDENCE / BVAL-COVERAGE | Both clients matched literal microcase expectations and the original pinned PQ1/canonical observations, including all ordered reads and category counts. All seven actual canonical witnesses passed; all 17 witness semantic mutations were rejected after an unchanged production-check baseline. No expected result was obtained from new native output. |
| BVAL-EXACT-DISPATCH | Exact 109 unique registry IDs expanded to 214 unique expected results; actual order was identical. All 128 controls passed, including OS selector boundaries, complete same-ID substitutions, 90 minimal field deletions/changes and five manifest challenges. |
| BVAL-SOURCE | Runtime fuel substitution failed at `Runtime.lean:44:2`; empty loader input failed at `Entry.lean:23:64`; query argument reversal failed at `Entry.lean:36:2`. The exact source consumers below remain intact after restoration. |
| BVAL-TIME / restoration | All retained owned records had no timeout, output-limit event or terminated owned ID and completed within their deadlines. All source/Git restoration flags passed; a separate final read-only pass matched all 31 source, 19 generated-C and three artifact hashes. |

Final PowerShell parsing, Python AST parsing and the scoped `git diff --check`
passed. Both required repository trust/hygiene scans returned no matches;
`binary-commands/binary-final-static-checks.json` records the exact patterns
and checked files. The coordinator owns the final aggregate gate, so this
leaf did not repeat a full build or gate after its required campaign.

The separately owned contract leaf reports all nine controls and its one
omitted 44-case replay passed, with source/registry/shared-object restoration.
Its receipts are `contract-replay-20260912T132516703.json` and
`contract-replay-20260912T132610808.json`; full details and its repaired
runner identity are in `CONTRACT_VALIDATION.md`.

The evidence files are under `binary-commands/`:

| Receipt | SHA256 |
| --- | --- |
| `binary-controls-20260912T130603847.json` | `2BEAD2557D7CD8EA6056265636B45F05E0AF68F4E39F848441EF51F9226C06ED` |
| `binary-replay-20260912T131712734.json` | `C159656B68A1C1757EB439277D21C36C485D39A228A516BD47995E69C8CD60EA` |
| `binary-v3-final-128-20260912T130558739.json` | `ACB96574D5D43E5FAA61B1571591CBCA9AE41D29C0B27DEC3377F30C6E5CD9C6` |
| `binary-final-extraction.json` | `82DE67D23A1D730CE1C42B434EE5C9EFFAA87B543A8D7982FC6B251AAF461EC2` |

The owned outer campaign took 2,337.505 seconds within 7,200 seconds. The
omitted child took 1,665.969 seconds within 3,600 seconds, from
`2026-09-12T13:17:09.6789118Z` to `2026-09-12T13:44:55.6856038Z`.
Its actual fresh full toolchain verification took 25.497 seconds, with all
six probe receipts retained. Earlier 60.358/64.644-second calibration times
and the slow build diagnosis remain below; this warm result does not erase
them or change the live compiler/runtime assumptions.

## Exact source and FFI mutation consumers

The frozen source propositions challenged by the three Lean mutations are:

```lean
theorem nativeCore_source (image : StorageImage) (left right : LimbWord.Word)
    (fuel : Nat) (observeReads : Bool) :
    nativeCore image left right fuel observeReads =
      ((LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).final,
       (LimbMachine.run image.width image.memory image.code fuel
        (nativeInitialState image left right)).transitions.foldl
          (LimbMachine.recordTransition observeReads) {})

theorem nativeLoadEntry_source (bytes : ByteArray) :
    nativeLoadEntry bytes =
      match StorageImage.decodeSupported nativeLimits bytes with
      | some image => .ok image
      | none => .error "invalid or unsupported binary image"

theorem nativeQueryEntry_source (image : StorageImage) (left right : ByteArray)
    (fuel : Nat) (observeReads : Bool) (h : NativeQuerySupported image left right fuel) :
    nativeQueryEntry image left right fuel observeReads =
      .ok (nativeObservationText (nativeCore image left.data right.data fuel observeReads))
```

Thus the first mutation breaks `nativeCore -> runThin -> runThin_projection`
to the original run's final state and transition fold. The second breaks the
actual byte argument through `BinaryCursor.decodeSupported_eq` to the checked
storage decoder. The third breaks the ordered endpoint arguments through
`nativeEvaluate_source` to the actual `nativeCore` observation. Each mutation
has one uniquely matched designated diagnostic, and every diagnostic line is
retained; the fuel mutation also broke the separate no-reads theorem.

| Mutation | Actual designated diagnostic | Owned UTC interval | Seconds / bound |
| --- | --- | --- | --- |
| `source-core-fuel` | `Runtime.lean:44:2: error: type mismatch` | `13:44:18.6310384Z` to `13:44:32.3976722Z` | 13.721 / 180 |
| `source-loader-bytes` | `Entry.lean:23:64: error: unsolved goals` | `13:44:33.5784094Z` to `13:44:44.4862218Z` | 10.871 / 180 |
| `source-query-order` | `Entry.lean:36:2: error: type mismatch` | `13:44:45.4449831Z` to `13:44:54.1167081Z` | 8.644 / 180 |

All three exited 1 as required. Dates in the table are 2026-09-12 UTC. Runtime
was restored to SHA256
`23EF158FCC87169566CC443401BD6842197F9373E39CF5DF172165B765FEA847`,
Entry to `ADD666450D8CF6B724F1467CC2CD4182E8B5EEFC50AE1BF369AEFC5A2A4B7832`.
The independent stale-source operation rejected the exact diagnostic
`stale native source: RMQ/Core/WordRAM/Native/Runtime.lean` and restored the
same Runtime bytes. Every recorded scoped Git restoration flag is true.

The C-shim mutation compiled the actual pinned 19 generated-C files with
swapped copied endpoint arguments into an isolated DLL. Compilation exited 0
in 47.977 seconds within 300 seconds, from
`2026-09-12T13:43:14.7185758Z` to `2026-09-12T13:44:02.7539246Z`.
Both unchanged clients first produced exactly:

```text
halted 93536104789177786765035829293842113257979682750468
2
0 0 1 0 0 1

```

Both clients against the mutated DLL then disagreed with that normal
expectation and matched exactly `fault\n1\n0 0 1 0 0 0\n\n`, exit 0 and
empty stderr. This exercises the actual rebuilt shim and both consumers.
The mutated shim SHA256 was
`86CBFD29B95D832E30C740DC8FA385067381BAAFA6062942451D8589AF283B1E`,
the isolated DLL SHA256
`ADABB0288DF4BD9561072721F84BEC5B89FFBF8EDE96A244ABF464479132A969`.
The shim was restored to
`0D395279A803AB9FB796BB1176F5376F59CBF887E0414F09AF4D376A78F89780`;
all baseline artifacts and generated-C pins remained equal. No process was
suspended. The contract worker explicitly released its compiler window before
these calls, and this worker released it after final restoration.

The final baseline artifact hashes are:

| Artifact | SHA256 |
| --- | --- |
| `packed_rmq.dll` | `7605525E9E89540D43DFD307E84DE24F03062A9632A59062682600D20E0168C4` |
| `packed-rmq-native.exe` | `7A6FB03165C0DFCBD8F58D4A7E04D383019D1633CC9E28F052B57E2FA27814D7` |
| `packed-rmq-native-cpp.exe` | `74F0AE4696EBD35DF6C230D25859FA83458F62BDDD2AE8EE6CAE90E59956BEC2` |

## Proof digestion

The validation path now binds a complete nonempty registry to independent
bytes and expected observations, executes the same rebuilt native core through
both clients, and detects changes at the byte loader, original transition
fold, ordered query arguments and real C marshaling boundary. The mutation
controls show that these named checks are sensitive to the claimed behavior;
they are finite adversarial tests, alongside the separate source theorems.
Compiler correctness, Lean/runtime primitives, the C ABI and operating system
remain live assumptions. Tool inventories establish measured provenance, not
a compiler-correctness theorem. A skeptical reader should inspect how the
source equalities above compose with the public capstone's supported-input
conditions and the independently produced canonical witness chain. Full
public acceptance and the separate 42-field contract campaign are coordinated
outside this bounded leaf; the latter is documented in
`CONTRACT_VALIDATION.md`. The following sections preserve the original frozen
requirements and historical development checkpoints, including failures.

## Frozen original requirements before drafting

| ID | Verbatim frozen requirement | Evidence needed | Initial status |
| --- | --- | --- | --- |
| CHK-NATIVE-CONTROLS | Use the existing eight-case exported PQ1 experiment as a starting fixture only. Add cross-cell reads, both selects, fringes, interior/final rank, invalid ranges, corrupt/truncated/oversized metadata, width and address limits, shift/divisor failures and malformed binary length/padding controls. Check every ordered read/reply and category against an independent reference. Include source mutation controls that break the claimed code-correspondence check. | Literal independently specified microcases plus original pinned PQ1 observations; expanded canonical route witnesses coordinated with root/Lean validator; actual binary CLI/C++ results; source mutations at exact Runtime/Entry consumers. | OPEN |
| REPLAY-EXACT-REGISTRY | any new replay must have a nonempty exact versioned case registry and report executed/expected cases; silently losing a case is failure. | Immutable complete semantic case contract, independently pinned roster and all case fields; exact final execution inventory. | OPEN |
| REPLAY-SELECTOR-NONVACUITY | omitted, valid, empty, whitespace, malformed and unknown selectors have pinned behavior; focused runs cannot succeed by selecting nothing. | Actual OS subprocess selector boundaries, including explicit empty arguments; positive original operations and negative preserved-ID substitutions. | OPEN |
| REPLAY-SUBPROCESS-DEADLINE | run subprocesses with bounded ownership/timeout, preserve exits and stderr, restore mutated bytes in finally, and verify exact clean restoration. Use existing process ownership tooling. A condition the host cannot create is uncovered/inconclusive, not passed. | Existing owned process helper, absolute UTC intervals around each call, chosen deadlines and output limits, exact source/registry/manifest restoration; no unsupported host marked passed. | OPEN |

These original rows stay open until their complete required surfaces are
covered. The old eight cases do not by themselves establish both selects,
every fringe/rank branch or the final source-level native join.

## Frozen local implementation contract

Ownership is restricted to `scripts/packed_native_binary_replay.ps1`,
`scripts/packed_native_binary_controls.ps1`,
`scripts/packed_native_binary_cases.json`, `scripts/packed_native_cases.py`
and this report/evidence. Other workers own Runtime, Entry, C ABI, Rust/C++,
the efficient cursor and `scripts/packed_native_image.py`. They are not to be
overwritten or reverted. The old v3 text-route runner stays unchanged.

The new native artifacts are `.lake/native1/binary-build/packed_rmq.dll`,
`packed-rmq-native.exe` and `packed-rmq-native-cpp.exe`. Manifest schema is
`native1-binary-build-v1`; its exact complete source inventory is an explicit
pending root input. It must not be inferred from whichever entries remain in
an editable manifest.

Both CLI consumers support `load IMAGE` (stdout `loaded WORD_BYTES\n`) and
`query IMAGE LEFT_HEX RIGHT_HEX FUEL READS [REPEAT]`, with reads 0/1 and repeat
1..16 (default 1). A file is loaded once and may serve repeated queries. Each
success emits exactly `Runtime.nativeObservationText`; rejected input exits
1 with a specific stderr reason. Executed checked-machine faults are successful
query observations, distinct from parser/API rejection. The registry will pin
both stdout and stderr rather than assuming a channel.

| Local ID | Bounded obligation | Direct consumer | Initial status |
| --- | --- | --- | --- |
| BVAL-INDEPENDENCE | Expected results come from literal independent microcase specifications or the original PQ1 exports, never from new native output. The root-owned exporter only encodes bytes. | Python fixture producer and both CLI consumers | OPEN |
| BVAL-EXACT-DISPATCH | Pin every case's ID, operation, artifacts, arguments, expected exits/streams and source-failure surface; reject missing/changed/extra fields and same-ID downgrades. | Binary replay and its production boundary controls | OPEN |
| BVAL-SOURCE | Mutate Runtime.nativeCore fuel and Entry loading/query argument use; require failure at exact source consumers, restore source bytes and Git state. | nativeCore_source, nativeLoadEntry_source, nativeQueryEntry_source | OPEN |
| BVAL-TIME | Record absolute UTC start/completion around every owned subprocess, in addition to the existing duration/deadline/exit/stdout/stderr. Coordinate each Lean mutation slot. | Binary command and control receipts | OPEN |
| BVAL-COVERAGE | Include real 168/176-bit successful operations, explicit checked faults, missing data/fetch, malformed binary fields/padding/headers, invalid endpoints, corrupt metadata and repeat ownership. Name any canonical route witness still needed. | Full exact binary case registry | OPEN |

## Verification plan

Draft and inspect the exact current source APIs first. Pure fixture generation,
static parsing and independent byte-layout checks may run without a Lean/native
slot. No native build, Lean mutation or new binary registry execution starts
before root coordination and a stable complete build manifest. Once ready,
run bounded startup and one known selector before full replay. Use focused
checks to diagnose failures, then one final complete registry on unchanged
content. Preserve every failed/incomplete receipt. The root owns public prose,
policy, axiom inventories, integration and final full-capstone acceptance.

## Evidence append area

No binary-native case has run yet. This document froze the requirements
before the new harness or fixture producer was drafted.

### Draft case and process contract, before any native replay

The first draft contains 101 case IDs: 97 native cases, each dispatched to both
Rust and C++, three source correspondence mutations, and one separately named
source identity rejection. The 198 expanded dispatch results include literal
168/176-bit arithmetic, a 4096-bit supported endpoint, all six operation
categories, ordered repeated reads, all ten arithmetic operations, explicit
checked arithmetic faults, missing fetch/memory, 25 malformed binary images,
the 128 MiB + 1 host-file boundary, endpoint/fuel/repeat/reads boundaries, the
eight original PQ1 fixtures and quiet-query projection. These remain draft
expectations, not successful execution claims. In particular, unsafe raw
arithmetic is not silently equated with a checked machine fault.

`packed_native_cases.py` does not interpret the RMQ machine. Its microcase
expectations are literal arithmetic expressions and instruction/category
counts. It reads PQ1 expected observations only from the original pinned
exports. A separate offset-based binary reader checks the root-owned exporter's
serialized header and every numeric code/memory cell against the declared
fixture before passing it to the native loader. All 88 non-PQ1 native fixture
specifications materialized successfully during the draft inspection. This is
producer evidence only; malformed cases have not yet been rejected by the
delivered native loader.

The draft registry pins both stdout and stderr as exact strings. The shared
owned-process helper intentionally omits empty output lines, so direct use of
its line arrays would erase part of `nativeObservationText`, especially quiet
and repeated observations. The new producer's capture operation runs beneath
that existing owned process, captures native byte streams to two uniquely owned
files, enforces a separate deadline and combined byte bound, emits base64 bytes,
and deletes only those two files. The existing ownership job still contains the
Python process and its child. The caller rejects timeout/overflow/incomplete
results and strictly decodes UTF-8 before exact comparison. Both wrapper and
child have UTC start/completion timestamps. The independent Python-child
control preserved stdout bytes `[10,88,10,10]` and stderr `[69,10]` exactly:
`binary-commands/raw-byte-capture-control.json`, SHA256
`22F86D139B9A5BC99BB64075B0AC5951CD2417704E2381E47E2E018543865901`.
This is not a native result or a source correspondence proof.

The revised draft controls roster contains 93 IDs (initially 92), including real process
selector boundaries, preserved-ID source downgrades/substitutions, minimal
deletion/change of 37 top-level/case/nested-image field representatives,
manifest omissions, valid smoke and omitted full dispatch. The registry
producer's mutation helper locates one JSON value/property span, preserves the
unrelated prefix/suffix, and independently compares the resulting parsed
object against exactly the intended edit. This prevents a global reformat from
confounding a source-kind downgrade challenge. Complete donor cases also replace
both source mutations and source-pin cases with an ordinary valid PQ1 case,
and replace the source proof with a complete valid source-pin case, always
retaining the victim ID. All 74 field-span preparations passed without changing
the production registry. Full production controls await
the stable binary manifest and startup check.

The actual owned-child empty/whitespace argument check passed after correcting
its development test to emit bytes explicitly. The first test used Python
`print`, emitted CRLF on Windows, and failed its LF assumption; it already
preserved both arguments correctly. Both receipts remain at
`binary-commands/empty-argument-capture-control.json` (failed expectation) and
`binary-commands/empty-argument-byte-capture-control.json` (passed byte test).
Native expected streams were not changed. Replay parsing explicitly preserves
the child's UTC timestamp strings instead of letting PowerShell convert them
to local DateTime values. The replay requires the bundled PowerShell runtime's
`ConvertFrom-Json -DateKind String` support.

Production replay and controls now select the exact Python executable returned
by the workspace-dependency tool, rather than whichever Python appears first
on PATH. Each receipt records its actual full path, version, executable SHA256,
adjacent Python runtime-DLL hashes and bounded version-probe process. Earlier
producer development checks used `C:/Python314/python.exe`; they remain
development evidence, not a claim about final producer runtime identity.

Canonical route expansion is a separate checked witness leaf. Its requested
names follow actual query call sites: `canonical-select-left` and
`canonical-select-right` both use `packedSelectCloseLeaf`; left/right fringe
coverage must come from the window/fold subcall, not merely its rank seed;
`canonical-interior` uses `packedInteriorRangeMinRead`; final rank uses the
distinct `packedRankCloseLeaf(close+1)` call. The witness exporter will include
input integers, leftmost semantic answer, logical/physical ordinals and actual
transition index/pre-state/load address/reply. JSON content uses the existing
`.fixture` operational extension. No unclassified native JSON exception is
introduced. Those exports are not yet present or accepted.

### Discovered toolchain provenance gap and bounded repair

After the earlier route repair, source review found that its v1 toolchain
identity enumerated Lean bin/include/lib, Rust bin/target libraries and three
external executable files, but omitted external C++ STL/SDK headers and
libraries. The earlier 55/55 and 16/16 receipts remain exact historical
execution evidence. They do **not** establish the stronger claim that every
external C++ build input was pinned by that old inventory. No old receipt was
rewritten or rerun to hide this discovery.

Root explicitly extended this worker's ownership to
`scripts/packed_native_identity.ps1`. A bounded `clang -###` dry-run exposed the
effective dependency selection without compiling or linking: VS2022 clang
19.1.5 selects VS18 BuildTools MSVC 14.50.35717 and that toolset's `link.exe`,
while the configured Rust linker/import librarian are MSVC 14.44.35207. The
effective Windows SDK is 10.0.26100.0 and clang resource directory is version 19.
Deriving all include/library paths from the configured linker would therefore
still pin the wrong C++ inputs.

The repaired `native1-toolchain-v2` identity records the exact ordered include
and library search paths, actual roots and versions; rejects missing or
ambiguous compiler/MSVC/SDK selections; inventories eight required dependency
trees; hashes the fourth actual external executable (the selected C++ linker)
and adjacent DLLs in the selected compiler/linker/librarian directories; and
incorporates all of those bytes and paths into the digest. The eight trees are
the effective and configured MSVC include/x64-library pairs, SDK versioned
Include/ucrt-x64-library/um-x64-library, and the clang resource tree. Existing
Lean and Rust inventories remain. Retained manifest inventory fields must also
equal the newly reconstructed inventory; deleting an inventory row while
leaving its digest untouched is rejected.

The first discovery check rejected absent advertised ATL/MFC directories.
The host's clang defaults name `atlmfc/include` and `atlmfc/lib/x64` even when
that optional component is not installed. Root authorized an explicit
present/absent pin for exactly these two optional paths. Required STL/resource/
SDK roots still must exist. Installation of either optional directory changes
the digest, and present optional directories are fully inventoried. This avoids
inventing files, scanning unrelated machine trees, or treating an absent
optional search path as a consumed header. A later evidence-write wrapper
failed because its output directory had not been created; creation of that
directory fixed only the wrapper. Neither failure ran compilation or native
case dispatch.

The successful discovery receipt is
`binary-commands/cpp-effective-discovery.json`, SHA256
`DE098CE9A3F2CCF498D3677C3F00AB68C9D87730AAE35BB05E2E0A0851C3DE57`;
its owned dry-run duration was 3.983 seconds, exit 0. Static PowerShell parsing
and scoped whitespace checks passed. At root's freeze request, the helper's
source SHA256 is
`3853E9E2F71096B75598F8220461F0796A7C19166E0738BBDF395C849947CABF`.
No full repaired inventory has run yet. It invalidates v1 toolchain identities
and cache digests; the root will perform the actual inventory/build once the
source consumers are checked. The binary source roster remains the root's
exact 31 paths (19 Lean plus 12 native/build files), including this helper.

The explicit external assumptions remain compiler/runtime/FFI correctness,
allocation availability, and OS behavior, including system DLL behavior. The
inventory is byte provenance for the selected toolchain files, not a proof that
compilers, the OS, or foreign callers satisfy their contracts. Root owns the
shared WDD entry; the rationale above is supplied for that entry. Root was also
notified that exact LF attributes are required for the registry and both
producer sources so fresh Windows checkouts preserve their embedded hashes.

### Additional frozen wrapper and public-contract challenges

Root approved the actual C wrapper argument-order challenge required by
`REQ-NATIVE-CODE` in the original acceptance matrix. The binary draft now has
102 cases (200 expanded results before the seven canonical witnesses) and 102
controls. The new `source-ffi-order` case swaps the actual shim's left/right
`copy_bytes` arguments, compiles an isolated DLL, copies both delivered CLI
executables byte-for-byte beside that DLL, and applies the literal asymmetric
168-bit subtraction fixture. The ordinary prediction is a halted positive
difference with one arithmetic and one halt step. The swapped prediction is a
checked underflow fault with one arithmetic step and no receipts. Both
consumers must disagree with the original prediction and agree exactly with
the independently predicted fault. A stale-source rejection cannot pass this
case. No C/Lean mutation has run yet.

The root added an exact generated-C inventory to the still pre-build v1 binary
manifest: 19 repository-relative emitted `.c` paths and their byte hashes.
The replay verifies that complete roster independently from the manifest's
contents, and verifies all those hashes immediately before and after the
isolated rebuild. It does not use mutable module-cache metadata as the source
of these identities. The actual shim is restored byte-for-byte in `finally`;
source diff, all original artifacts and original generated C must remain
unchanged. Every command, including failed preparations or compiler calls, is
retained separately from successful case results so a late assertion cannot
erase its command evidence.

Root also assigned exactly two additional files for the public contract
counterfactuals: `scripts/packed_native_contract_replay.ps1` and
`scripts/packed_native_contract_cases.json`. The frozen obligation is:
“Need frozen42 fields in Capstone with markers, exact Contract consumer
checkN01..42, independent source-byte pin, each field weakenedtoTrue with
initializerTrue (producer mustcompile, exactconsumer mustfail),
publictheoremtypecollapse, expected-accept unchanged control,
restorationrawsource+oleans+diff.” The original spelling is retained here;
the implementation uses ordinary Lean `True` and `True.intro`.

| Local ID | Frozen obligation and actual consumer | Status |
| --- | --- | --- |
| BVAL-CONTRACT42 | Each `field-n01` through `field-n42` replaces exactly its complete proposition with `True` and its initializer with `True.intro`. The producer must compile. The independently frozen `checkN01` through `checkN42` consumer must fail at the exact projection line with a type mismatch. | STATIC DRAFT; not executed |
| BVAL-CONTRACT-PUBLIC | Replace `nativeExecutionCapstone_holds : NativeExecutionCapstone` and its entire producer body with `nativeExecutionCapstone_holds : True := True.intro`. The producer must compile and `publicContract : NativeExecutionCapstone` must fail. | STATIC DRAFT; not executed |
| BVAL-CONTRACT-RESTORE | Restore actual producer bytes and source diffs; consume a fresh per-case overlay `.olean`; verify the shared Capstone/Contract `.olean` hashes never change. | STATIC DRAFT; not executed |

The exact 44-case contract roster contains one unchanged expected-accept case,
42 separately named field mutations and one public theorem type collapse. Its
nine controls exercise actual subprocess omitted/valid/empty/whitespace/
malformed/unknown boundaries and three registry challenges. A complete valid
baseline donor replaces a field mutation while retaining its ID; this changes
only that case's object span. A separate exact consumer-line property mutation
also preserves unrelated text. Neither challenge can succeed through
unrelated registry reformatting alone.

Root froze these independently checked source bytes after its final proof
checks: Capstone SHA256
`E2B2FB55223A271B3383AACB70361D85126ABEB3C252ACB0E314467729C6FA0D`
(reported check 4.970 seconds) and Contract SHA256
`A8DB1EAAC6445F2F8490A6C344A3F573FD169D3FD7B82E6637C4947159E306AE`
(reported check 7.309 seconds). This worker independently matched both hashes,
confirmed all 42 exact declaration/initializer/consumer anchors, inspected each
source transformation, and parsed the scripts without running Lean. Contract
registry SHA256 is
`6E0C8E5A73F7DE47D14F7298435E7F72F2AC82A5881AEBF3EFFE0388CBF48E2C`.
The registry retains each entire original proposition, initializer and
independent consumer block, not merely theorem names.

All source mutation executions remain behind root's shared Lean-slot handoff.
The final binary registry will be frozen only after the seven canonical
witness exports are present. Before that, root authorized a direct bounded
artifact smoke check using the independently inspected 146-byte image
`query-smoke.bin`, SHA256
`C27D76DC6F6B7033CF596E1CBEE1B0B38B88007EBFF68D996E38A67563B5CDAC`.
Its exact 24-byte expected observation is
`halted 8\n2\n0 1 0 0 0 1\n\n`, SHA256
`DF71E7B0B3B05342D8E34D7F0EC1FE70F5B14867EE1FCF92CAC2D948AA090A7F`.
That upcoming development check cannot certify an unexecuted full registry.

### First delivered binary startup and final witness-control preparation

Root subsequently completed the binary build and both bounded raw-byte startup
checks. Its retained `startup-packed-rmq-native.exe.json` and
`startup-packed-rmq-native-cpp.exe.json` record exit 0, empty stderr and exactly
the 24 expected bytes above, in 0.266 and 0.453 seconds respectively. These are
development smokes, not full replay acceptance. This worker's separate
`binary-static-manifest.json` records a read-only comparison of all 31 source,
19 emitted-C and three artifact hashes against the exact independent roster.
The build manifest SHA256 is
`8ACF20E470E6247E3E415FE283F909C7BDE2F968518F76F0CDA0ED7F988954FD`;
the actual v2 toolchain digest is
`8DF566C7330ED567CDBDE84504EC261D1FB26EA713E4BF6034ECA7B0A20751C7`.
This comparison did not repeat the expensive toolchain inventory.

The FFI mutation now first runs the exact asymmetric fixture through each
unchanged consumer and requires its independently predicted normal result.
Only then does it replace the actual shim argument order and compile the
isolated DLL. Each final mutation result retains the matching baseline
observation, so a broken baseline cannot count as a detected mutation. This
strengthening adds two native invocations without changing the case roster.

The canonical program packaging decision is explicit: retain the existing
committed `program.txt.gz`, the seven committed `.fixture` witnesses and a
baseline export receipt that records the actual `canonical-program.txt` hash
and its equality with the decompressed gzip. The temporary plaintext itself
is not a required replay input. Every replay still hashes the actual
decompressed program before parsing any instructions, and pins each witness
file and both checked exporter source files. A second large plaintext copy or
a fresh Lean export per focused selector would add no different replay bytes
or independent expectations. The witness worker owns the baseline export
receipt; those actual seven bytes remain pending at this preparation point.

The intended final binary roster is 109 cases, expanded to 214 consumer/source
results. The controls draft now freezes 127 names: 14 selector/structural
controls, 90 deletion/change controls for 45 complete semantic-field
representatives, 17 direct witness semantic challenges, four manifest
challenges and two production positive selectors. The witness challenges
first run the unchanged fixture through the same production checks and emit
a required success marker. They then serialize one changed semantic value
to an owned scratch fixture and require the exact failing diagnostic. Cases
cover stage, physical ordinal, transition index, source PC/load operands,
prestate PC/address, ordered receipt address/reply, loaded memory, span,
logical reply, false crossing, empty/missing physical cells, literal RMQ
oracle and program identity. They do not merely trigger a fixture hash
mismatch. The original fixture remains unchanged and its final hash is
checked. These controls are drafted, not yet executed.

The Python checker verifies the numeric occurrence claims it can derive from
the pinned program, memory, ordered expected receipts and span geometry. It
does not independently execute the original query to rediscover the full
prestate or the logical ordinal within its semantic stage. Those composition
claims consume the checked Witnesses/WitnessExport source chain and the
baseline export's actual checks. No duplicate Python RMQ evaluator is added.

The witness export subsequently passed in 403.369 seconds and copied all seven
fixtures to `native/packed-rmq/fixtures`. Its durable command and byte-equality
receipts are `commands/witness-export-01.json` and
`commands/witness-export-artifacts.json`. This worker's
`binary-commands/witness-independent-inspection.json` records successful
unchanged checks of all seven numeric witnesses. The six source-stage cases
use width 176 and input length 12, with independent answer packet 6. The actual
two-cell occurrence uses width 184 and input length 24, with packet 1; this
extra width is retained exactly rather than relabeled as a 176-bit case.

Before the first production selector, the complete 109-case registry was
frozen at SHA256
`2D38A1002C1E8A72DF5E164144EC4E8F5410511F2C585831AEFBBC0D1BD4C637`.
It pins producer SHA256
`C6AF8167DCE972FF220FA5D61B1D528109737FA9BC9D0A7AB625AB06B0391A4C`.
The initial frozen replay and 127-control runner hashes are
`671B38F65B49B9C30ADE9334B597EBD62C832DA6EE2CCB171607C289C6CDA363`
and `351E49ABC7103CC67CB2C29D22F545A9D96D243ED2205406223AD8E64849FC13`.
All 90 minimal field mutation preparations passed with only the intended
semantic change and unchanged production registry; see
`binary-commands/final-field-span-preparation.json`. This preparation does not
claim the still pending actual production rejection verdicts.

### Measured cross-shell inventory-order failure

The first frozen production `query-smoke` selector exited 1 after 55.852
seconds, before native dispatch, at `Assert-NativeToolchainIdentity`'s digest
comparison. It did not time out and performed no source mutation. The failed
outer receipt is `binary-commands/binary-first-selector-v1.json`, with the
inner `binary-replay-20260912T114513436.json`. The root's earlier direct native
startup checks remain successful evidence for their stated input; they did
not run this complete production identity assertion.

A single focused fresh inventory was retained as
`toolchain-mismatch-actual-v2.json`, with `toolchain-mismatch-diagnosis-v2.json`.
The independent `toolchain-order-delta.json` comparison proves that all full
path-to-row maps are identical: 4,856 Lean files, 48 Rust files, 6,545 C++/SDK
files, 145 adjacent tool DLLs and four external executables. Every byte hash,
file size, actual version string, dependency root, ordered include/library
search path and optional-directory state agrees. Only array order differs:
11 Lean, 19 Rust, 366 C++ and 23 DLL indices moved. The build's Windows
PowerShell 5 culture sorting and the runner's PowerShell 7 sorting place
punctuation differently, for example `libleanshared.dll` versus
`libleanshared_1.dll`. The v2 digest therefore changes from `8DF566C7...` to
`B37CC3DB...` despite identical compiler dependencies. Production correctly
failed closed; this is a harness canonicalization defect, not evidence that
the compiler bytes changed. Repair requires deterministic ordinal ordering
and a new explicit identity version, followed by a rebuilt pinned manifest.
The assertion must retain strict digest and complete inventory equality.

Before authoring the dedicated v3 replay, its bounded acceptance IDs are
frozen here: IV3-ORDER requires the actual production ordinal helper to produce
identical canonical identities from both captured equal maps under Windows
PowerShell 5 and bundled PowerShell 7; IV3-RETAIN requires unchanged retained
identity acceptance and exact rejections for changed command file/arguments/
version text, dependency key shape/root/search order, inventory bytes, sort
policy, top-level keys, command roster and digest; IV3-RESTORE requires both
captured input files and the production helper to remain byte-identical after
the replay. IV3-SELECTOR requires actual omitted/valid/empty/whitespace/
malformed/unknown child-process controls with exact executed inventories.
The runner may canonicalize the previously captured maps to test the new
representation, but this is not a substitute for the subsequent actual v3
build and production startup inventory. The old 10-case identity runner and
its historical evidence remain intact.

The repaired production helper is frozen at SHA256
`A21F67E2EDF49C8E218C657E73967E920EFB85FF025476E01BD04A83CA50B17A`.
Identity schema is now `native1-toolchain-v3`, with explicit sort policy
`ordinal-case-sensitive-utf16`. Unordered path sets and property names use
`StringComparer.Ordinal`; semantically ordered compiler include/library
search paths retain their original order. Normalized compiler roots and
stable command file/argument/version text now participate in the digest.
The production retained-identity predicate also compares each recorded
command's stable fields and the exact C++ dependency key shape. Timing/PID
data remain historical subprocess receipt metadata. The source-review gap in
retained command metadata is distinct from the measured order-only failure.

The dedicated `scripts/packed_native_identity_v3_controls.ps1` runner is frozen
at SHA256 `D8C9C5209D2E4FD738D9F89208A3AEDAB5FC35916A9F8220CCFD94E94422BBD1`.
Its inline exact semantic registry SHA256 is
`4CB180BB0380215D14AC80058652120AA877488BDF4A231C39BF6017CD99DA14`.
All 20 predicate controls and all six actual selector controls passed in
214.817 seconds under a 600-second owned deadline, with no timeout, output
limit, surviving owned process or stderr. See
`binary-commands/identity-v3-final-wrapper.json`, selector receipt
`identity-v3-controls-20260912T120438830.json` and full 20-case receipt
`identity-v3-controls-20260912T120637882.json`. The actual Windows PowerShell
5.1.26100.9444 and bundled PowerShell 7.6.5 children independently produced
the same canonical digest:
`2E1772C727BBEB16A0B65CFEA6902C74E8184A49CF483D65DF482A8177D84402`;
their receipts end in `120706093` and `120722287`. Both captured files and
the production helper remained byte-identical. The initial ordinal
development receipt is retained; the final control additionally uses one
valid supplementary Unicode character to distinguish UTF-16 ordinal order
from scalar-value order. The registry still runs every required case.

A separate source review found that the binary runner could read a manifest
Lean root independently of the root whose toolchain had been verified. The
runner now requires their normalized equality before dispatch. A named actual
child-process manifest-root mismatch control raises the final binary control
count to 128; its execution awaits the rebuilt manifest. The binary case
registry remains 109 cases/214 expanded results with the same frozen bytes.
Root owns the single subsequent rebuild and WDD-008 integration. Fresh v3
tool discovery and the binary/full contract campaigns are still pending;
the captured-map controls do not substitute for them.

The coordinator authorized one further runner-only process change while the
v3 build was pending. `owned_process_tree.ps1` initializes its C# job wrapper
when dot-sourced. The binary runner had done so before any malformed registry
or selector guard. It now first checks the exact registry, selector, producer
pins and build shape/content, then loads the already source-verified identity
helper and checks its pure shape, and only then initializes process ownership.
Every actual subprocess still uses the original owned helper and full identity
verification precedes dispatch. Frozen computational/build sources were not
changed by this reordering.

The real empty, whitespace, malformed and unknown selector rejections and the
same-ID source-kind downgrade all passed after this change, with no native or
Lean execution and exact registry restoration. The receipt is
`binary-commands/binary-early-guards-after-v3.json`; runner SHA256 is
`F4FDB47B674BCE93B4D353F071B04AE7F83CE347DEE8284DB0773D3416B22C46`.
Measured child times were 17.394, 20.026, 21.044, 23.886 and 16.336 seconds.
This sample does not demonstrate a reliable wall-clock speedup; the report
does not attribute all observed startup time to the deferred initialization.
At the measured mean of 19.737 seconds, the final 109 rejection children alone
would take about 36 minutes. The total 128-control campaign also includes 90
mutation preparations, 17 witness checks, two positive selectors and the
omitted 109-case binary replay. The proposed 7,200-second outer and
2,400-second omitted-child deadlines provide margin for current startup cost;
the coordinator authorized a 600-second smoke selector and one focused large
PQ1 image selector to calibrate the remaining native/decode cost first.

The replay receipt now retains the six fresh owned tool-version/dependency
probe records (including UTC start/end), rather than discarding them with the
large freshly checked identity object. This is receipt metadata only; the
full identity is still checked before dispatch. The runner after this change
parses cleanly and has SHA256
`36774810EB0BA670594D11D11DBD22924032CE8F67554027B5ED5F02CB80DCF6`.

The subsequent v3 rebuild exposed a separate measured IO problem before any
Lean compilation. The coordinator sampled roughly 1.64 GB across 401,759
reads (about 4 KB/read) while the owned build process had used only 44 CPU
seconds over approximately 14 minutes. That observation invalidates the
provisional selector deadline forecast until the cause is resolved. A bounded
host-only scratch benchmark read the independently pinned 149,042,606-byte
`lib/lean/libLean.a` in Windows PowerShell 5.1.26100.9444 using SHA256 with a
1 MiB sequential FileStream buffer and then the existing `Get-FileHash`.
Both exactly matched the retained hash
`9A8BCDE682EAC2413F5BF2B211AA04631581A7404FD39857CF589BA0AA0C080F`.
Times were 1.011 and 1.510 seconds, respectively; the owned wrapper completed
in 7.980 seconds with no timeout, output limit or terminated process.
`binary-commands/hash-buffer-benchmark.json` retains the script and exact
measurements; `hash-buffer-benchmark-owned.json` is the owned receipt.
The second read may benefit from warm cache. This confirms hash equivalence
on that file and fast host reads, but does not reproduce or explain the much
slower build process. The production identity helper remains unchanged at
this diagnostic checkpoint; no full inventory or native replay was claimed.

The coordinator's stop guard then observed a live compiler child and rejected
the stop request: no process was stopped. The build had emitted the expected
v3 digest and reached 9/19 module passes. The coordinator therefore kept the
production helper frozen and did not adopt the buffer change. A second
bounded read-only sample sent 100 exact pinned Lean leaf paths (2,136,064
bytes total) through the unchanged production `Get-NativeFileInventory` in
PS5 and PS7. Both matched every original path, size and SHA256 row. The
enumeration/hash work took 1.419 seconds in PS5 and 0.861 seconds in PS7;
owned process durations were 8.437 and 12.410 seconds, respectively. Both
120-second deadlines completed without timeout, output limit or terminated
process. Exact sample pins, script and full actual rows are retained in
`binary-commands/hash-small-file-benchmark.json`, with process evidence in
`hash-small-file-owned.json`. These warm sequential samples do not establish
the cause of the earlier delay or predict the cost of the full inventory.

The coordinator's complete v3 build passed and its immutable manifest is
`BINARY_V3_BUILD_MANIFEST.json`, SHA256
`A4C20BCAA5E35402293DB522CE8736A81BD84FBC67FC2648693475504E5E1069`.
The bounded expected-accept selector then passed both Rust and C++ clients
with the exact independent 24-byte observation, exit 0 and empty stderr.
The full identity check took 60.358 seconds; the owned selector took 86.639
seconds within its 600-second deadline. Exact evidence is
`binary-commands/binary-replay-20260912T125636041.json` and
`binary-v3-calibration-query-smoke-20260912T125624257.json`. Six fresh
toolchain probe records, including their UTC boundaries, were retained.

The one authorized large calibration, `pq1-n9-full`, also passed both clients
with the exact independent 4,523-byte observation, exit 0 and empty stderr.
The input was the inspected 70,854,686-byte image. Identity verification took
64.644 seconds, preparation 27.596 seconds, and the Rust/C++ owned calls
29.969/27.851 seconds (native child time 27.657/24.532 seconds). The complete
selector took 164.828 seconds within 600 seconds. See
`binary-commands/binary-replay-20260912T125916442.json` and
`binary-v3-calibration-pq1-n9-full-20260912T125906228.json`.

These measurements predict about 2,300 seconds for the omitted 109-case
replay: sixteen large cases near 85 seconds each, 88 small native cases near
nine seconds each, and the identity/FFI/source controls. The original
2,400-second omitted-child deadline would leave insufficient cold margin.
Before the first full campaign, the coordinator authorized increasing only
that operational deadline to 3,600 seconds, with a 7,200-second owned outer
deadline. All individual native/preparation bounds, 109 registry cases, 128
controls and exact expected verdicts remain unchanged. Final controls SHA256
is `EDEE71ED973FFF4BC860E1258C6B7FED315FEE43218179C800407998AAD58104`;
the replay runner remains `36774810...80DCF6`. Syntax and scoped whitespace
checks passed. The full campaign has not yet been claimed by this paragraph.

The coordinator transferred contract replay execution and subsequent runner
repair to the validator worker while the binary controls were running. Its
first expected-accept baseline failed before any consumer check: Lean resolved
the partial `RMQ` overlay as an entire import root, hiding `Execution.olean`.
The preserved receipt is
`binary-commands/contract-replay-20260912T131025801.json`; producer exit 1
took 2.137 seconds. This was a harness import-tree failure, not a rejected
field weakening. The coordinator approved a physically copied local import
tree with exact fresh-producer hash binding before and after the untouched
consumer. The repaired baseline passed in 31.464 seconds (copy 12.330,
producer 5.127, consumer 4.712); see
`contract-replay-20260912T132003337.json`. The repaired runner SHA256 is
`AE8BC171667857E693D58E74626D425AB5C7F8AB43BDA4D6996A6FF92C8C3687`;
the 44-case/9-control registry is unchanged. Further contract execution and
restoration evidence belong to that worker's `CONTRACT_VALIDATION.md`.
The original runner hash above remains the historical draft identity.
