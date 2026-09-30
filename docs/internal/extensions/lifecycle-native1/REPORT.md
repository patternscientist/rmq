Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# LIFE-NATIVE-1 worker report

The native consuming owner, all required local execution campaigns and the
default build are complete. The external delivery receipt binds final source,
report and ledger bytes to the clean candidate commit and successful strict
report-sensitive certification. This report does not record coordinator
acceptance, an aggregate gate, a blind audit, integration or publication.

Worker: LIFE-NATIVE-1. Task title: `(LIFE-NATIVE-1) Consume the proved lifecycle in a native owner`.
Worktree: `C:/Users/poin/.codex/worktrees/44d6/RMQ`.
Branch: `codex/life-native-1-consuming-owner`.
Base/source parents: `3dbdebedcc6ba6b2a864df0d46dcc09ccaaa7536`, formal
`7d247703a7009aa0f5faa1a9a67abf5f2ce526b6`, native
`8a74ad3af84feaf0ccea7185813ce8b55c50d96a`.
Governance: `7b227c49ef2ec044b702126cc41c9add847eed01`.
The final candidate commit and this report's final byte hash belong in the
external delivery receipt, avoiding recursive self-identification.
The complete changed/new path roster is in [CHANGED_FILES.md](CHANGED_FILES.md).
The exact command-to-row ledger is [COMMANDS.md](COMMANDS.md).
Final committed identity and report bytes are recorded at
`.lake/lifecycle-native1/delivery/DELIVERY.json` after certification.

## Result and composition

The added C ABI builds the input, retires construction storage, runs the caller's
real first query, replaces all four backing arrays with exact-capacity arrays,
and publishes one halted reusable owner. Later calls consume that owner through
the inherited charged request protocol and query, then publish a replacement.
The safe Rust facade encodes unique mutation, thread restrictions and resource
lifetimes. The C and C++ clients use the same DLL; C++ contains no RMQ algorithm.

The computational chain is
`nativeInitial = Executable.initialOwner -> nativeRunFirst -> runThin -> executeArray -> Owner.status`.
For continuation it is
`nativeQuery -> query -> requestProtocolThin -> runThin -> Owner.status`.
`runThin_eq_runOwner` holds for every program, fuel and owner, including failed,
stopped and missing-fetch states. The boundary and observed thin loops have the
corresponding unconditional equalities. This removes transient execution records
without replacing any primitive semantics. `COMPILED_ROUTE_EVIDENCE.md` follows
the emitted functions, actual FFI call sites and initializer closure.

The export theorem has precisely the source assumptions
`InputDomain model xs`, `left < 2^wordWidth xs.length`, and
`right < 2^wordWidth xs.length`. It derives an `ExportContract model xs left right`
at `buildFirst model xs left right = Ownership.owner model xs left right`.
Its output has the guarded correct halted packet, canonical produced memory,
empty key banks, an 8273-entry numeric bank and
`Ownership.capacity model output * wordWidth xs.length <= 2*xs.length + retainedRho xs.length`.
No outgoing answer or memory equality is an input assumption.

Continuation requires the incoming `Ownership.Ready xs owner`, its halted
status, and represented endpoints. It derives
`query model left right owner = Executable.queryOwner model left right owner`,
preserved memory, READY, the guarded correct packet and
`Reusable.queryRun.steps <= 160257`. The request prefix contains exactly two
request-admission and two control-entry events; the uninterrupted first request
does not prepend that external prefix. The detailed independent expected types,
all mandatory projections, domain guards and composition chains are quoted in
`PROOF_EVIDENCE.md` and checked in `RMQ/Validation/LifecycleNativeContract.lean`.

Native admission proves count/decoded-input identity, input-domain membership and
canonical endpoint representation before transfer. Word input retains its
`InputFits` obligation; comparison input is arbitrary finite `List Int` at the
formal layer. The host ceiling is 4096 input values, 1..4096 magnitude bytes each,
and 16777216 magnitude bytes total. Sign/magnitude and answer packets use arbitrary
precision values; no u64/u128 truncation supplies the semantic domain. Native
READY count and memory length come from produced metadata, not caller duplicates.

## Ownership and error boundary

| Event | Owner disposition | Answer/observation and cleanup |
| --- | --- | --- |
| Malformed or unrepresentable later request | The same old owner remains valid | Both outputs empty; parsing temporaries released |
| Represented invalid interval | Formal execution succeeds and publishes canonical reusable state | Ordinary packet 0, with separately owned optional diagnostics |
| Successful first or later request | One owner is published after exact-capacity replacement | Independent answer and optional observation handles |
| Failure after irrevocable take | Owner slot becomes empty/poisoned | All initialized temporary resources released; explicit error |
| Controlled failure before external publication | No replacement escapes | Even strictly validated arrays and allocated handles are released |
| Model fault / exhausted fuel | No reusable builder state is published | Distinct statuses 7/8, empty outputs |
| Ordinary Lean allocation failure | Runtime may terminate | No recoverable-allocation guarantee is claimed |

Status 0 is success; 1 format, 2 domain, 3 limit, 4 wrong thread, 5 initialization,
6 state, 7 model fault, 8 fuel exhaustion, 9 injected/native handle allocation, and
10 controlled failure are distinct. The full ABI contract is in
`native/packed-rmq/include/packed_rmq_lifecycle.h`.

C callers must obey valid-buffer, exclusive-handle and initializing-thread
preconditions. Rust exposes no safe raw-owner escape or clone, requires
`&mut Owner` for a query, and ties all native resources to a thread-bound runtime.
Borrowed answer bytes cannot outlive their independently owned answer object;
that object may outlive the operational owner. Runtime acquisition uses the
existing crate-level claim guard, including sticky initialization failure.
Finite native controls do not quantify over arbitrary foreign misuse.

At every successful publication the implementation copies all four arrays,
including the complete canonical memory and zero-length key banks, and releases
old backing roots. Later native replacement is additional work beyond the
modeled query-step theorem. Native pointer equality is not a consequence of the
logical `Repacked` theorem; that theorem transports values, READY and capacity.

## Current execution evidence

All relative receipt paths in this report are under `.lake/lifecycle-native1/`
and end in `RESULT.json`. Raw outputs stay there; committed sources contain the
exact replay cases, expected verdicts and compact evidence indexes.

| Consumer | Receipt | Actual outcome |
| --- | --- | --- |
| Four focused Lean roots and independent consumer | `runs/build-20260927T062313663` | PASS; 5979 pins, cached Lean stage 0.890 s, overall 44.741 s |
| 365-module production/testing DLL closure | `runs/build-20260927T063830290` | PASS; 7091 pins, five actual native stages, ABI and PE closure |
| C/Rust/C++ binaries | `runs/build-20260927T064222779` | PASS; eight compile/link stages, 7143 pins |
| Fresh startup | `replay/20260927T064556967-9557393a` | PASS; 5.434 s actual native process |
| Exact first fixture selector | `replay/20260927T064716438-5960f47b` | LN1-W-TIES only, both modes PASS |
| Complete 13 fixtures | `replay/20260927T064849543-b1d28b93` | 26 fresh processes, 142 query results PASS |
| Corrected-recipe native-control discovery | `native-controls/20260927T072450429-92e7bea9` | NC-NONE-BUILD measurement PASS; complete recipe independently reconstructed |
| Historical 48 native-control discovery | `native-controls/20260927T051058239-1758cc65` | Actual measurements reviewed; 4 accepts, 1 nondistinguishing, 43 rejects |
| Historical 48 native-control replay | `native-controls/20260927T052620110-f51e89eb` | All 48 projections passed; superseded for current recipe binding by the fresh Replay below |
| Historical Rust misuse discovery | `rust-misuse/20260927T050848252` | 15 intended rejects and 2 accepts |
| Historical Rust diagnostic replay | `rust-misuse/20260927T051519397` | All 17 passed; current-source refresh is recorded below |
| Current Rust misuse discovery | `rust-misuse/20260927T072740867` | All 17 full diagnostics exactly equal the reviewed historical cases; 111 pins and cleanup PASS |
| Complete corrected-recipe native replay | `native-controls/20260927T073240346-3c38ea74` | All 48 unchanged expectations PASS; 7638 pins and cleanup |
| Complete current Rust diagnostic replay | `rust-misuse/20260927T073749082` | All 15 intended rejects and 2 accepts reproduce exact diagnostics; 112 pins and cleanup |
| Complete current C++/Rust clients | `clients/20260927T065517097-e55bf689` | All 10 PASS; 7292 pins and cleanup |
| Current ABI boundary checks | `replay/20260927T065401229-f97e3be7` | 23 checks PASS; separate from fixture-case count |
| Required untargeted default `lake build` | `default-build/20260927T074010540` | PASS; 374-job build, actual 207.869 s, 6056 source/tool/raw pins and cleanup |

Production DLL SHA256:
`03c17dd0fbacff8f72e707f40ba737096daf096059ace99ec7a0c9fd69c1772d`.
Testing DLL SHA256:
`160f2b9e0beb5d25de80d3852608d5f5bb8309a860c3faee6da9c90c92736218`.
The exact compiler/runtime/import/source/artifact pins and complete commands are
in those build receipts; runtime staging verifies adjacent copies and PE closure.
The current client-build receipt hash is
`6dd359050473a2604ab6370ef65813ba90ef0f3b4acd3ffaa776a08118caf699`.
The default-build receipt hash is
`3b4a40505c289403d28c71520a57c112a1a573ea7196ed13e31c1af8bf5a1eaf`.
Root rechecked its sixteen raw capture pins, exact Lean version bytes and
ordinary zero build exit with empty stderr. Its 1183 source pins and 4856
tool pins cover the declared baseline plus the added lifecycle sources.

The fixture registry uses independent reference expectations and covers both
models, empty/singleton/two-element inputs, leftmost ties, negative and wider
than 128-bit comparison values, sizes 24/83, invalid represented ranges, and valid
queries after invalid ones. All observed/unobserved pairs agree on answers and
canonical memory. Every published array has capacity equal to initialized size.
Actual later-step maximum is 28613 on these fixtures, below the 160257 model bound;
it is a finite observation, not a new tight theorem.

`ROUTE_COVERAGE_EVIDENCE.md` distinguishes close-block branch decisions from
input indices. It verifies actual interior payload addresses and every 10480
later read/reply occurrence against canonical memory; 3288 are payload-address
occurrences. Segment 20 marker counts alone are insufficient to establish a
successful payload read. Crossing-cell occurrences are established at the shared
reader; no unproved segment-specific crossing classification is asserted.

`NATIVE_CONTROL_EVIDENCE.md` records all 48 actual helper challenges and their
same-predicate oracles. In particular, skipped construction repacking rejects
excess capacity, while skipped later repacking is honestly nondistinguishing on
already exact arrays. Wrong copied values/offsets change actual memory bank 1 at
the selected indices. Shared immutable boxed scalar roots are accepted; retained
operational owner/input/arena/key/history roots are rejected. Partial-copy cuts
0,1,8272,8273,8274 exercise both phases and release every initialized entry.
Current-operation counters are not a global census of older preserved handles.

The fresh one-case control discovery exposed a provenance defect before the
new full replay: `Sort-Object path -Unique` treated the ordered-dictionary pin
keys as absent and reduced the fingerprint recipe to its first row. Both old and
fresh fingerprints were therefore the hash of the unchanged runner pin alone.
The individual source/tool/artifact checks before execution and in `finally`
still ran; the cross-run recipe guard was insufficient. The repaired runner
binds every distinct pin with exact ordinal path keys and rejects conflicting
duplicate identities. Eleven recipe controls and eighteen actual selector
callers passed. Root independently reconstructed all 7148 input occurrences,
rehashed their 6013 distinct files and checked the 1135 consistent duplicates.
The complete 1034385-byte recipe has SHA-256
`494eadb41c09ba18e4d27d84eec77d12a0c220abf04b817b6f1b42a839a83791`.
The corrected focused discovery and its complete healthy projection passed.
Only the expectation manifest's input binding and provenance note changed;
all 48 exact case objects and their historical discovery pins remain intact.
Current full replay reproduces all those cases under the corrected recipe.
Historical measurements are fixed oracle data, not evidence that the old
fingerprint covered the complete producing inputs. The repair, its controls and
the refreshed producers are indexed in `NATIVE_REFRESH_EVIDENCE.md`.

The current native48 replay also passed an independent read-only reconstruction
of every full projection, command, ordinary exit, raw stream and failure-class
predicate. All 7638 final pin entries were rehashed. That review is
`native-control-independent-review/20260927T073240346-3c38ea74/REVIEW.json`, SHA-256
`39c6f5155edcf143b5b4a85884c5f6a96c39d5efa27bee60846ee52802de4f2f`.

Current Rust Discovery independently reproduced every byte of all 17 reviewed
compiler cases. Root rehashed all 111 source/tool/fixture pins and 144 raw capture
pins, then rebound the unchanged cases to the current recipe. Its 93 input rows
all remain present: the runtime's dictionary-property sort permutes them without
deduplication. No insertion-order or path-sorted identity is claimed. The exact
replay uses `RUST_DIAGNOSTICS.json` SHA-256
`985835ed2ac39483dae006c327f656a0fd92546d60c91ef97122f67b6d795141`.
It passes the complete fifteen-reject/two-accept roster with 112 integrity pins
and successful cleanup. No diagnostic normalization or expected-case change was
needed for the producing-source refresh.

Caller-level control receipts are indexed in `NATIVE_SELECTOR_CONTROL_EVIDENCE`,
`NATIVE_CLIENT_SELECTOR_EVIDENCE`, `NATIVE_CONTROL_EVIDENCE`,
`RUST_MISUSE_EVIDENCE` and `OWNED_DESCENDANT_CONTROL_EVIDENCE` (all `.md`).
They preserve actual ordinary exits, full strict UTF-8 streams, byte-order and
newline distinctions, unknown/empty/duplicate selector rejection, full ordered
mapping and owned-process deadlines. Raw captures, rather than inherited
returned-line arrays, carry literal semantic output evidence. The inherited
Get-NativeToolchainIdentity version metadata joins and trims returned lines;
those display records do not certify BOM/newline-preserving version output.
Exact compiler/runtime identity instead comes from complete binary/import file
pins. The final default-build Lean version additionally has its own exact raw
capture. No normalized legacy version display is used as a literal diagnostic
replay oracle. Integrity and cleanup run
independently after failure. The shared heavy mutex serializes native/Lean work.

The later `checkE01_program`, `checkE02_owner` and `checkQ10_capacity`
validation-proof edits restrict final proof comparison with `with_reducible exact`
at the identical expected propositions. Q10 first infers its projection under
ordinary transparency, preserving the independent expanded READY/capacity type.
These changes prevent sibling mutations from exhausting reduction or stack space.
The refreshed four-root build is `runs/build-20260927T062313663`; all four focused
siblings, two expected accepts and three admission/codec mutations pass at
`export-mutations/20260927T062619289-c2944c55`. Every rejection is the intended
single type mismatch, with ordinary exit 1 and empty stderr; every producer and
accepting consumer has ordinary exit 0 and empty streams. All 48 recorded
expected-signature entries (29 distinct check names) remain unchanged. Registry
`declaration_line` hints retain the original signature-freeze coordinates;
current failure locations come from the consumer's reconstructed theorem ranges
and raw compiler diagnostics. Full 34-case discovery passed at
`export-mutations/20260927T070116393-4514a722`: 66 producer/descendant stages
exited zero with empty streams, 32 consumers rejected at their intended surfaces,
and two consumers compiled. All 50 diagnostic objects were reviewed, with an
independent review of the first 25 cases and exact full-stream comparison of the
last nine to the previously reviewed focused run. The 5618-pin integrity check,
zero live restoration writes and shadow/mutex cleanup passed. The frozen
`EXPORT_DIAGNOSTICS.json` has SHA-256
`8688e2089ff225de19b741327af451eef2c019f0997e4652dfccecd181b0c542`;
complete exact Replay passes, as indexed below.

The first full Replay attempt at
`export-mutations/20260927T074439300-7ff52e82` passed four cases, then failed
closed on E05 because the consumer produced no ordinary exit. Its owned launcher
recorded a timeout against the unchanged 180-second deadline across a
2678.281-second wall-clock gap. Both E05 producers had already exited zero with
empty streams. The failed receipt, SHA-256
`71d77f10e3eb6b8aace2c2f78e81ba41645628353567ed1f667ae06451e0ec06`,
retains the empty consumer streams and failure. All 5619 pins and shadow/mutex
cleanup passed; all three reported owned PIDs were absent afterward. This is
not an accepted semantic rejection or a completed Replay. The earlier Discovery
consumer took 17.0926872 seconds. The focused diagnostic retry at
`export-mutations/20260927T083821597-51bfd2c5` passed before the new complete run:
both producers exited zero with empty streams and the consumer reproduced all
four frozen diagnostics with ordinary exit one in 7.050421 seconds. Root rehashed
all 24 raw pins and compared the complete streams. All 5619 integrity pins and
cleanup passed; its receipt SHA-256 is
`41ede20ddd3b154cfef2b1b041411164c3ebac42fe3bf709e62178d377bd5eab`.
Neither expectations nor deadlines were weakened.
Windows Kernel-Power and Power-Troubleshooter records subsequently identify a
critical-battery sleep interval from 07:48:21.3876846 to 08:32:57.3826635 UTC,
matching that gap. A read-only power-status check after resume reports AC power
and charging. No power configuration was changed.
The retained `sleep-interruption/SYSTEM_EVENTS.xml` under the failed run is
12996 bytes, SHA-256
`671251f2530b39c0ebae3d4e0d50865cdc4d24db8d68a880f85218c06f34d696`.

The 21-declaration axiom Discovery at `axioms/20260927T072200262` passed with
5604 pins and ordinary Lean exit zero. Root read every exact set and complete
raw diagnostic: one declaration uses no axioms, eight use only `propext`, three
use `propext` and `Quot.sound`, and nine use all three permitted constants,
including `Classical.choice`. The frozen `AXIOMS.json` has SHA-256
`a9b0ffcd5c9527d18936d2f76a6afc4964d517c47743e895f86a1c6a59d78895`;
its complete exact Replay passes, as indexed below. This inventory supplements the fixed-type
consumers and does not verify native runtime memory management.
`VALIDATION_APPLICABILITY.md` records a historical independent audit of 13,484
pins and the exact 365-module DLL closure after the first E01-only edit. At that
checkpoint only the validation source and its `.olean` changed, outside the closure.
All native-producing sources, generated C, objects, tools, DLLs and staged clients
remained identical at that validation-only checkpoint. Later header/Rust comment
corrections require a fresh native recipe and consumer batch under the strict
final-source contract. Existing native execution receipts remain historical receipts
for that unchanged executable chain; their broader whole-manifest fingerprints
are not relabeled as current after subsequent source and runner pins changed.

## Final formal replay

The complete producer-first 34-case Replay passes at
`export-mutations/20260927T084110803-e9431c50/RESULT.json`, SHA-256
`341c44469ecb17b4eebb2b45341a71ef8120a3b12fd0d2104496998b30d58866`. All 32 required intended rejections and both
acceptance controls reproduce the frozen full diagnostics. Producers and their
affected descendants compile before each consumer; ordinary exits, complete
streams, source/tool/artifact pins and shadow/mutex cleanup are checked. The
failed battery-sleep attempt remains separately recorded above; it contributes
no accepted rejection or missing case to this complete run.

The exact 21-declaration axiom Replay passes at
`axioms/20260927T085337097/RESULT.json`, SHA-256
`b298894304173a52874593ee066aea530c55574aa2897aa3a14f5cc9918a967f`. Every exact set and full raw diagnostic reproduces
the root-reviewed AXIOMS.json. The permitted trust base remains only `propext`,
`Quot.sound` and `Classical.choice`; native C/runtime correctness remains external.

Root independently checked the complete 34-case/21-declaration rosters,
66 clean producer stages, all ordinary consumer exits and complete frozen
streams, and rehashed the 808 raw capture-pin occurrences from these two runs.
The compact final review is `formal-final-review/REVIEW.json`, SHA-256
`9ebd86ed3052b0d65b3e905cc8c5cdc3321ba51d13fa5e2f223f3f7877481402`.

## Resource and trust interpretation

The current generated copy hook counts calls at instrumented generated
`lean_copy_expand_array` sites, not every internal runtime allocation. In the
historical fuel-100 probes, the original run copied 570837 cells in 69 calls; the exact thin loop copied 8273
cells in 1 call. Neither measurement establishes zero copying. The residual
initial numeric-bank copy is consistent with the generated persistent 8273-zero
array and first write; attribution to that instruction is source inference,
not a recorded native stack/PC sample.

Fixed program arrays contain 223371/223379 instructions, with requested outer
array bytes 1786992/1787056. Startup separately inventories 11135 fixed global
roots, 7154107 reachable objects and 179203176 requested outer bytes, plus 16
requested GMP limb bytes. Program/global graph inventories overlap and must not
be added. These are measured implementation storage, not modeled encoded words.

The pinned Lean 4.22 Windows x64 runtime uses GMP integers. Requested external
limb bytes use allocated 64-bit limb capacity, separate from the 24-byte outer
object. `RUNTIME_LAYOUT_SOURCES.md` documents the source/probe correction of the
earlier non-GMP assumption; prior wrong assumptions remain historical evidence,
not current layout authority. Requested bytes are neither allocator usable bytes
nor RSS. Native FFI layout, generated C/compiler correctness and runtime memory
management remain explicit trust assumptions supported by controls.

## Scope, decisions and remaining certification

The only protected formal-source amendment is the user-approved exact five
`@[macro_inline]` annotations in `STARTUP_AMENDMENT.patch`. Definition names,
types, bodies and theorem propositions are preserved. The generated expensive
proof-witness initializers disappear; the current startup passes. The original
3844-file raw/Git inventory and 55 frozen requirement rows remain separately
checked; the full scope checker allows only the approved insertions.

DD-LIFE-NATIVE1 entries record the export/repacking boundary, runtime layout and
exact thin-loop decision. WDD-LIFE-NATIVE1 entries record the frozen evidence
order, source/tool/artifact binding and staged-once control orchestration. The
last reduces setup overhead while preserving the exact 48 challenges and predicates.
The final certification wrappers preserve inherited sandbox Git configuration
while appending child-local advice/exclusion overrides. An initial wrapper that
replaced that configuration failed the design check; its failed raw receipt is
retained. No repository or user Git configuration was changed.
No algorithm, model, dependency, policy, gate or global helper has been replaced.

Final-check development evidence is separate from final certification:
`final-checks/20260927T055410813` passed the 3844-file scope check and retained
255 integrity pins, then failed the wrapper's Git configuration handling.
`final-component-development/20260927T055914124` passed the corrected exact-base
design check (83 paths: 26 code, 54 workflow, 3 neutral). Its full unchanged-policy
claim scan finished in 178.106 seconds and reported the three native comment
qualifiers subsequently corrected. The focused current-comment scan at
`final-component-development/focused-20260927T060601088` passed with four hits
and zero strict failures. These draft checks are not final report certification.

The committed `final_stream_controls.ps1` replays 15 component-language cases.
Its current run at `final-stream-controls/20260927T064348259-8b9ba5b5` passed four accepts
and eleven exact rejects, checked 161 pins and removed disposable files. The
cases use fresh owned PowerShell byte emitters; they do not claim native or
production-policy execution. The complete ID/handler/mutation/verdict/diagnostic
mapping now has an independent frozen hash before setup; the original 15 entries
remain verbatim. `FINAL_STREAM_MAPPING_EVIDENCE.md` records actual caller
challenges to that mapping. Git whitespace and clean-tree stages also require
both captured streams to be empty through the ordinal stream predicate; a NUL
diagnostic cannot count as an empty string. Actual production checker calls
remain separate from these helper controls.

Historical native runtime fixtures are pinned and explicitly labeled in
`PREDECESSOR_DLL_REUSE.md`; old DLL conflict checks do not claim freshly rebuilt
old binaries or substitute for new lifecycle execution. Retained client selector
controls have a new applicability review against unchanged consumed sources.
Failed development probes and obsolete fingerprints remain at their original
local evidence paths. No final aggregate or blind coordinator audit is claimed.

Final certification uses the complete final changed-path roster, including this
report, both decision ledgers, all frozen JSON expectations and public prose.
`COMMANDS.md` records the exact strict-design base and unchanged-policy claim
scan arguments. The final committed check also requires both whitespace checks
and clean Git state. Its successful receipt, final HEAD and this report's raw
and committed-blob hashes are recorded in the external
`.lake/lifecycle-native1/delivery/DELIVERY.json`. This separation avoids recursive
self-hashes while binding the actual delivered report. No push, integration,
publication or retirement occurred.

## Proof digestion

Conceptually, this adapter connects the already proved continuous owner to an
actual owned ABI and makes native backing storage retirement explicit. Its first
result comes from construction and the caller's real query; subsequent requests
consume the same modeled canonical store through charged re-entry. Logical
equality now survives a measured native replacement boundary without claiming
pointer identity or silently retaining construction inputs.

The live mathematical assumptions are the inherited input model, represented
endpoints, READY/halted premises for continuation and permitted Lean trust base.
The live implementation assumptions are the pinned compiler/runtime/FFI layout
and foreign-caller contract. A skeptical reader should next ask how much native
copying and GMP/initialization overhead remains, how a different runtime profile
would change the measurements, and whether a native machine specialization can
preserve the exact same export contract. None is answered by relabeling model
ticks as native time or modeled payload as native heap usage.
