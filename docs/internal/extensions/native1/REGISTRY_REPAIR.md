Status: INCOMPLETE
Phase: REGISTRY_REPAIR_VERIFIED

This bounded producer belongs to NATIVE-1; the full native capstone and the
original 31 frozen acceptance rows remain open. No frozen row is rewritten.

Worktree: `C:/Users/poin/.codex/worktrees/1817/RMQ`; branch
`codex/native-1-packed-execution`; reviewed base
`c8c266f987d46284382cc93c5fa8e01bd7a9ffb9`; governance
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Preflight passed with required `rmq-proof-sprint` and runtime catalog
`rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint` before edits.

## Frozen bounded repair contract

The source review and measured coordinator receipt are read-only inputs:
`C:/Users/poin/Documents/RMQ/extension-coordination-20260911/NATIVE1_ROUTE_SOURCE_REVIEW.md`
and `native1-route-review/registry-kind-downgrade.json` in that directory.
The latter reports PASS `source-core-mutation` while its only verdict is
`stale-source rejected`: the old ID inventory did not constrain dispatch.

| ID | Exact assigned requirement | Evidence needed | Consumer and attack | Initial status |
| --- | --- | --- | --- | --- |
| REG-SEMANTICS | Pin the complete semantic case contract before dispatch: ID, kind, required fixture/mode and expected operation/result fields. Reject changed or missing load-bearing fields and undeclared variants. Preserve explicit versioning for intentional registry evolution. | Production script rejects every field deletion/change and undeclared shape before dispatch; original registry accepted. | `packed_native_route.ps1` consumes the exact v2 registry; same-ID mutation kind/fixture substitutions must fail. | OPEN |
| REG-ATTACKS | Add production-boundary controls for the measured same-ID/source-pin downgrade and the source review's same-ID/ordinary-fixture substitution; retain positive original-source-mutation and correctly named source-pin controls. | Real bounded subprocess verdicts; exact source failure surface, complete restoration. | Positive source-core mutation must invoke Lean and fail at `routeCore_source`; stale-source case must invoke identity rejection. | OPEN |
| REG-SELECTORS | Actual subprocess selectors omitted/valid/empty/whitespace/malformed/unknown must be nonvacuous and bounded using existing owned-process helper. | Real OS PowerShell process entry, explicit empty argument survives quoting; omitted selects all exact cases and valid selects one. | No helper-only exception assertions; executed/expected counts and identities checked. | OPEN |
| REG-RESTORE | Mutations must restore exact bytes in finally and verify clean restoration. | Hash and pre/post Git-diff equality for tracked registry and manifests; source mutations retain existing exact checks. | Failed child or unexpected accept cannot leave mutated files. | OPEN |

These rows refine `REPLAY-EXACT-REGISTRY`,
`REPLAY-SELECTOR-NONVACUITY`, `REPLAY-SUBPROCESS-DEADLINE`,
`INV-CERTIFICATE-ANTI-BYPASS` and `INV-MUTATION-REPRODUCIBILITY` for this
bounded repair only. No finite fixture collection proves general Lean execution.

## Verification plan

Development: parse the two changed scripts; exercise cheap subprocess selectors
and registry rejections (120 seconds per child, 8 MiB output cap, owned process
tree). Mutations are against the production runner, not copied predicates.
Final bounded repair: after the root's toolchain-manifest edits stabilize, run
the exact full control registry once, including omitted/full dispatch and the
original source mutation. Reserve the one shared Lean slot with the root for
that source mutation. Native execution uses the already authorized host context
because earlier receipts show sandbox startup stalls before argument parsing.
Record time, exit, stderr, restored hashes, selected IDs/counts and the exact
registry/script pins. The root owns full integration, public prose/policy checks
and final capstone validation. No aggregate is scheduled by this leaf.

## Evidence append area

Implementation and measured results will be appended without modifying the
frozen repair contract above.

### Implemented boundary and review rationale

`native1-route-registry-v2` explicitly supplies every case's operation, mode,
expected exit/result, executable or source path, and the mutation anchors and
failure surface where applicable. The production runner checks SHA-256
`D129ADB049146FDB67FD4E0C7A186A7785596803491E06CB22880C0AF08B429E`
before JSON parsing and independently checks the schema and ordered 16-case
roster. The exact-byte contract deliberately rejects formatting changes,
unknown fields, duplicate JSON keys and all altered values, rather than
silently canonicalizing a changed registry. Intentional evolution requires
updating both the explicit version and reviewed source pin. The parent approved
this choice. The existing package LF attribute preserves these committed bytes.

The original 14 semantic cases remain, with their operations pinned. Two
explicit C++ cases are added: `cpp-n9-full` compares the entire independent
reference output; `cpp-malformed-instruction` requires exit 1 and
`ERROR instruction shape`. They use the parent-built C++ executable in the
same three-artifact v2 build inventory as the Rust executable and Lean-core DLL.

Every load-bearing value used by native dispatch is taken from the pinned
entry. The mutation uses its actual anchor/replacement, compiles its source,
and matches its expected type diagnostic at its declared proof line; source-pin
rejection consumes the declared exact identity error. Results retain the case's
full semantic contract, operation-specific evidence and exact restoration.

The production control script has an independent exact 51-case roster. It
invokes the route script using a fresh PowerShell OS process with `-File` and
real argument arrays through `Invoke-RMQOwnedBoundedProcess`. It does not call
the selector helper in its own session. Process receipts retain the executable,
arguments (including an explicitly empty string), exit, stdout, stderr,
duration, deadline and Windows job ownership. Four rejected selector classes,
both original same-ID attacks, the analogous stale-case substitution, 30
field-deletion/change representatives, nine additional registry shape/key/
format cases, three manifest-removal cases, valid smoke, and omitted/full
dispatch are covered. Omitted/full must execute all 16 exact route cases; its
receipt is also checked for the distinct source-mutation and source-pin evidence.

These field representatives test each of the 15 case-field names; they are
not an exhaustive independent proof about arbitrary JSON. The production
boundary is the reviewed SHA-256 pin over the complete registry before parsing,
using the same source/artifact identity convention as the rest of this native
campaign. It does not contain field- or formatting-specific exceptions. This
is a deliberate narrow, versioned registry API.

All mutated tracked bytes are restored in `finally`; the control compares
both pre/post hashes and the pre/post Git diff. Restoring the pre-existing
dirty state is intentional: the script must preserve concurrent work without
pretending the whole shared worktree was initially clean.

### Development evidence

The coordinator's original false-positive receipt and correctly named
source-pin positive are preserved byte-for-byte at
`commands/registry-kind-downgrade-coordinator.json` and
`commands/registry-source-pin-positive-coordinator.json`. They describe the
old production runner; they are not results from the repair.

The repaired production CLI passed these focused controls on Windows with
PowerShell 7.6.5; all had 120-second owned-child deadlines:

| Control | Receipt | Result |
| --- | --- | --- |
| Explicit empty OS argument | `commands/controls-20260912T091008993.json` | Exit 1; `invalid exact selector`; no semantic case executed |
| Same ID changed to source pin | `commands/controls-20260912T091026831.json` | Exit 1; `exact semantic registry mismatch`; exact restoration |
| Same ID changed to ordinary fixture | `commands/controls-20260912T091036366.json` | Exit 1; `exact semantic registry mismatch`; exact restoration |

These receipts precede the addition of explicit command arguments to every
child receipt; their stored selectors and actual owned-child rejection output
remain development evidence. Final roster evidence must follow the parent's
stable v2 toolchain/build manifest. Both scripts parsed without errors and
scoped `git diff --check` passed after implementation. No Lean compilation or
native execution was invoked by these three rejection controls.

The field attacks were then strengthened to replace or delete only the named
property span in the original bytes. The controls independently compare the
parsed result with the intended one-property mutation, so unrelated semantic
changes cannot accidentally supply the failure. The same-ID fixture attacks
replace only that one case object. This avoids confounding a field rejection
with full-document JSON reformatting. The minimal source-pin-only downgrade
passed at `commands/controls-20260912T091719835.json`; the earlier receipt is
retained as development history rather than silently superseded.

The parent's measured complete toolchain inventory cost 159.128 seconds cold.
Each positive child therefore has a 900-second deadline; cheap malformed
selectors, registries and fixture/build inventory shapes reject before that
inventory. Full toolchain verification still precedes every semantic/native
case. This measured source-provenance I/O is distinct from proof-witness
initialization and from the native query's execution time.

Before the final campaign, the registry had 3,572 bytes, zero CR bytes and 21
LF bytes. Git's filtered and unfiltered blob hashes both were
`311b2f46760fe19ef5487f3b7ce8c8cf122fa1e0`; the embedded SHA-256 therefore
matches the fresh-checkout LF representation. No version change was needed.

The v2 artifact startup evidence retains two launch failures and their actual
repairs. The generic command wrapper rejected `-Arguments @()` at parameter
binding, before invoking native code
(`commands/repair-native-startup-binding-failure.json`). Calling the existing
owned-process helper directly preserved empty arguments, but the first call
omitted the required Lean runtime directory from PATH and exited
`-1073741515` in 2.599 seconds, with no timeout or output
(`commands/repair-native-startup-owned.json`). Dependency inspection showed
`packed_route.dll` imports `libInit_shared.dll`, which is present in the pinned
Lean `bin` directory. Adding that directory exactly as the production route
already does was a material environment correction; startup then returned
the expected usage text and exit 2 in 2.236 seconds
(`commands/repair-native-startup-runtime-path.json`). Neither failed launch
is counted as a semantic pass or a timeout.

The known `smoke` selector subsequently passed in 38.693 seconds with complete
toolchain verification, under a 480-second owned deadline:
`commands/repair-known-smoke.json` and its exact route receipt
`commands/route-20260912T092619569.json`. A stopwatch-only addition to route
receipts then separated complete toolchain-verification time from the
per-executable process times in the final campaign. Computational code and
all 19 source/three artifact pins stayed fixed.

### Proposed task-specific WDD entry for the parent ledger

**WDD-NATIVE1-REGISTRY-KIND.** The coordinator measured a false certificate:
changing only `source-core-mutation.kind` to `source-pin` preserved the ID and
produced a passing record whose evidence was only stale-source rejection. The
ordinary-fixture substitution was first derived by source inspection; the
repaired runner now rejects both substitutions at its real subprocess boundary.
An ID roster plus a recorded registry hash merely documented the changed test;
it did not enforce what that ID meant. The v2 replay pins the complete registry
bytes before parsing and declares operation/result/exit/mode/source fields
explicitly. Unknown fields, duplicate keys and formatting changes also require
an intentional version-and-pin update. This narrow accepted-input contract was
chosen over loose schema-only dispatch or mutable per-case expectations.

The 51-case production-boundary controls retain the original mutation and
source-pin positives, test every case-field name through deletion and change
representatives, distinguish actual OS empty from omitted selector arguments,
and verify expected/executed case identity. Owned child processes retain full
outcomes and exact mutations restore hashes and existing Git diffs in `finally`.
The parent adds C++ source/artifact identity in the v2 build inventory; the
registry adds both complete successful output and malformed-input exit/error
comparisons against that same compiled-core DLL. This repair certifies the
route campaign's dependency coverage; it does not close the finite-limb,
binary-loading, canonical-composition or final native-capstone requirements.

### Proof digestion

Conceptually, a test name now has a fixed operational meaning that must survive
dispatch and appear in the output evidence. In plain English, the runner cannot
quietly replace its promised theorem-breaking test with an easier passing test.
The downstream consumer is NATIVE-1's final mutation campaign, which still must
expand to the complete checked-limb/binary-loaded source chain. Live assumptions
include the fixed registry pin, the PowerShell/OS process boundary, Git/hash
restoration and the separate native compiler/runtime/FFI assumptions. A
skeptical graduate student should next check that the final public native
capstone itself is the mutated proposition and that every expected diagnostic
pins the same objects and quantifiers as its positive consumer.

### Version 3 repair after the first full campaign

The first complete controls invocation did **not** pass:
`commands/repair-controls-final.json` exited 1 after 746.059 seconds, without
timeout. `commands/controls-20260912T094238749.json` records 50 passing
controls and a failing `omitted-full`. Its route receipt
`commands/route-20260912T094135118.json` records 13 passing native cases,
followed by the C++ malformed-instruction failure. The native C++ consumer
correctly returned exit 1 and `ERROR instruction shape` on stderr; the runner
had compared only stdout. No Lean source mutation ran in this attempt, and
the exclusive compile slot was released immediately after diagnosis. This
is a harness/channel-contract defect, not a counterexample to the C++ repair.

The parent approved explicit version-3 output semantics. Each native case now
declares `outputChannel` and `expectedOtherOutput`. Successful results use
stdout with empty stderr; Rust parser failures retain their exact stdout
error and stderr `Lean parser rejected input`; the C++ parser failure uses
stderr with empty stdout. The production runner compares both channels and
the exit code. The v3 registry retains the exact 16 case identities and pins
all bytes with SHA-256
`33609A968052FB37894CACD9721BE12AD1FBAFF0BF332A0287CD1AA38622F539`.
Two new field names add four deletion/change controls, producing an exact
55-case control roster with an explicit v3 result schema. All previously
measured failure receipts remain committed evidence.

Source inspection also found that two control IDs included `proofLine`, while
the optional control-selector grammar allowed only lowercase letters. The
control selector now allows ASCII letter case and still requires
case-sensitive membership in its exact roster; the native route's own
lowercase selector contract is unchanged. Focused real-child calls to
`registry-delete-proofLine` and `registry-change-proofLine` both passed in
`commands/controls-20260912T094700539.json` and
`commands/controls-20260912T094711304.json`. An unknown uppercase spelling
must still reject. The new channel fields similarly have real production
delete/change controls rather than merely appearing in metadata.

The old 50/51 run is development evidence only. Final v3 checks must exercise
the corrected C++ channel, original source mutation, correctly named source
pin and exact 55-case roster before this bounded producer is reported ready.

### Final bounded verification

The v3 campaign passed all **55/55** controls and its omitted-selector child
passed all **16/16** native cases. The outer owned invocation exited 0 in
617.614 seconds under an 1,800-second deadline; there were no timeouts,
output-limit failures, missing cases or surviving mutations. Durable receipts:

| Surface | Exact receipt | Measured result |
| --- | --- | --- |
| Entire v3 control invocation | `commands/repair-controls-v3-final.json` | Exit 0; 617.614 seconds |
| Exact control roster | `commands/controls-20260912T100023269.json` | Expected 55; executed 55; every verdict passed |
| Actual valid selector | `commands/route-20260912T095846357.json` | Expected/executed only `smoke`; bound selector true |
| Actual omitted selector | `commands/route-20260912T095926516.json` | Expected/executed all 16 IDs; bound selector false |
| Corrected C++ error, focused | `commands/repair-v3-cpp-error.json` | Exit 0 for checker; C++ exit 1, exact stderr error, empty stdout |
| Unknown uppercase control selector | `commands/repair-v3-control-unknown-uppercase.json` | Expected exit 1 and `invalid exact controls selector`; no semantic dispatch |
| Compact pins and positive-child timings | `commands/registry-repair-final-summary.json` | Full control/route/source hashes and counts |

The exact final runner SHA-256 is
`D483F5764E34FFBBCD3C2DD0FE24D4CE3CC2EF4E0307C8751AF8C1A3E5401DEF`;
the controls script SHA-256 is
`2720061FF3A2A47C77F221A6BF5831D0CF60EF1E27B8A045AE7C2EC529FDBE21`.
Both final positive route calls consumed build-manifest SHA-256
`B07F660A24BA5966D7CD5BDA3D2C7C7D90ECF6FDD4192DE0B709C486D5F006F9`.
Complete toolchain verification took 34.8952181 seconds in valid smoke and
28.0026912 seconds in omitted/full; the corresponding owned child calls took
44.133 and 93.205 seconds. These times include provenance verification and
process overhead and are not query-time model costs.

The original source-core mutation genuinely compiled the modified
`RMQ/Core/WordRAM/Native/Route.lean` with Lean 4.22, `-j 1`, and a separate
`mutated.olean` destination. It exited 1 in 6.034 seconds under a 120-second
deadline. Its required diagnostic was exactly:

```text
RMQ/Core/WordRAM/Native/Route.lean:114:2: error: type mismatch
```

The altered `routeCore` used fuel zero while the consumed
`runThin_projection observeReads memory program fuel s {}` proves the fold
of the original `runFinite memory program fuel s` transitions. Thus the
actual consumer failed at its original quantified fuel and state objects.
The separate correctly named source-pin case rejected exactly
`stale native source: RMQ/Core/WordRAM/Native/Route.lean`. Both cases restored
source SHA-256
`C00240A5A2E994DD1A996C79A52FF54780A0B5A87010B3DBCF4ED3A61244A5C5`
and verified identical Git diff. Every registry/manifest mutation likewise
records before/mutated/restored hashes and exact pre/post Git restoration.

The shared Lean slot was released after the source mutation. Chat delivery
alone did not establish its start time: the underlying helper records duration
but no absolute start/end timestamps. The root reconstructed causal timing
from the MachineChecks receipt (created/written 10:00:15.976/977 UTC), the C++
malformed fixture write (10:00:14.0801155 UTC), and that preceding owned C++
call's 2.072-second duration. The C++ call therefore could not finish before
10:00:16.1521155 UTC, and the subsequent source compile could not start before
that. This implies at least 0.174 seconds of separation from the completed
Machine check, assuming stable UTC during the interval. It is an explicit
causal inference, not a directly captured source-process start timestamp.
The root will add absolute UTC intervals to future native-harness calls;
the frozen passing route was not edited merely to add timestamps.

Both scripts parsed successfully, the final registry again had zero CR and
21 LF bytes at its pinned SHA-256, and scoped `git diff --check` passed. No
shared ledgers were edited by this leaf, and no commits were made; the parent
owns ledger integration, strict per-commit policy, the final committed-range
checks and all full-capstone verification.

| Bounded row | Final local evidence | Status |
| --- | --- | --- |
| REG-SEMANTICS | v3 complete field pin; 34 minimal field deletion/change controls plus schema/shape/key/format attacks, all through production dispatch | VERIFIED bounded producer |
| REG-ATTACKS | Both measured/source-derived substitutions reject; original source mutation fails at line 114; correctly named source pin separately rejects | VERIFIED bounded producer |
| REG-SELECTORS | Real child-process empty/whitespace/malformed/unknown rejections; actual valid and omitted native selectors; both camel-case control IDs accept and unknown uppercase rejects | VERIFIED bounded producer |
| REG-RESTORE | All registry/manifest/source mutations preserve recorded bytes and existing Git diff; final source and registry hashes match baseline pins | VERIFIED bounded producer |

This completes the assigned bounded replay repair. It does not accept or close
any of the original 31 full NATIVE-1 criteria, does not instantiate a new native
capstone, and does not certify another host. The next native binary validation
campaign must pin its own operational fields and actual source theorem in the
same manner, with explicit stream/error contracts and absolute process times.
