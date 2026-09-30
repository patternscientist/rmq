# Historical single-E01 validation applicability audit

**Status: HISTORICAL, limited to the single-E01 snapshot below.** This audit
does not establish applicability at the later or final candidate frontier.
Subsequent E02/Q10 proof edits, four native comment-line changes and selector
guard changes mean that the complete producing/replay recipe is no longer the
one audited here. Fresh build/discovery identities and a separately reviewed
expectation-provenance bridge are required for that later frontier. Preserve
this receipt and its original input hashes; do not update it to describe those
later changes or treat its two-mismatch inventory as a current checkout check.

At the recorded single-E01 snapshot, the exact proof-only edit to
`checkE01_program` did not require rebuilding or rerunning the native executable
chain. A read-only audit rehashed 13,484 unique
input pins and reconstructed the DLL's complete 365-module import closure.
Every executable-producing source, generated native C file, object, tool,
runtime, DLL, client and inspected staged artifact matched its producing
receipt at that snapshot. The only two mismatches were the validation consumer source and its
`.olean`, both outside the DLL dependency closure.

This is **scoped applicability**, not successful current-byte reuse of the old
whole manifests. Those manifests genuinely contain two stale provenance pins.
They remain unchanged and must not pass a strict whole-manifest reuse guard by
silently dropping, rewriting or overlooking those mismatches. The revised
consumer still requires its own compilation, mutation, axiom and final checks.

## Exact edit and excluded provenance

At `RMQ/Validation/LifecycleNativeContract.lean:37`, the edit inserts precisely
the 24 bytes `by with_reducible exact ` before the existing proof term:

```lean
theorem checkE01_program : cachedProgram model = (Layout.program model).toArray :=
  by with_reducible exact (export_contract model xs left right domain hl hr).program
```

Removing that one insertion reproduces the previous 46,155-byte source hash
exactly. Imports, propositions, object arguments and computational declarations
are therefore unchanged. The generated validation C also remains byte-identical;
the changed `.olean` is a proof-facing artifact, not a DLL object input.

| Extra provenance path | Previous bytes / SHA-256 | Current bytes / SHA-256 |
| --- | --- | --- |
| `RMQ/Validation/LifecycleNativeContract.lean` | 46155 / `4e3a18078aa253065fbec51d2149539ae5f97a84bb2b0a05fd4f0a130659b2ab` | 46179 / `224dc54ffd2f110552105892c2fbe65da2f674d625ab05f80107e9832b0b9473` |
| `.lake/build/lib/lean/RMQ/Validation/LifecycleNativeContract.olean` | 242752 / `8296cb5f6ee205b5e2ca7ac990486cd61195fb1267faae992759287faa6e6497` | 242752 / `008d52dedf2f9c35d9510015c72688dcf1665e0a5858c6e212372e5def2ff0ca` |

Both build receipts listed below pin these files in their broad Lean-target
provenance. The DLL build's derivation contains neither validation module nor
validation C/object. `lifecycle_native_build.ps1:240` obtains the broad target
closure for source/generated pins; line 261 separately obtains the import
closure of `RMQ.Core.WordRAM.Native.Lifecycle.Entry`; line 308 passes only that
native closure to `Build-LN1Native`. The independent audit used the same
anchored RMQ import grammar as `lifecycle_native_identity.ps1:40`, recursively
read current source, and obtained exactly the 365 ordered modules in the
preserved DLL derivation.

The broader provenance has six additional proof-facing modules:
`Native.Lifecycle`, `Native.Lifecycle.AdmissionContract`,
`Native.Lifecycle.BoundaryProofs`, `Native.Lifecycle.Contract`,
`Native.Lifecycle.Repack` (under `RMQ.Core.WordRAM`), and
`RMQ.Validation.LifecycleNativeContract`. None belongs to the Entry closure.
Only the final module's source and `.olean` differ in this audit.

## Retained audit and producing receipts

The structured audit directory is
`.lake/lifecycle-native1/validation-applicability/20260927T055818202/`.

| Audit artifact | Bytes | SHA-256 |
| --- | ---: | --- |
| `RESULT.json` | 5518 | `c40efc837d75df0a6e860bf29d62aae1f8ccad9e2bd9ba4fc3fba6452ea0b024` |
| `PIN_REVIEW.json` | 7220310 | `b3381243fe102e10d686d6478c4acff90fb82eb9087af983ded0f2aeb108150b` |
| `CLOSURE.json` | 19699 | `718de139b312d70fa733242cbabe51592b5672392908e0cddddbf18e3e76d4d3` |

`PIN_REVIEW.json` records all 13,484 absolute input paths, their producing
receipt categories, expected and observed byte counts/hashes, per-file read
stability and match verdicts. Exactly 13,482 match and the two explicitly
listed extra-provenance pins differ. No input receipts contain conflicting
pins for the same path. The audit read 5,212,309,456 bytes in 29.204 seconds;
it ran no compiler or native semantic process and repeated no fixture answer
or stream validation.

Inputs include both receipts' full source and generated inventories; 4,856
Lean tool files, 48 Rust tool files, 6,545 C++ include/library files, 145 tool
runtime files and four external tools; all 365 original emitted C files,
365 derived C files, 365 native objects and the global visitor aggregator;
four DLL-stage and fourteen client-stage artifacts; and six staged-file pins
from each of the full fixture and final native-control receipts. These category
counts overlap and are not added to obtain the unique total. A reused file's
categories remain visible in the structured audit.

The four input receipts, under `.lake/lifecycle-native1/`, retain their original
identities:

| Producing or executing receipt | SHA-256 |
| --- | --- |
| `runs/build-20260927T043851446/RESULT.json` | `2e463e730ab5f10f9390a8c1d8a7ba5c0ee0c1afef0e29d79d49c7d45b246033` |
| `runs/build-20260927T044516107/RESULT.json` | `9495af5ed6de8f4b0809f22af5ec3b54457291cf7328b62b05e165b9b3a5437c` |
| `replay/20260927T045754455-9f927669/RESULT.json` | `dba6e61f39c83f3b45db1ca9612f70f56139a482c6fc7c66a90b84a171954497` |
| `native-controls/20260927T052620110-f51e89eb/RESULT.json` | `5b960e5cc8517adc315463cd531f4e68af600abf9e1bcdc2741cd71b14019d06` |

The DLL receipt consumes the earlier four-root Lean receipt; the client receipt
verifies the DLL manifest and builds the C/Rust/C++ artifacts; the full fixture
and final native-control receipts consume the client build and stage its actual
artifacts. Their producing identities are preserved even though the broader
current proof-checking frontier has moved.

## Meaning and limits

For N1-11 and N1-23, the checked bridge is unchanged executable-producing
dependency closure and bytes, followed by unchanged built and staged artifacts.
It is not an assertion that all old source/proof provenance still describes the
current checkout. Compiler/runtime/FFI assumptions remain as documented in
[COMPILED_ROUTE_EVIDENCE.md](COMPILED_ROUTE_EVIDENCE.md) and
[NATIVE_EXECUTION_EVIDENCE.md](NATIVE_EXECUTION_EVIDENCE.md).

This historical conclusion applies only to the exact edit and hashes above.
It does not apply to the subsequent E02/Q10, native-comment or guard changes.
Any change to
the executable source/import closure, native C/object derivation, ABI,
compiler/runtime or built/staged artifacts requires a new applicability
decision. The revised fixed-type consumer and export mutation campaign must
be certified at their current source identity; this audit does not certify
their acceptance surfaces, final report bytes, whole candidate or coordinator
acceptance. Ordinary strict old-manifest reuse correctly rejects its two stale
pins.

Proof digestion: changing how one validation proof elaborates changes its
proof artifact without changing the program that produced the native evidence.
The separation is established by an exact dependency/byte audit, not by merely
calling the edit proof-only. The next skeptical check is whether the revised
typed consumer still rejects every required mutation at the intended surface;
that remains the separate export campaign.
