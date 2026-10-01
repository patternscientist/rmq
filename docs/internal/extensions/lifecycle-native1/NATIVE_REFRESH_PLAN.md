# Native refresh after qualified comments

Status: the planned eight-stage production/execution batch completed; see
`NATIVE_REFRESH_EVIDENCE.md`. Its focused discovery exposed an insufficient
recipe fingerprint: named-property sorting collapsed ordered-dictionary pins
to the first entry. The repaired recipe function and its complete sensitivity
controls passed, but a new focused discovery under that repair and root's full
48-case replay are still required. Root owns the heavy-slot handoff, final
source freeze, expectation rebind and local result review. The contract and its
55 acceptance rows remain unchanged.

The exact comment bridge is recorded in `NATIVE_COMMENT_AMENDMENT.json`. Reversing
its four substitutions in memory reproduces both historical client-build source
hashes exactly, including byte lengths and line counts. The amended sources
passed the focused unchanged-policy claim scan at
`.lake/lifecycle-native1/final-component-development/focused-20260927T060601088/RESULT.json`
(SHA-256 `60d5c6b0bfa1f93331ad447e49571d2af7dc8f983cb09fbeb6ab293a2fa6be94`).
These facts support the comment-only source review. They do not preserve the old
native source fingerprint. N1-23 requires fresh consumers of the current source.

## Handoff and producing receipts

Wait for the final Lean consumer to freeze and for the existing heavy-slot owner
to release it. Use the fresh, successful standard
`lifecycle-native1-build-v1` Lean receipt supplied by root, with current source,
generated C/olean and tool pins. A thin-runner development receipt is not a
substitute for that standard producer receipt. Do not rebuild or edit Lean from
this leaf. All commands below are sequential; each existing runner acquires its
own shared heavy mutex, so do not wrap the sequence in a competing mutex.

Use the same pinned PowerShell executable for discovery and replay. Run each
command in a fresh `-NoProfile -File` child, retain its ordinary exit and streams,
and inspect its completed `RESULT.json` before advancing. A failed stage,
deadline, stale pin, stream mismatch, failed integrity check or failed cleanup
stops dependent work. Record the exact emitted receipt path instead of selecting
the newest directory by timestamp. The named variables below are explicit paths
chosen from successful producer results, not guessed future paths.

```powershell
# $Pwsh: exact pinned PowerShell executable.
# $FreshLeanReceipt: root's final standard Lean producer RESULT.json.
& $Pwsh -NoProfile -File scripts/lifecycle_native_build.ps1 `
  -Phase dll -LeanReceipt $FreshLeanReceipt

# Validate the DLL RESULT and DLL_MANIFEST before this next command.
& $Pwsh -NoProfile -File scripts/lifecycle_native_build.ps1 `
  -Phase clients -LeanReceipt $FreshLeanReceipt
# $FreshClientsReceipt: this successful clients RESULT.json.
```

The DLL phase derives the native closure from emitted C, verifies ABI prototypes,
rebuilds the aggregate global visitor and production/testing shims, and relinks
both DLLs. Its exact-source cache may reuse unchanged derived C objects. The
clients phase validates the fresh `DLL_MANIFEST.json`, then produces C, C++, Rust
and test artifacts. Its `nativeReceipt` pin names that manifest, whose `receipt`
pin identifies the successful DLL producer. Check both producing results,
derivation records, source/generated/tool/artifact pins, PE closure and cleanup.

Retain historical build receipt and staged-file identities before overwriting
standard build artifacts. Historical references are DLL producer
`runs/build-20260927T043851446/RESULT.json` and client producer
`runs/build-20260927T044516107/RESULT.json`, under `.lake/lifecycle-native1/`.
The latter has SHA-256
`9495af5ed6de8f4b0809f22af5ec3b54457291cf7328b62b05e165b9b3a5437c`.

Do not assert PE bit identity from the comment bridge. The existing link command
does not request reproducible PE output. Measure new artifact hashes, fresh
symbols/ABI and dependency closure, and inspect generated-closure differences
against the final Lean producer. Root's compiled-route review must explain any
change beyond the recorded comments or proof-only consumer work. If the current
runtime semantics cannot be connected to the existing expectation basis, obtain
new measurements before assigning a new basis; do not relax projections merely
to make a replay pass.

## Serial execution sequence

The measured prior maximum native fixture duration was 6.8187042 seconds;
startup was 3.7651555 seconds; ABI was 2.176185 seconds; the ten clients ranged
from 0.0973674 to 2.2276003 seconds; controls ranged from 1.6824 to 2.4884 seconds.
Use a 120-second per-native-stage ceiling with cold-start margin. Native build
stages retain the existing independent 300-second compile/link ceilings.
Startup and ABI currently hardcode 120 seconds internally. Do not substitute an
aggregate timeout for the retained actual per-child exits.

```powershell
$NativeRationale = 'Prior actual native maximum 6.82s; 120s permits cold runtime and host scheduling margin; exact ordinary exit, complete streams, pins and cleanup remain required.'

& $Pwsh -NoProfile -File scripts/lifecycle_native_replay.ps1 `
  -Phase Startup -BuildReceipt $FreshClientsReceipt -Variant production `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

& $Pwsh -NoProfile -File scripts/lifecycle_native_replay.ps1 `
  -Phase Fixtures -Cases LN1-W-TIES -BuildReceipt $FreshClientsReceipt `
  -Variant production -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

# Omit Cases: all 13 fixed fixtures, both observation modes.
& $Pwsh -NoProfile -File scripts/lifecycle_native_replay.ps1 `
  -Phase Fixtures -BuildReceipt $FreshClientsReceipt -Variant production `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

& $Pwsh -NoProfile -File scripts/lifecycle_native_replay.ps1 `
  -Phase AbiBoundaries -BuildReceipt $FreshClientsReceipt -Variant production `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

# Omit Cases: all ten C++/Rust client cases.
& $Pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/native_clients.ps1 `
  -Phase Run -BuildReceipt $FreshClientsReceipt `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

& $Pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/native_controls.ps1 `
  -Mode Discovery -Cases NC-NONE-BUILD -BuildReceipt $FreshClientsReceipt `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale

# Only after root reviews the focused current receipt and freezes the rebind:
& $Pwsh -NoProfile -File docs/internal/extensions/lifecycle-native1/native_controls.ps1 `
  -Mode Replay -BuildReceipt $FreshClientsReceipt `
  -ExpectationsPath $RefreshedExpectations -ExpectationsSHA256 $RefreshedExpectationsSHA256 `
  -CaseDeadlineSeconds 120 -DeadlineRationale $NativeRationale
```

Full fixtures must contain the frozen 13 IDs in order, 26 observed/unobserved
executions and 142 requests. ABI uses one process with 23 internal cases; its
wrapper fixture count zero is expected, so check `abi-boundaries.json.caseCount`
and the complete ordered ABI roster. Clients must contain all ten IDs. The
focused discovery must contain exactly one selected case, not claim complete
registry coverage. Final native Replay must contain all 48 cases in order with
`success=true`, `completeRegistry=true`, and independent integrity and cleanup
success. Its `campaignComplete=false` intentionally reserves whole-task
certification for root; it is not a failed native registry verdict.

Compare fresh startup data with the old startup receipt
`replay/20260927T044846600-daedf225/startup.json`. Only the two process-specific
program-array addresses vary; preserve their nonzero liveness. Compare every
other property exactly, including program initialized/capacity/requested bytes,
signature values, object counts, global-root counts and both memory inventories.
Historically the program lengths were 223371 and 223379, fixed global roots
11135, fixed reachable objects 7154107 and fixed runtime-reported bytes
179203176. Program-graph and fixed-global-graph measurements overlap and must not
be summed. An unexplained difference requires root review, not normalization.
The new startup measurement, fresh closure/symbol evidence and complete
unchanged diagnostic projections bind the current runtime semantics.

## Exact expectation provenance rebind

The frozen historical expectation file is `NATIVE_EXPECTATIONS.json`, SHA-256
`ac42d3ee867503737956e5c0091a5cd31d8b8822e27101aa458bf05c6844439b`.
Its old `inputFingerprint` is
`4fddb88fdf3b1b8b6d3217a29fc78ff79bcc56bd27e73d39e3c9965d56785047`.
The mapping SHA-256 remains
`ea90bd61fb7d226210aa47b3afd38cbca8953debaf3246c238a5785b20e69f2d`.
Its complete 48-element `cases` array, serialized by the unchanged runner's
`Canonical-Control` function as strict UTF-8 without BOM or trailing newline,
is 291770 bytes with SHA-256
`5697ab0c52c768001620aeda4ab5c4363c66c8e1d1d2f116d3140ab1c4d00ba9`.

1. Preserve a pinned copy of the old expectation bytes and verify the above
   identity. Independently validate the fresh focused discovery's full recipe,
   staged-file/dependency pins, actual exit/streams, cleanup, and exact healthy
   `NC-NONE-BUILD` projection against its historical case. A focused discovery
   does not invent verdicts for the other 47 cases.
2. Obtain a new focused discovery using the repaired recipe function, then read
   its `inputFingerprint` and retained `inputRecipe` from `RESULT.json`.
   Independently reconstruct all input pins, counts, exact text and hash before
   accepting that value. The old `065740444-c4346a02` discovery's fingerprint
   hashes only its first runner pin and cannot establish the full recipe. The
   repaired function computes the complete recipe before staging regardless of
   mode or selected cases; do not substitute a hash of only comments or the DLL.
3. Root creates the refreshed complete expectation manifest from the historical
   file. Change the top-level `inputFingerprint` only, and add explicit root
   provenance for this rebind. Preserve status `FROZEN_ROOT_REVIEWED`, schema,
   complete-registry flag, mapping, all 48 ordered cases, verdicts, explanations,
   exact projections and historical `discoveryReceipt` pins. Preserve the
   original full-discovery review as historical evidence. Do not relabel the
   focused one-case receipt as the discovery source for all 48 cases.
4. Rebind provenance records the old expectation pin/fingerprint, new
   fingerprint, current focused receipt pin, fresh Lean/DLL/client producer
   pins, comment-amendment pin, measured artifact/closure/startup comparisons,
   unchanged case-payload hash and the root reviewer. Root hashes the final
   manifest and passes that exact SHA-256 to Replay. Any source, tool, artifact
   or load-bearing helper change after discovery requires a new current recipe
   receipt before rebind; rewriting the expectations alone cannot certify it.
5. Full fresh Replay applies the unchanged challenge predicates and exact
   `Canonical-Control` equality to every newly measured projection. It must
   reproduce four accepts, 17 publication rejections, 17 operation rejections,
   six pre-build rejections, three pre-transfer rejections and one
   nondistinguishing `NC-SKIP-REPACK-QUERY`. Shared-scalar accepts still need an
   actually retained scalar; wrong-copy controls still need actual mismatch
   witnesses. Generation-local cleanup counters do not replace same-owner and
   memory preservation checks before transfer.

The repaired fingerprint recipe uses the wrapper's complete pre-staging pin
list. An explicit ordinal path dictionary rejects duplicate paths whose byte
length or hash conflicts; exact duplicate pins contribute one row. Absolute
supplied path spelling is the identity, without case folding or a claim about
filesystem aliases. `Array.Sort` with `StringComparer.Ordinal` orders all keys.
Each row is `path<TAB>bytes<TAB>sha256`; rows are joined by LF with one final LF,
encoded strict UTF-8 without BOM, then hashed. The receipt retains source,
unique and duplicate pin counts, all ordered unique pins, exact recipe text and
its hash in `inputRecipe`. Inputs are the wrapper, registry, clients receipt, current PowerShell,
fixture registry, contract/matrix and identity/process/stream/storage/integrity
helpers; all clients source/generated/tool/artifact pins; and its native
manifest pin plus the manifest's source/generated/artifact pins. The selector,
mode, ephemeral staged paths, reports, captures and expectation file are not in
that pre-staging fingerprint. Replay separately pins its expectation file.

Root separately reruns all 17 Rust misuse cases in Discovery, reviews exact
compiler diagnostics against unchanged classifications, freezes the fresh Rust
source/tool fingerprint and runs full Replay. Do not run it concurrently with
the native producers or any other owner of the shared heavy slot. The existing
Rust runner retains its bounded 60-second compiler stages and the same 15
expected rejections plus two expected accepts.

## Evidence boundary and digestion

The new comments qualify foreign-handle preconditions and distinguish native
runtime allocation/lifetime behavior from modeled resources. Their reverse-byte
bridge is exact, but the producing recipe changed, so old execution receipts
remain historical. This plan supplies a bounded fresh-production path and a
reviewable provenance change while preserving all measured expectation content.
No new expected failure is inferred, no binary equality is assumed, and no
acceptance row closes from this plan alone. The skeptical follow-up is whether
the fresh producers and all current measurements actually match this unchanged
oracle; only the retained executions and root's review can answer it.
