# OPT-1-R1 canonical source and compiled artifact profile

This profile connects the raw Git sources at
`aecf4a580c591e8f694a3699e19e843198089194` to new, actual Lean compilation.
It does not reinterpret or replace the historical OPT-1 runtime receipt.
The production certificate runner requires its own literal SHA-256 pin for
`BUILD_RECEIPT.json`; a live checkout cannot choose that expected receipt.

`SOURCE_PROFILE.json` is immutable and pinned by the production profile library.
It records the Git blob ID, raw Git SHA-256, canonical SHA-256, byte length and
direct import list of each of 263 sources: all 261 transitive RMQ imports of
`RMQ.Validation.PackedOptimized`, that validator itself, and the exact
`RMQ.Core.WordRAM.Optimization.Consumers` module. It also records the configuration
files and the unchanged owned-process implementation. Its executable/library
inventory covers all 4,823 files under the pinned Windows Lean distribution's
`bin` and `lib` directories (1,983,374,857 bytes), including implicit `Init`, `Std`,
Lean, Lake, native DLLs, and the compiler binary. This is a distribution-specific
profile, not a version-string-only test.

`TOOLCHAIN_VERSION.json` retains the actual bounded `lean --version` result:
Lean 4.22.0, Windows x86-64, compiler commit
`ba2cbbf09d4978f416e0ebd1fceeebc2c4138c05`, Release. The child succeeded in 2.696
seconds under a 30-second deadline with empty stderr. An ad-hoc outer comparison
initially expected an incorrect compiler commit suffix and failed; this did not
change the successful child result or the already pinned binary. The separate
`TOOLCHAIN_VERSION_CHECK.json` records that failure and the recheck of retained
output against the requested version/platform and pre-existing executable hash.
No child was rerun and no raw receipt was rewritten.

The sole admitted source serialization is strict UTF-8 with no leading BOM and
no bare CR, replacing each CRLF pair by LF. No whitespace, comment, identifier,
token or trailing newline is removed. Raw Git/LF and default Windows/CRLF sources
therefore have the same canonical identity. Both raw and canonical source hashes
remain distinct. A semantic edit, a missing source or dependency, a different
toolchain/configuration, a changed manifest, and stale or changed artifact bytes
fail closed. The complete directory inventory also rejects omitted or added
toolchain files. Foreign ambient `LEAN_SYSROOT` is rejected by the profile API.
The compiled-artifact cache must contain exactly the 263 declared `.olean`
files and their ancestor directories, with no extra files, empty directories,
optional `.olean.server`/`.olean.private` sidecars, or filesystem aliases. An
extra `Init.olean` or even an empty `Init` package directory can change Lean's
package-root resolution and is rejected. This profile requires a dedicated
cache: a broad Lake build cache containing other modules is not accepted. Run
broad certification in its own private build tree.

The raw-source manifest was generated from a bounded `git archive` of that exact
commit, with raw blob IDs independently calculable as Git's SHA-1 of
`blob <byte-length> NUL <raw-bytes>`. The retained archive used for construction
had SHA-256
`5ee3dbfed2aa1171522a572be7f313444b40946d9ad9c720bc864f4607125fba`.
Its command succeeded in 2.656 seconds under a 60-second Windows owned-job
deadline and a 4 MiB output ceiling. Its sole stderr line was the host's existing
Git ignore-configuration permission warning; the command exit was zero.
An initial manifest-authoring parser mistakenly included prose beginning with
`import` inside a Lean block comment. This was diagnosed before manifest creation
or compilation; the extraction used nested block-comment and line-comment
removal and exact module spelling checks. No proof source was edited.

## Reproducing the production profile

Use the pinned Windows x86-64 Lean 4.22.0 distribution. In a fresh checkout of the
repair candidate, dot-source the library and build into a new private directory:

```powershell
$repo = (Get-Location).Path
$lean = 'C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/lean.exe'
. scripts/packed_optimized_replay_profile.ps1
$build = Build-OPT1ReplayProfile -RepoRoot $repo -LeanPath $lean `
  -BuildDirectory (Join-Path $repo '.lake/reviewer-opt1-build') `
  -ReceiptPath (Join-Path $repo '.lake/reviewer-opt1-build-receipt.json')
```

This first checks the versioned source and complete toolchain inventory, then
materializes canonical LF sources into a fresh private tree. It compiles every
module once, in dependency order, using relative source and output arguments and
`-j1`. It does not reuse artifacts based on timestamps, share mutable caches,
link another checkout's cache, or hide an aggregate Lake fallback.
The default limits are 600 seconds per compiler child, 14,400 seconds overall,
and 4 MiB of retained process output. The existing owned-process implementation
retains exit/stdout/stderr, applies kill-on-close Windows jobs and cleans up in
`finally`. Each module receipt records before/after canonical source hashes,
direct dependency artifact hashes (including implicit `Init`), the actual
command/result, and the resulting `.olean` hash. Failed attempts remain in the
private build's `BUILD_ATTEMPT.json` and supplied receipt path.

Next install the independently copied compiled files using the externally pinned
receipt value from the candidate's certificate runner:

```powershell
# Use the literal $buildReceiptSHA256 in the versioned certificate runner.
# Do not replace it with a hash of a newly supplied receipt.
$pin = 'REPLACE_WITH_CANDIDATE_LITERAL_RECEIPT_PIN'
Install-OPT1ReplayArtifacts -RepoRoot $repo -LeanPath $lean `
  -ExpectedReceiptSHA256 $pin -ArtifactDirectory $build.ArtifactDirectory
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_certificate_replay.ps1 -LibrarySelfTestOnly
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_certificate_replay.ps1 -OnlyCase A01-UNCHANGED
powershell -NoProfile -ExecutionPolicy Bypass `
  -File scripts/packed_optimized_certificate_replay.ps1 -OnlyCase W03-widthBounds
```

The install operation first checks every source, toolchain and artifact against
the pinned receipt, makes ordinary independent file copies into this checkout's
`.lake/build/lib/lean`, and checks the copies. A reviewer may also install from a
private copy of the original canonical build's artifacts using the same API;
the original actual-compilation receipt still binds those exact bytes. A copied
artifact hash by itself is not source-compilation evidence.

The installer assigns the same current installation timestamp to all copied
`.olean` files after checking their bytes. This makes the installed artifacts
newer than a fresh checkout for the unchanged runtime's additional mtime check.
The timestamp describes installation only: it neither substitutes for source and
artifact hashes nor changes the actual compilation observations in the pinned
receipt. The API returns `InstallationUTC` separately.

`BUILD_DRIVER.ps1` is the immutable exact script loaded for the recorded build,
SHA-256 `a14f1205c57ac4d475c38e3d73179fc1645eaf1d5bc4962dad9f3c42655588a9`.
The running build had already loaded those definitions when the production
verifier added an ambient-sysroot guard and a check against this frozen snapshot.
Keeping the actual producer bytes prevents falsely attributing its measurements
to later verifier edits. The inherited `LEAN*` environment was observed empty;
the compiler's built-in search path uses `Lean.getBuildDir = IO.appDir.parent`,
and each child explicitly receives only its private `LEAN_PATH` for RMQ imports.
Future builds record the then-loaded production script's own canonical hash in
their new scratch receipt; they do not overwrite the historical candidate pin.

The admitted compiler-artifact identity is exact `.olean` equality for this
Windows compiler/library distribution, canonical LF source bytes, relative
arguments and fixed module order. The receipt timestamps, process durations and
absolute private directory names are observations, not reproducible artifact
identifiers. No promise is made that another Lean release, platform or arbitrary
compiler build yields identical artifacts. If this supported profile produces a
different `.olean`, installation rejects it; the mismatch must be investigated
instead of silently replacing a pin. POSIX compilation, owned-tree execution and
certificate replay remain unexecuted by this Windows profile.

All Lean semantics, theorem types, 39 capstone fields, 78 exact consumers, modeled
costs and payload accounting remain those of the frozen sources. These new
receipts establish reproducible compilation and replay setup; they do not turn a
modeled instruction bound into a native performance claim.

For proof digestion, the conceptual change is an explicit source-to-artifact
chain that survives ordinary checkout newline conversion. In plain English,
reviewers can start from the committed files and obtain the exact checked
compiler inputs and imports without recovering an editor's historical byte
layout. The live assumptions are the pinned Lean/Windows distribution, trusted
versioned profile/driver/receipt pins, and the existing Lean proof trust base.
The downstream consumer is the production certificate replay and its unchanged
39-field, 78-consumer rejection campaign. A skeptical graduate student's next
check is whether a real source token change, a substituted import artifact, or
an omitted dependency can get through that same production path; the repair
registry supplies those controls, and exact final replay supplies the consumer
evidence.
