# OPT-1-R1 production runtime rejection controls

These controls test the production PowerShell runtime replay boundary. They do
not execute Lean query semantics and do not replace the inherited 27-case Lean
runtime campaign or the 80-case certificate campaign.

The repaired function is `Assert-OPT1Rejected` in
`scripts/packed_optimized_runtime.ps1`. Its downstream calls are the four
inherited corrupt-compiler cases and five Lean selector rejection controls.
Those calls still supply their original exact expected surface. The inherited
27-case registry, validator, compiler, theorem statements and constants are
unchanged.

For a fixed caller-supplied surface `s`, predicate P accepts an owned bounded
process result exactly when it did not time out or exceed its output ceiling,
its exit is 1, and concatenating its retained stdout and stderr lines yields
the singleton `["uncaught exception: " + s]`, using case-sensitive exact string
equality. The owned process reader discards genuinely empty lines when splitting
CRLF or LF transport; that existing representation is the domain of P. Empty
transport separators can surround the one diagnostic. Whitespace-only lines,
leading/trailing spaces, embedded extra content, duplicate diagnostics and any
other retained output are outside the grammar. Either stream may contain the
sole diagnostic. With no diagnostic, even blank-only output rejects.

The pre-repair predicate Q searched combined output for one trimmed matching
line, excluded two success prefixes and a finite error blacklist, and admitted
unrelated uncaught exceptions. P rejects the whole unrelated-output category
through the singleton condition. The registry includes category holdouts whose
wording is unrelated to the coordinator's original fixture, as well as success
and resource failures. Timeout and overflow controls each run both with and
without the intended line. A setup failure cannot stand in for either condition.

`REGISTRY.json` freezes 53 exact cases under `opt1-r1-runtime-v1`. The runner pins
its independent ordered IDs, count and SHA-256; the local attributes preserve
only that enumerated new registry's bytes. Missing or duplicate middle cases,
reordering, changed expected results and changed case definitions fail before
execution. Focused selection must execute exactly one named case. Omission
selects all 53; explicit empty, whitespace, padded, malformed and unknown values
fail. `-SelectorProbeOnly` reports selection without launching semantic work.

```powershell
& ./docs/internal/extensions/opt1/repair-r1/runtime/replay.ps1 -SelectorProbeOnly
& ./docs/internal/extensions/opt1/repair-r1/runtime/replay.ps1 -OnlyCase R1RT-ACCEPT-STDOUT
& ./docs/internal/extensions/opt1/repair-r1/runtime/replay.ps1
```

An optional `-RepoRoot` selects the candidate checkout whose actual functions
and runtime entry point are tested. `-ArtifactDirectory` must name a fresh
private output directory. The default is a unique directory below
`.lake/opt1-r1-runtime`. `RESULT.json` reports exact expected/executed IDs, actual
child results with exit/stdout/stderr and resource flags, production/source/
registry/runner hashes before and after, and all per-case outcomes. Each child
has a 60-second positive deadline and a 1 MiB output ceiling, except intentional
timeouts (30 seconds) and overflows (32 KiB ceiling). Every child changes its
own scratch fixture; `finally` restores its original binary bytes and checks
SHA-256. The timeout cases create an actual sleeping child and verify both its
PID and the root PID are absent after the Windows owned-job barrier. A missing
PID file is inconclusive/failure. POSIX execution is unexecuted on this host.

On overflow, the unchanged shared owned-process helper deliberately discards
both retained streams and returns its output-ceiling marker. The overflow cases
therefore also require a child-written witness after the expected diagnostic
was emitted and flushed (or a witness that no such diagnostic was emitted),
before the output flood. The production classifier receives the untouched
helper result and rejects on `OutputLimitExceeded`. Over-ceiling output is not
claimed to be fully retained. The initial development run requiring a retained
expected line on overflow failed, and its receipt is preserved; that failed
condition was corrected to match the shared helper's documented representation.

`Invoke-OPT1Lean` now sets `LEAN_SYSROOT` explicitly to the parent of the chosen
Lean executable's `bin` directory alongside its explicit local `LEAN_PATH`.
An inherited sysroot cannot silently select a different builtin distribution.
The source/build profile evidence for that distribution is owned by the parent
repair lane; these host-only controls do not claim a toolchain build check.

Production functions are obtained by unique PowerShell AST extents from the
candidate file, with the same actual registry initializers. There is no copied
classifier. Registry corruption passes mutated in-memory arguments to the real
production registry functions without touching tracked source. Selector and
contradictory-mode cases invoke the actual production script through a real
owned PowerShell child, check exact stream output and exit, and verify its
inherited selector environment is restored. The `RegistrySelfTestOnly` entry is
also executed; its existing controlled result now includes both stream fields.

`frozen-reproduction/RESULT.json` is the initial pre-edit measurement at exact
base `aecf4a580c591e8f694a3699e19e843198089194`. It records the sole expected case
accepted, mixed expected stdout/unrelated stderr wrongly accepted, and unrelated
only rejected. It proves a classifier defect, not that the original four Lean
negatives had mixed failures. To reproduce that historical behavior after the
repair, run `reproduce-frozen.ps1`: it extracts the actual frozen production
script's Git blob into a new private directory with bounded `git archive`, then
uses its unique AST extents and real children. Historical receipts are never
overwritten or treated as fresh repaired measurements.
