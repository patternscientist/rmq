# Actual selector and stream controls

Run `native_selector_controls.ps1` from this directory with PowerShell on the
certified Windows host. It uses the real `scripts/lifecycle_native_replay.ps1
-Phase Validate` caller boundary and the existing raw capture / owned-process
helpers. It acquires no heavy-build mutex and executes no native RMQ or Lean
program. The 30-second per-caller bound follows the earlier selector controls;
the new ordinary byte callers took about 1.7–2.0 seconds in this run.

The current registry preserves the preceding twenty-four controls and adds
nine actual caller holdouts. Its frozen SHA-256 is
`fb9d38afd5ca8b8ff1313c355e7c649cb6e3e44777eef9a1915b818585ef67b5`.
The current checked result is
`.lake/lifecycle-native1/selector-controls/20260927T063333385-e85600e9/RESULT.json`:
outer ordinary exit zero, all thirty-three ordered controls passed, ten pinned
source/tool files unchanged, and disposable source copies removed. The result
contains each actual capture, ordinary exit where present, raw-file hash,
caller script, exact expected stream, and production rejection message.

The new cases reject the known fixture ID followed by NUL, soft hyphen,
zero-width space or BOM. Four analogous malformed ControlName values reject
before the build-receipt boundary; exact `none` reaches that boundary as expected.
Ordinal hash-set membership replaces PowerShell's cultural comparison for
ControlName. A development emitter encoded soft hyphen as ASCII hyphen through
Windows best-fit console output; explicitly setting strict UTF-8 in those caller
fixtures corrected the diagnostic transport. The production error predicate and
all preceding twenty-four controls stayed unchanged. This complete run took
169.15 seconds and retained 264 raw capture pins plus 33 caller pins.

The preceding twenty-four-case result at
`.lake/lifecycle-native1/selector-controls/20260927T044728822-6fc9e7e4/RESULT.json`
is historical after the production selector guard changed. The earlier result at
`.lake/lifecycle-native1/selector-controls/20260923T090347015-0deb35d1/RESULT.json`
remains historical development evidence; the ordinary caller timing range above
comes from that earlier run.

| Boundary | Actual controls and interpretation |
| --- | --- |
| N1-21 selector binding | Omission selects the complete thirteen-ID registry; a known selector selects one. Explicit null, empty array/string, whitespace, unknown and duplicate selectors reject through the real script parameter boundary. |
| N1-21 frozen roster | An intact isolated copy accepts. Omitted, duplicated and reordered middle IDs in disposable registry copies fail the real frozen-byte hash check. These cases do not claim to reach the later structural classifier. |
| N1-20 exact streams | Exact CRLF bytes accept. Extra LF/text/stderr and a real ordinary exit seven reject. BOM prefix (`EF BB BF`), NUL suffix (`00`) and changing the expected CRLF to LF reject by ordinal stream equality. A raw `FF` suffix rejects through `Read-LNExactStream`'s strict UTF-8 decoder. |
| N1-20 output overflow | An actual caller first validates the known ID, then writes seventeen MiB of raw bytes. The unchanged sixteen-MiB capture limit rejects: 17,825,842 stdout bytes captured, overflow marker present, launcher ordinary exit 125, production predicate reports incomplete bounded capture. The producer exit receipt was absent and remains null; the harness does not invent an exit zero. This is a transport failure, not semantic success. |
| Wrapper numeric binding | `CaseDeadlineSeconds=2147483647` accepts validation; `2147483648` is rejected by the actual Int32 parameter binder, with its exact exception text captured. This is not native numeric-codec coverage. |

No stream acceptance uses the inherited returned-line helper output. The
CRLF-to-LF hostile caller deliberately changes a real returned line; the
unchanged acceptance predicate still compares its physical captured bytes
against the original CRLF expectation. The raw child and all three production
stream predicates are pinned in the result, including their source files.

Frozen N1-21 concerns selection. The strict UTF-8, ordinary-exit and output-limit
requirements are N1-20; host count/endpoint/codec overflow is N1-03/N1-15. Native
overflow remains dependent on an actual compiled C/Rust client invocation and
is not closed by this harness, a JSON hash mismatch, or Int32 deadline binding.
For example, the C testing client's decimal `--argument` parser can be challenged
with `18446744073709551616` on Windows x64 before runtime acquisition. Endpoint
overflow must additionally reach the real profile/endpoint parser. Those native
cases have not been executed here and require their own pinned capture and
expected-verdict evidence. Timeout/descendant, forced partial-setup failures and
broader native acceptance rows also remain separate from this bounded result.
