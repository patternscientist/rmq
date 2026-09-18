# OPT-1-R1 runtime repair leaf results

This note records the delegated runtime leaf. It does not declare candidate or
coordinator acceptance. The parent repair report and its frozen 39-row matrix
own the complete local contract, the production 27/80 semantic campaigns,
source-profile certification and final external audit.

Worktree: `C:/Users/poin/.codex/worktrees/ccb1/RMQ`.
Branch: `codex/opt-1-r1-replay-certification`.
Exact frozen base: `aecf4a580c591e8f694a3699e19e843198089194`.
Governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Actual runtime RMQ skill names: `rmq-audit-prompt`, `rmq-coordinator`,
`rmq-proof-sprint`; required `rmq-proof-sprint`; exact-governance preflight passed.
The canonical proof-sprint skill, completion gate and relevant failure-mode
guidance were read before implementation. The parent froze the new acceptance
matrix before edits. The runtime mixed-diagnostic reproduction and the parent's
independent provenance reproduction both preceded the production repair.

`scripts/packed_optimized_runtime.ps1` changes only `Assert-OPT1Rejected`, its
controlled `RegistrySelfTestOnly` result's stream fields, and the explicit
`LEAN_SYSROOT` environment in `Invoke-OPT1Lean`. The exact grammar and P/Q
comparison are in `README.md`. The 27 runtime IDs and their mappings are
unchanged. No Lean module, validator, proof definition, typed consumer,
allocation, cost constant, axiom inventory or original evidence file was edited
by this leaf. No local commits, pushes or shared-cache mutations were made by
this leaf.

The frozen production function was first extracted uniquely from its actual
pre-edit AST and applied to three real owned children with 60-second deadlines
and 1 MiB output ceilings. `frozen-reproduction/RESULT.json` records the intended
exception accepted, the mixed expected stdout/unrelated stderr wrongly accepted,
and unrelated-only output rejected. A fresh replay of the actual raw Git blob
through bounded `git archive` and `reproduce-frozen.ps1` also passed; its separate
receipt is `evidence/frozen-raw-reproduction.json`. These prove the historical
classifier defect, not mixed failures in the original Lean campaign.

The final command was:

```powershell
& ./docs/internal/extensions/opt1/repair-r1/runtime/run-bounded.ps1 -ArtifactDirectory .lake/opt1-r1-runtime/final53
```

It passed all 53 exact expected/executed IDs in 237.647 seconds, exit 0, no
stderr, no outer timeout or overflow, within the 600-second/1 MiB owned wrapper.
The measured predecessor had completed 33 cases in a total of 149.680 child
seconds, including two intentional 30-second timeouts, before the documented
overflow-fixture failure below. The final registry contains:

| Kind | Cases | Boundary checked |
| --- | ---: | --- |
| Classifier | 31 | Three permitted exception controls and unrelated-output, padding, duplicate, wrong-surface, exit, success and resource holdouts |
| Timeout | 2 | Actual descendant creation and death, with and without emitted expected diagnostic |
| Overflow | 2 | Actual output ceiling, with and without separately witnessed flushed expected diagnostic |
| Script boundary | 12 | Real omitted, valid, empty, whitespace, padded, malformed, unknown, zero, duplicate, contradictory and selector/startup modes; actual registry selftest |
| Registry | 6 | Actual production literals/Markdown/source controls, including missing and duplicate middle IDs |

All 47 actual process cases restored their original binary scratch bytes in
`finally`, with identical SHA-256. No tracked source was mutated by the
campaign. The production script, owned helper, validator, inherited registry,
new registry and actual runner have equal hashes before and after. The two
timeout controls recorded root/child PID pairs `24008/23944` and `18324/25204`;
all four were absent immediately after their Windows owned-job barriers.
POSIX execution is unexecuted. Intentional timeout/overflow flags are successful
negative controls, distinct from the outer wrapper's bounded successful result.

Receipts:

| Artifact | SHA-256 |
| --- | --- |
| `evidence/final-runtime-repair.json` | `d53853e373dfd04500bc4f1842c3aefeb92adadbaf74fa4161d648a4406594ad` |
| `evidence/final-runtime-wrapper.json` | `ebe14ae1ca6979d897b90cb1ec3c47ed51f2f89f2a4f0011696b5626bca77f8c` |
| Checked production runtime script | `69494710c3aaa873fdc3f915ba0dd67cfa449f40e2a9890dca126f9eade0f347` |
| Checked `runtime/replay.ps1` | `1d63d9b3327ed408e2ea2e1733741b232488f120da566ffd57dcfc4e5222f2c6` |
| Exact 53-case `REGISTRY.json` | `35dee68d8efbb972fb35276bc03b1ec18071048d83e0bfac0334daa9364ade4d` |

The 53-case final receipt includes all actual stream/exit results that the
shared bounded helper returns, production-function verdicts, exact boundary
diagnostics, source identities, emitted-diagnostic witnesses and restoration.
The wrapper receipt includes the complete 53-case marker sequence and final
summary. Raw over-ceiling streams are deliberately discarded by the existing
shared helper; they are not claimed to be fully retained. The classifier sees
the unchanged helper result and rejects the overflow flag before diagnostics.

One development campaign stopped after 33 completed cases because its overflow
fixture incorrectly required the expected line in retained stdout, despite the
shared helper's deliberate overflow discard. No overflow semantic rejection was
credited in that run. The separate actual failed case and its explanation are
`evidence/development-overflow-failure.json`; the completed predecessor cases
remain in `evidence/development-full-1.json`. The fixture was changed to require
a post-flush child witness and the untouched real helper result. Focused
overflow, omitted selector, duplicate-parameter and registry-selftest controls
passed before the final full run. An earlier skill-preflight attempt also used
an array for a scalar parameter and failed binding; corrected comma-delimited
runtime arguments passed the exact-governance check, without substituting roles.

The scoped mathematical meaning is preservation: this leaf changes what host
evidence is accepted for an expected Lean user exception. The execution theorem
and query model are untouched. In plain English, one known failure message can
no longer hide another failure or a success receipt. The live assumptions are
the shared owned-process result representation, the caller's fixed expected
surface, and the unchanged Lean/runtime contracts verified by the parent. The
next consumer is the parent's real 27-case production runtime replay, including
its four genuine corrupt-compiler user exceptions and exact source/profile
checks. A skeptical reader should compare those real outputs to the singleton
grammar and verify that profile identities bind the executable distribution;
the parent owns those checks. The proposed scoped WDD records why the earlier
certificate diagnostic rule had not reached runtime, and the proposed DD records
the new explicit registry/AST/replay artifact design without changing the model.

No Lean build or broad aggregate was launched by this leaf: its owned change is
host verification logic, and the parent owns the required final Lean, hygiene,
design, claim and coordinator certification commands. Scoped whitespace review
passed after the implementation; the parent performs final report-sensitive and
committed-range checks after its final edits and commit.
