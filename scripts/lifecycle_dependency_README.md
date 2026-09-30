# LIFE-1 public dependency replay

Run from the repository root with PowerShell 7 after the final named Lean targets
have built. The script never builds missing prerequisites or writes original
source/artifacts. It serializes compiler work with
`Local\RMQLifecycleImplementationHeavy20260920`.

```powershell
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -SelfTestOnly
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -StartupOnly
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1 -OnlyCase D01_CONSTRUCTION
pwsh -NoProfile -File scripts/lifecycle_dependency_replay.ps1
```

`-SelectorProbeOnly` checks selection without starting a compiler. Exactly one
case may be selected. `LIFE1_DEPENDENCY_SELECTOR=id:D01_CONSTRUCTION` is the
equivalent environment channel; simultaneous channels, `id:`, whitespace,
unknown IDs and malformed selectors fail. No selector means the complete,
nonempty ordered registry. Registry order, IDs, producer/client mapping and
normalized UTF-8 hash are checked independently in the runner.

The 120-second deadline applies to each owned Lean process. This has margin over
the measured warm core-client checks (approximately 10–30 seconds); the runner
requires existing dependency artifacts and never substitutes a cold Lake build.
One complete private RMQ import package is copied per invocation because Lean
resolves imports by root package. Before and after each case, the private
Capstone and Provenance bindings are restored from checked original artifacts.
Every case writes a modified copy of the actual producer source and compiles its
fresh `.olean`; its unchanged direct client imports that artifact. No downstream
artifact checked against an incompatible producer is imported.

The producer must compile with exit zero and no diagnostics. A negative client
must return exit one with empty stderr and exactly the registered diagnostics.
Lean `--json` is required: every stdout line must be a diagnostic JSON object,
with the prescribed error class and location inside the named client declaration.
Extra errors, warnings, unlocated exceptions, panic output and malformed output
fail. Positive clients must compile cleanly. Complete returned stdout, stderr
and process receipts are persisted before verdict classification.

| Cases | Accepted proposition P and challenged conclusion Q |
| --- | --- |
| D01–D07 | Each of the seven public fields is replaced by `True`; its constructor is adjusted. All other fields stay present. |
| D02 additionally | The valid/invalid corollaries dependent on the removed retained field are explicitly weakened; all three clients must reject. Producer errors are never accepted as evidence. |
| D08 | The physical field and its initializer are deleted. |
| D09 | The physical field is replaced by the sibling executed-owner proposition on the same objects. The producer supplies its existing owner proof; the physical client must reject. |
| D10–D12 | The general public theorem and/or each input-form wrapper concludes `True`, preserving the input guards. |
| D13 | The record still refers to `PhysicalRun`, but that producer alias becomes `True`. The client spells out its expected physical facts independently. |
| D14 | The actual step bound is weakened from construction budget + 160253 to + 160254. The producer checks the P-to-Q implication with `Nat.le_trans`. |
| D15 | Physical reads and prefix bounds remain; the fetched-code-word clause is removed. |
| D16 | Prefix resource conclusions are reduced to `Fits`; the producer explicitly projects the retained first conjunct. |
| D17 | Executed-owner readiness drops its finite array bank size; the canonical state conjunct remains. |
| D18 | Supplied-store determinism retains its full guarded premise but concludes `True`. |
| D19–D20 | Expected acceptance for a comment-only producer change and unchanged core source. |
| P01–P04 | Each actual production receipt group becomes `True` while its proof group is adjusted; the independent receipt client must reject. |
| P05 | The public provenance theorem retains its actual capstone premise but concludes `True`. |
| P06 | Expected acceptance for unchanged provenance source. |

The clients freeze retained-state data, finite bank, readiness, prefix resource
bounds, instruction-code backing, scalar receipt guards and complete object
arguments. They pin the numeric bank, control count, code budget, setup cost,
service budget, reusable query budget and construction budget formula.

Evidence is written under `.lake/lifecycle-dependency/<unique-run>/`. Original
load-bearing sources and checked artifacts are hashed before and after replay;
each case records changed source, fresh artifact and unchanged client hashes.
The private tree is removed only after its resolved path is checked inside that
run's evidence directory. Cleanup and restoration failures prevent the terminal
success marker. Concurrent unrelated documentation edits are outside this
scoped byte-restoration check; the coordinator's final source manifest and Git
checks bind the complete candidate tree.

The self-test executes the production registry/selector/diagnostic checkers and
an owned six-second process timeout. The timeout fixture starts a hidden child,
then verifies that child is absent after the owned process tree is terminated.
This is a dependency and replay check, not a native machine or allocator proof.
