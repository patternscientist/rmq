# BV-1 replay entry points

Use Windows PowerShell 7, the pinned Lean 4.22.0 toolchain and one Lean/Lake
process at a time in the build tree. These scripts retain fresh timestamped
records rather than overwrite the committed evidence. An aggregate run also
requires the coordinator's host-wide slot; the commands below do not grant one.

## Prepare a fresh checkout

First verify the committed bytes with the procedure in
[CHECKOUT_BYTES.md](CHECKOUT_BYTES.md). A fresh checkout has no local compiled
imports: `lake env lean` does not build missing import artifacts automatically.
Build `RMQ.Core.WordRAM.Bitvector.Capstone` with the existing
[bounded command runner](run_command.ps1) before the proof consumers or runtime
scripts. Its dependency closure contains Source and CompleteReader, the actual
imports of every runtime fixture below. Use a new Stage and an observed
cold-build deadline with margin; preserve and inspect any timeout rather than
repeat an unchanged expensive command. The candidate's recorded capstone
check is a warm-import measurement, not a measured fresh cold build.

The independent public proof consumer is
[controls/public_expected_type.lean](controls/public_expected_type.lean).
Run it through the same bounded runner with Lake arguments
`env lean docs/internal/extensions/bv1/controls/public_expected_type.lean`.
The additional exact eight-file proof replay, including its hash and axiom
checks, is specified in [LEAF_CONSUMER_REPLAY.md](LEAF_CONSUMER_REPLAY.md).

## Runtime and mutation campaigns

From the repository root, use the production commands below serially. Each
wrapper owns bounded children. Startup and a known case are separate checks;
the selector campaign's omitted case performs the one complete registry.
Its remaining selectors must not silently select zero cases.

```powershell
pwsh -NoProfile -File scripts/packed_bitvector_probe.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_probe.ps1 -Case mixed-true
pwsh -NoProfile -File scripts/packed_bitvector_selector_controls.ps1 -Runner Main

pwsh -NoProfile -File scripts/packed_bitvector_validation_controls.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_validation_controls.ps1 -Case baseline
pwsh -NoProfile -File scripts/packed_bitvector_selector_controls.ps1 -Runner ValidationControls

pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -Case access-raw-cell
pwsh -NoProfile -File scripts/packed_bitvector_machine_controls.ps1 -ReplaySelectors

pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -Case long-super-false
pwsh -NoProfile -File scripts/packed_bitvector_exceptions.ps1 -ReplaySelectors

pwsh -NoProfile -File scripts/packed_bitvector_public_controls.ps1 -Prepare
pwsh -NoProfile -File scripts/packed_bitvector_public_controls.ps1 -Startup
pwsh -NoProfile -File scripts/packed_bitvector_public_controls.ps1 -Case weaken-accessCorrect
pwsh -NoProfile -File scripts/packed_bitvector_public_controls.ps1 -ReplaySelectors
```

The main registry has 46 cases: 43 actual primitive runs and three explicit
guarded-API cases. The validation mutation registry has five cases and 17 exact
verdict pins. Machine controls have 12 cases. The exception selector replay
also performs its wrong-route expected-reject and two expected-accept controls,
for 11 outer controls covering all four parameterized routes. The public
campaign has 32 cases, with successful constructors required before exact
semantic consumer rejection. It uses the same local reducibility boundary
for every fixture; the independent consumer body and public producer bytes
remain pinned. A resource failure is never a semantic rejection.

The three focused reader crossings can be replayed through run_command.ps1
with Lake arguments `env lean --run scripts/packed_bitvector_crossing.lean`.
The observed final-allocation run took 141.010 seconds under a 300-second bound.
These complement the main registry's four whole-operation crossing witnesses.

Exact registries, expected verdicts, immutable fixtures, scope limitations and
record links are in [VALIDATION_CONTROLS.md](VALIDATION_CONTROLS.md),
[MACHINE_CONTROLS.md](MACHINE_CONTROLS.md),
[EXCEPTION_CONTROLS.md](EXCEPTION_CONTROLS.md) and
[PUBLIC_MUTATION_CONTROLS.md](PUBLIC_MUTATION_CONTROLS.md).
Historical failed generations are retained as diagnostics; the current public
registry pointer selects the corrected generation. Do not treat an old failed
receipt, a missing case or an unexecuted host branch as passing evidence.

## Final certification

Only after the complete candidate is committed and the coordinator grants its
slot, use [run_final_gate.ps1](run_final_gate.ps1) with that exact commit, the
retained grant and the scheduled deadline. It invokes the unchanged aggregate,
whose first build stage is the required `lake build`. It does not perform a second
standalone build or automatically retry a failed aggregate. The wrapper records
grant bytes, ownership, exact before/after HEAD and clean state, matrix identity
and complete output. Pending byte/gate work is identified in REPORT.md; this
reproduction guide is not evidence that an unfinished campaign passed.
