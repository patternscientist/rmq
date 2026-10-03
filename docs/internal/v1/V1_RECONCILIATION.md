# V1 source and evidence reconciliation

This record separates source identity, prior verification, current verification
and coordinator acceptance. It was opened on 2026-10-01 at the implementation
base `ee44f04a561f2194b3713f071c26b6faf9ba7fab`. Current verification and the
independent release audit are discharged by `V1_COORDINATOR_ACCEPTANCE.md`
and its exact-input evidence index. The delivered instance is recorded separately
in the external delivery receipt.

## Exact source lineage

`source-closure-inventory.json` records every local imported file and Git blob,
not just the public alias, at these objects:

| Role | Commit |
| --- | --- |
| Earlier lifecycle audit target | `eb8e4f250ee13eaf378f4a42028ce32e7cf0b94a` |
| R3 repair tip | `d27ffa341f4ed8ceccc46817455eb26c73b319a1` |
| R4 integrated lane | `68163d9496559f06038d108c74bfcb0781175eda` |
| Squash merge | `5a5f8f2e239aaab48a955ec86b9adf0a3cab0a71` |
| V1 implementation base | `ee44f04a561f2194b3713f071c26b6faf9ba7fab` |

The closure rooted at `RMQ.Headlines.Lifecycle`,
`RMQ.Validation.LifecycleContract`, `RMQ.Core.WordRAM.Lifecycle.Provenance`
and `RMQ.Validation.PackedLifecycle` contains 368 local Lean modules. Their
blobs and the toolchain pin agree across all five objects. The only external
import root is the pinned toolchain's `Std`. Thus the source-level propositions
and proof bodies reviewed in that lane reach the V1 base unchanged. This does
not certify a different executable, an altered harness or the subsequent V1
proof-maintenance delta.

The separate `lifecycle-blobs.json` inventory covers 116 formal, native and
script paths. All 116 match between R4, the squash and the V1 base. Relative
to the earlier audit and R3, its sole changed path is
`scripts/lifecycle_validator.ps1`. The R4 validator results must therefore be
used for that path. This 116-path inventory is not asserted to be the complete
native compiler/tool/runtime dependency closure: native build receipts supply
those additional identities.

The paper closure contains 262 local modules. The three differences between
its deliberate `3849ecbb53bbedfcd679352cc68d095fa5a304c2` pin and the V1 base
are enumerated in `paper/V1_SOURCE_RELATION.md`: five `macro_inline` attributes
in two files and one source-comment correction. The candidate's later proof
cleanup is an additional reviewed delta, not part of that historical equality.

## Formal lifecycle and native supplement

The formal lifecycle result has a seven-field public contract and an independent
expected-type client. Construction, its returned owner, first service and later
requests concern one continuous modeled execution. The comparison-key and
signed-word input models have distinct live assumptions; input materialization
precedes the execution. Complete retained numeric bits are distinct from peak
arena cells. The public claims packet specifies these objects and units.

The V1 aggregate gate adds the existing independent lifecycle client, controls,
provenance module, provenance expected-type script and lifecycle axiom inventory.
This closes a default-gate coverage gap. It does not add native PowerShell
campaigns to that gate or turn a source theorem into compiler correctness.

The native interface remains an executable supplement. Its full historical
campaigns and tool identities are evidence at their recorded inputs. Any V1
rebuild/replay must identify its own source and tools; success on an earlier
branch is never reported as a newly executed V1 result. Compiler, foreign
ownership, allocation and runtime assumptions remain explicit even after
successful finite controls.

## Four inherited follow-ups

The frozen V1 evidence-hardening contract and its recorded checks live in
`V1_EVIDENCE_MATRIX.md`. Each follow-up has an actual consumer:

| Follow-up | Property required for V1 | Current implementation obligation |
| --- | --- | --- |
| Label-trusting pin coverage | Exact independently specified pin paths and valid SHA-256 values; missing pins and coordinated count changes rejected. | EH1: repair the current R4 predicate/registry and exercise controls. |
| Entry values under unqualified pin keys | Distinguish entry snapshots from values verified in finalization; reject a mid-run mutation while restoring the fixture. | EH2: repair dependency controls and their labels/consumers. |
| Registry or component reads before durable evidence | Once execution has accepted valid arguments/selectors, a missing or drifted required input leaves an owned failure record. | EH3: cover these paths with a current versioned adapter if immutable historical guards prevent an in-place repair. |
| Old evidence-reader schema and pins | State exactly which historical collectors accept which old keys, references, executables and evidence roots. | EH4: document their bounded historical use; do not make a key rename stand in for a fresh verifier. |

An old `INCOMPLETE` or `Open` label is not rewritten. R4's report explicitly
reserves integration, audit, CI and acceptance to the coordinator; its appended
evidence contains actual completed campaigns. V1 dispositions are recorded
separately after inspecting that evidence and the current implementation.

## Evidence boundaries

The R4 recorded campaigns include 67/67 PowerShell 7 and 66/66 Windows
PowerShell registry cases, validator startup/single/full modes on both shells,
and native-p0 integrity, dependency and stream controls on both shells. Those
are dated records, with receipt indexes and finalization pins under
`extensions/lifecycle1/repair-r4/receipts`; they are not fresh candidate results.
The source comparison supports transfer only for identical dependencies and
the same proposition being checked. Changed current harness properties receive
their own discriminating controls and exact identities.

The release candidate is accepted only after the integrated checks and fresh
audit discharge the frozen V1 rows. Agreement between Codex and Claude, a
successful merge, or an unqualified count of green receipts is insufficient.
