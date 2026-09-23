# BV-1 retained leaf consumers

Status: CANDIDATE_COMPLETE for persistence and fresh replay; exact8/8 consumers
passed at their retained paths. This is an evidence-preservation repair authorized by
the coordinator after the prefinal composition review. It changes no production
Lean module, existing consumer, frozen requirement, or prior result record.

The inherited governance is `0e6a00f654abc64f8b68988fa9675b9a839dca2f` and the
source checkpoint is `645a0502b9da9ad6444edbe44759e1c2c5661f25`. The canonical
proof-sprint preflight/completion rules remain applicable. Other workers are
active; this worker owns only the new `controls/leaf_consumers/` directory,
this document and the separately authorized prefinal review.

## Exact registry and byte provenance

The nonempty version1 replay list is
`controls/leaf_consumers/replay-list-v1.json`. Its exact eight-case order is:
regular-layout-types, regular-layout-axioms, select-semantics, rank-semantics,
rank-layout, generic-select-safety, canonical-select-safety, scratch-frame.

Each old path begins `C:\Users\poin\AppData\Local\Temp\`; each new path begins
`docs/internal/extensions/bv1/controls/leaf_consumers/`. The filename is unchanged.
The copy used raw file copying with no encoding or newline conversion, and
SHA256 of the current old and new files matched. The manifest records absolute
old path, relative new path, bytes, SHA256, prior command arguments, prior
successful exit, prior record path/hash, and document-text comparison.

| Case | Filename | Bytes | SHA256 | Prior successful command record |
| --- | --- | --- | --- | --- |
| regular-layout-types | bv1-regular-layout-exact-types.lean | 3415 | F59CCBB23FD0074B8E769D98DC16ED263C16A7DBC3939E6F76FF20CC1586E337 | regular-layout-axioms.json |
| regular-layout-axioms | bv1-regular-layout-axiom-source.lean | 363 | 67012CCC16E31764979ADED20BA08C462E1CC207DA389839737219CD98E7627D | regular-layout-axiom-source.json |
| select-semantics | bv1-select-semantics-consumer.lean | 2874 | 35A9FEB285AA5CD883F9AB0FBECC693EE7DE9271242EB63E8F45EA07B27026A0 | select-semantics-consumer.json |
| rank-semantics | bv1-rank-semantics-consumer.lean | 3117 | 2F4D7A5B4FF532C80CCD162519C8A989F5B78B44B249CD9A159F122E7EEEA2C0 | rank-semantics-consumer-2.json |
| rank-layout | bv1-rank-layout-consumer.lean | 2044 | 283CE0B7E52E49F63108BBDBCBB66E916C6086C0E821F49C1F6B8B5D6A071E7F | rank-layout-consumer.json |
| generic-select-safety | bv1-generic-select-safety-consumer.lean | 4382 | 297C96DB48830938A8236C5D02CDA3DE35E87AFD4CCD75E17785814B5F53D8B7 | generic-select-safety-consumer-1.json |
| canonical-select-safety | bv1-canonical-select-safety-consumer.lean | 3741 | 6EB1741EC157B37904DCE556CDBC16BA9730DFD28269217C16FEEA0EE9B44C50 | canonical-select-safety-consumer-2.json |
| scratch-frame | bv1-scratch-frame-consumer.lean | 1684 | C40D8F1B3D776C84E2594FFC6605E51AD347F9ABBA1B5A83E1788CB214AC6712 | scratch-frame-consumer-1.json |

Every prior record is under `docs/internal/extensions/bv1/commands/` and records
exit0 at the listed old temporary path. However, those runner records hashed
the production modules, not the external temporary consumer itself. Therefore
historical byte identity is **PROVENANCE_UNCERTAIN** for all eight files. The
present copy/hash equality proves preservation of the currently available
temporary files; it does not prove those bytes were unchanged since the old
successful run. No such equality is inferred from timestamps or axiom output.

For the six files after the two RegularLayout entries, the complete current
consumer text also matches the full Lean code fence retained in its leaf
document, ignoring only line endings and surrounding whitespace. The two
RegularLayout files have successful path/output records but no matching complete
consumer fence. This distinction is recorded per case. All eight still require
a new direct check at their persisted paths, which will provide unambiguous
current evidence and supersede dependence on the temporary location.

The six existing current external consumers already retained in the worktree
are `access_expected_type.lean`, `canonical_rank_access_safety_expected_type.lean`,
`charged_setup_expected_type.lean`, `controls/controller_axioms.lean`,
`controls/allocation_reader_expected_type.lean`, and
`controls/public_expected_type.lean`. The older Normalization and AllocationFacts
consumers are also retained as `scripts/packed_bitvector_normalization_consumers.lean`
and `scripts/packed_bitvector_allocation_consumers.lean`; their historical
temporary command paths do not imply a missing current file.

## Prepared replay

Do not run this while another Lean/Lake process owns the build tree. After an
explicit coordinator slot grant, the exact replay list can be consumed serially
using the existing bounded command runner. No new semantic fixture selector or
mutation runner is introduced by this proof-import list.

```powershell
$leafManifest = Get-Content -Raw docs/internal/extensions/bv1/controls/leaf_consumers/replay-list-v1.json | ConvertFrom-Json
$leafExpected = @('regular-layout-types','regular-layout-axioms','select-semantics','rank-semantics','rank-layout','generic-select-safety','canonical-select-safety','scratch-frame')
if ($leafManifest.version -ne 1 -or $leafManifest.expectedCount -ne 8 -or
    ($leafManifest.registry -join '|') -cne ($leafExpected -join '|') -or
    ($leafManifest.cases.id -join '|') -cne ($leafExpected -join '|')) {
  throw 'Leaf consumer replay registry mismatch'
}
$leafTag = 'leaf-replay-' + [DateTime]::UtcNow.ToString('yyyyMMddHHmmssfff')
$leafPassed = 0
foreach ($leafCase in $leafManifest.cases) {
  if ((Get-FileHash -LiteralPath $leafCase.path -Algorithm SHA256).Hash -cne $leafCase.sha256) {
    throw ('Consumer hash mismatch: ' + $leafCase.id)
  }
  & docs/internal/extensions/bv1/run_command.ps1 -Stage ($leafTag + '-' + $leafCase.id) `
    -Executable $leafManifest.commandExecutable `
    -CommandArguments @('env','lean',$leafCase.path) -DeadlineSeconds 180
  if ($LASTEXITCODE -ne 0) { throw ('Consumer check failed: ' + $leafCase.id) }
  if ((Get-FileHash -LiteralPath $leafCase.path -Algorithm SHA256).Hash -cne $leafCase.sha256) {
    throw ('Consumer changed during check: ' + $leafCase.id)
  }
  $leafPassed++
}
if ($leafPassed -ne 8) { throw 'Consumer replay omitted a case' }
Write-Output "BV1-LEAF-CONSUMERS version=1 executed=$leafPassed expected=8 passed=$leafPassed"
```

The runner uses the direct pinned v4.22.0 Lake binary, one Lean thread and one
owned bounded child at a time. A failed elaboration, timeout, output cap or
changed hash stops the replay and is not a successful consumer. The fresh
records must retain the exact new path and be associated with this manifest's
consumer hashes. No aggregate gate is needed for these unchanged proof imports;
the coordinator owns final branch certification.

## Digestion

The proof propositions and construction have not changed. This repair makes
previously transient direct consumers ordinary repository artifacts. The current
copies are byte-exact, and their historical association is reported conservatively.
At preparation the remaining step was a fresh serial replay. That replay has
now passed as recorded below. Historical byte identity remains uncertain;
current retained-file verification is direct and does not depend on that
historical inference. No coordinator acceptance or commit is recorded here.

## Fresh retained-path replay

After numeric validation released the build tree, the coordinator applied the
approved fifth byte-preserving attribute between campaigns and explicitly
granted this worker the slot. The existing `lakefile.toml` bytes stayed at
SHA256 `66F2730CC65D0A796A6595D230B18C0554826DFEE9407799F64D0F744D3D823A`.
No concurrent Lean owner remained. The exact eight consumers then ran serially,
using the existing bounded runner, direct pinned v4.22.0 Lake, one Lean thread,
and180 seconds per child.

The decisive record is
[leaf-replay-20260912130101742-summary.json](commands/leaf-replay-20260912130101742-summary.json),
SHA256 `E1A6FCF86B0F856DC1ABB486836A13E42CA31240FE458248230F6D81402C2C30`.
It records version1, exact expected/executed count8, all cases passed, the new
repository paths, each consumer SHA256 before/after, and unchanged manifest
SHA256 `FCA3D67AD0B3B13AE65416431F73A209FBE8CECDE1C08E790FA7DADB2DFBEDEC`.
The replay began2026-09-12T13:01:01.7609591Z and ended13:02:17.0874936Z,
75.327 seconds wall time including runner setup. All child records are named
`commands/leaf-replay-20260912130101742-<case-id>.json`.

| Exact case ID | Exit | Child seconds | Typed assertions | Axiom reports |
| --- | --- | --- | --- | --- |
| regular-layout-types | 0 | 12.155 | 8 | 14 |
| regular-layout-axioms | 0 | 7.822 | 0 | 6 |
| select-semantics | 0 | 9.289 | 7 | 8 |
| rank-semantics | 0 | 7.193 | 7 | 5 |
| rank-layout | 0 | 7.712 | 7 | 12 |
| generic-select-safety | 0 | 9.175 | 8 | 8 |
| canonical-select-safety | 0 | 8.537 | 8 | 9 |
| scratch-frame | 0 | 5.196 | 7 | 6 |
| Total | all0 | 67.079 child seconds | 52 | 68 |

There were no Lean warnings, errors, timeouts or output-cap failures. The full
child outputs, including multiline axiom lists, were inspected: the union of
dependencies is exactly `propext`, `Classical.choice`, `Quot.sound`; two negative
constant-answer controls require no axioms. All eight current consumer files
remained byte-identical to the prepared manifest. The scoped forbidden-trust
and native-reduction scan of these Lean files returned no matches.

The manifest remains an immutable preparation record. Its per-case
`freshReplay` strings describe the earlier pending state and are superseded by
this fresh summary; they were not rewritten to invent a historical success.
The successful child arguments now name the retained repository files, so
reproducibility no longer relies on a temporary directory or on prose-only
consumer text. The six original full-text document matches remain additional
provenance, not substitutes for the fresh checks.

The slot was explicitly released to root and generic_controller immediately
after the final child and outer session exited. Documentation finalization was
offline. No aggregate, production source edit, shared-file overwrite or commit
was performed by this replay.
