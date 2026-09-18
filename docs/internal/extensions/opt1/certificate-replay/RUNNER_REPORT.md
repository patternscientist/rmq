Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.
This declaration applies solely to the assigned replay leaf. Overall OPT-1 remains INCOMPLETE pending the coordinator final phase.

# OPT-1 certificate replay runner

The complete 80-case campaign
passed on `bbbe652fa41fa40bf2530b5e2f09c4c225c0e896`; coordinator acceptance and
the separate aggregate compatibility gate remain outside this leaf.
Requirements were frozen before runner edits during continuation at
`8e355fda7788077f548865c1d6acf2ae5e88da55`.
Original OPT-1 governance remains `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Both preflights passed with `rmq-proof-sprint` required and all three actual
RMQ runtime skills. Root owns `FIELDS.json`, Certificate, Capstone and
Consumers; this leaf owns only the runner and its separate evidence.

Before implementation was frozen the coordinator expanded the contract to
39 fields (completedExecution and adequateFuel added) and then froze numeric
budget/program/encoding equalities at 151978/212964/722339. The final registry
is `opt1-certificate-replay-v3`: 78 rejects plus two accepts. The original
dispatch quotation below records its historical 37-field wording; the
coordinator's explicit v3 amendment governs the final counts and types.
The root-owned FIELDS.json bytes are pinned independently by SHA-256
`0d1529c98d35b6ff2ac53d58d107f0a47ec8f5d263f51819c085827c055a63bb`.

The coordinator's exact new requirement is:

> Prepare versioned field-deletion+weakening replay (74rejects+expected-accept controls) while no Lean slot: mutate Certificate field and matching Capstone initializer together so altered producer must compile, then fixed consumer must reject at exact field/type. Keep actual source hashes, byte restoration in finally and clean/restoration checks. Prefer isolated task-local copies+case-local olean override to avoid dirtying source during each case, but clearly report source mutation versus untouched tracked originals and restore mutated copies. Use unchanged fixed expected propositions, never derive expected type from mutant. Strict nonempty registry/selector/process ownership controls required; existing machinery reusable. Actual campaign awaits stable root sources and explicit slot, as does semantic replay.

| ID | Required evidence | Named consumer / identity chain | Status |
| --- | --- | --- | --- |
| `CERT-EXACT-REGISTRY` | Exactly 39 frozen names, 78 D/W rejects and two fixed accept controls, nonempty exact versioned registry and executed/expected equality | Independent literal names and REGISTRY.md checked against root FIELDS.json, original producer fields/initializers and fixed consumer types | PASS: exactly 80 expected/executed IDs in versioned order. |
| `CERT-PRODUCER-FIRST` | Delete or weaken one field and its matching initializer; both altered producer modules must elaborate before rejection counts | Isolated Certificate.lean -> isolated Certificate.olean -> isolated Capstone.lean -> isolated Capstone.olean -> unchanged Consumers.lean | PASS: 160 producer compilations exited 0 before 80 consumer checks. |
| `CERT-FIXED-CONSUMER` | Fixed field_expectedType and canonical consumers retain FIELDS.json propositions and actual projection proof; exact located type error for the selected field, no setup/resource failures | Unmodified Consumers bytes and same field/range, independent FIELDS.json types | PASS: 39 field-deletion and 39 field-weakening consumers exited 1 at the selected fixed theorem, with the required located error kind. |
| `CERT-ACCEPT-CONTROLS` | Both unaltered producer/consumer and comment-only change elaborate | A01-UNCHANGED, A02-COMMENT | PASS: both producer/consumer chains exited 0. |
| `CERT-RESTORATION` | Restore mutated copies byte-for-byte in finally and preserve original hashes; retain honest dirty-baseline state, without claiming tracked mutation restoration | Original source byte arrays -> case-local copy mutation -> finally byte restoration; task-local olean prefix prevents use of another case's artifacts | PASS: all 240 source-copy hashes restored and reverified; original/import/status/private-snapshot checks unchanged. Full campaign started and ended on a clean worktree. |
| `CERT-SELECTORS` | Omitted selects all 80; valid selects exactly one; explicit empty/whitespace/malformed/unknown/duplicate rejects before Lean | Actual script parameter boundary and PSBoundParameters, no native empty selection | PASS: omitted full80, focused A01/D03/W03 and nine script-boundary controls. |
| `CERT-OWNERSHIP` | Bounded stages with exits/stdout/stderr and descendant ownership, truthful unavailable-host coverage | Existing owned_process_tree.ps1 used for every subprocess | PASS on this Windows host: 243 owned stages, including 240 Lean compilations; existing deadline/descendant controls retained in runtime evidence. Other host branches remain UNCOVERED. |

No Lean process may start before explicit slot grant. `-PrepareOnly` is a
script-only copy/mutation/restoration check; it is not semantic rejection
evidence. Registry and selector self-tests likewise do not close producer or
fixed-consumer rows. Actual full replay requires stable imported sources and
completed task-local artifacts; no hidden Lake build is permitted.

Each D/W mutation is applied to isolated source files with their original
canonical module paths. Each case has a complete local `.olean` hierarchy;
Certificate and Capstone are rebuilt into private output paths there, then
the fixed Consumers copy is checked. Original tracked sources are never overwritten.
Finally restores the three case copies to the original bytes and verifies
their SHA-256 hashes. Mutant generated artifacts are case-local and are never
reused by a subsequent case. The recorded initial tracked status may already
be dirty due to concurrent authorized work; unchanged hashes mean no replay
mutation to those tracked originals, not that the whole repository is clean.

Initial deadlines were 180 seconds per producer/consumer stage and 10800
seconds for a full campaign. The nearest observed Capstone compile was about
14 seconds; the deadline includes initialization/cold-cache margin. At that
initial freeze no actual campaign runtime had been observed. On timeout diagnose ownership and
artifacts before any changed retry.

Proof digestion: this campaign tests whether each advertised public field is
load-bearing at an independently fixed proposition. Coordinated field and
initializer edits prevent a broken producer from masquerading as a consumer
test. Finite mutation results do not replace the universal theorem; the open
question was whether every selected mutated producer builds and its unchanged
consumer fails at precisely that field. The actual campaign below now answers
that finite replay question for all 80 registered cases.

## Script-only outcomes and pending semantic campaign

`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/packed_optimized_certificate_replay.ps1 -RegistrySelfTestOnly`
passed on the frozen v3 contract. The production checks reject missing,
duplicate and reordered IDs, all 78 altered field sources, and a fixed-consumer
projection substitution. Diagnostic controls also accept exact selected-field
D/W error fixtures and reject the wrong field, wrong diagnostic kind,
resource-failure text and an unexpected exit-zero result. These are checker
self-tests and are not substituted for real producer/consumer elaboration.

The same script with `-PrepareOnly` passed executed=expected=80. Every case
applied its isolated source change, preserved identical Consumers bytes,
restored all three source copies byte-for-byte in `finally`, and verified the
tracked originals' hashes and initial tracked status unchanged. The initial
tracked status was dirty due to authorized root work; no clean-tree claim is
made. [Preparation evidence](evidence/prepare80.json) includes all 80 case
records, expected verdicts, before/mutated/restored hashes, original snapshots
and before/after status. Every case explicitly has `ProducersCompiled=false`
and `ConsumerVerdict=NOT_RUN`.

`-SelectorBoundarySelfTestOnly` passed all nine real script invocations:
omitted, valid accept, valid reject, empty, whitespace, malformed, zero,
unknown and duplicate. Every invalid selector failed before any semantic
stage; valid selectors selected exactly one registered case.
[Selector subprocess evidence](evidence/selector9.json) retains exact exits,
stdout/stderr, command arguments, owned-tree mechanism and durations.

The runtime leaf's actual validator startup passed, but the coordinator then
requested an intentional shared-slot/content-freeze handoff before full
campaigns. At that historical checkpoint no certificate semantic case had run.
The planned order after explicit grant was first to
run focused A01-UNCHANGED, one D and one W to check isolated producer/import
plumbing, then run the complete 80 once on frozen content. The full campaign
uses the runtime runner's script-only artifact-freshness check and records
all imported source/artifact hashes before and after, in addition to isolated
source restoration. Stages have distinct names and preserve separate outputs.

Runner SHA-256 before the diagnostic-boundary repair:
`b7c60b3cfd7f7776dcfef769a9f2f310dc2ca4c0cc565657d8d273009c1b12b3`.
No commits, certificate-source changes, root FIELDS.json edits or coordinator
acceptance were made by this leaf.

## Mixed-diagnostic regression before semantic execution

An independent read-only review on frozen commit
`ac5af8e416f906391dc117f083a883acc053a268` exercised the actual
`Assert-CRejected` function with a located W03-widthBounds type mismatch and
an additional unlocated `error: cannot open file`. The old function accepted
that mixed result: its located-error loop did not inspect the extra line,
and the finite resource-text blacklist did not cover it. This was a synthetic
checker failure, not an observed Lean campaign result.

After the full runtime source snapshot closed, the coordinator opened a
tracked-write window. The minimal repair rejects column-zero `error:` lines
before validating the selected located diagnostic. It preserves ordinary
located D/W rejections and indented multiline details containing quoted
`error:` text. The versioned production registry self-test now exercises the
mixed diagnostic and the indented-detail accept control, in addition to its
existing ordinary reject and expected-accept controls.
The supported diagnostic categories are ordinary located Lean error headers,
unlocated top-level `error:` headers and the pinned known resource-failure
patterns. The checker makes no unrestricted claim about arbitrary prose.
[Exact before/after witness](evidence/checker-boundary.json) records the
unchanged fixture, actual verdicts from the actual production function,
selected field/range, source hashes and successful registry self-test command
and output. Before: `ACCEPTED_EXPECTED_REJECTION`; after:
`REJECTED_MIXED_DIAGNOSTIC`. The ordinary located mismatch and indented-detail
controls remain accepted as expected rejections. No Lean was launched by
these checker tests and the registry still contains 80 cases.

Repaired runner SHA-256:
`d900f70f87fddd8a0291e89552d621be02e9a27ed49828a4397c5e00b35ed8ca`.
Actual certificate execution after this repair is recorded below.

## A01 setup failure and complete isolated import hierarchy

On clean commit `15e5266888c35a38733ca14846e4ad53ed119ebe`, the real
`-OnlyCase A01-UNCHANGED` command failed before any consumer execution.
Certificate exited 1 in 5.069 seconds because Lean looked for QueryProof.olean
inside the partial case-local `RMQ` tree and did not fall through to the
second search prefix. Installed Lean 4.22.0 `Lean/Util/Path.lean` selects the
first prefix containing the package root before constructing a module path;
`Lean/Environment.lean` then rejects the missing object file.
[The actual failed A01 receipt](evidence/a01-import-root-failure.json) retains
the exact missing-object diagnostic, command, source/import snapshots and
all three restored source hashes. `ProducersCompiled=false` and
`ConsumerVerdict=NOT_RUN`; this is a setup failure, never an expected semantic
rejection. The original sources, import hashes and clean tracked status
remained unchanged after `finally`.

The repair copies the complete checked immutable closure once per campaign:
259 `.olean` files, 264,276,816 bytes (252.034 MiB). Copying the closure into
all 80 cases would require 19.690 GiB; instead the campaign keeps one private
read-only snapshot and creates complete per-case hierarchies with hardlinks
only to that private snapshot. No hardlink points to the main task cache.
Certificate, Capstone and Consumers are explicitly omitted from the snapshot.
Every producer output must be absent before compile, and must be a regular
private, writable, unlinked file afterward. Consumers is checked without an
output file. The only explicit `LEAN_PATH` entry is the complete case library;
installed Lean/Std search remains automatic. All materialized paths are
bounded under the workspace's owned campaign directory. Unsupported hardlink
creation fails closed, with no symlink or cache-write fallback.

The production artifact-freshness probe is now followed by exact provenance
binding to the committed successful runtime receipt, pinned independently at
SHA-256 `a7eb5831a88a7431607d5fe1d7189318d41978391e0a10be3ed336c014563661`
and source commit `ac5af8e416f906391dc117f083a883acc053a268`. Its import inventory
and source/artifact hashes are fixed expected values, never regenerated from
live candidate objects. Timestamps alone do not establish correspondence.
Original cache and private snapshot hashes are verified after the campaign.
Each actual case records its dependency-manifest hash, exact link count and
private producer-output hashes.

The production `-LibrarySelfTestOnly` path passed all 259 real dependency
links, three private output controls, existing-output/alias/path-escape and
changed-provenance rejection, with original and private snapshot hashes
unchanged. [Library control evidence](evidence/library-controls.json) records
the exact command, snapshot entries, all process receipts and before/after
hash/status checks. It launches no Lean and is not a producer/consumer pass.

A further synthetic mixed diagnostic exposed the ordinary compile-time
`uncaught exception:` header. The prior checker accepted an intended field
mismatch followed by `uncaught exception: failed to write output`. The repaired
production function rejects that prefix; [exact before/after evidence](evidence/uncaught-boundary.json)
records the identical stderr witness and the stdout-channel rejection control.
The registry self-test retains ordinary field rejection and expected-accept
controls, and now exercises both mixed-header failures. No actual Lean case
emitted the synthetic uncaught-exception witness. The supported diagnostic
domain remains located Lean headers, recognized unlocated headers and the
pinned resource patterns.

Current runner SHA-256:
`44536468e5df8bb8ed9e6cf88f86cfaedadceb6b55d4de71dd67531116e9b5d1`.
No field names, FIELDS.json types, 80-case order, proof sources or validator
were changed by these repairs. The repaired source was then frozen before
the actual focused and complete campaigns below.

## Complete certificate result on the repaired frozen source

The coordinator froze a clean worktree at
`bbbe652fa41fa40bf2530b5e2f09c4c225c0e896`. The actual focused A01 unchanged,
D03 widthBounds deletion and W03 widthBounds weakening all passed with exact
one-case summaries and closed source/import/status checks.
[Focused receipts](evidence/focused3.json) preserve every raw stage output,
case record, private producer hash and dependency snapshot. A01 producer and
consumer exits were 0/0/0. D03 and W03 exits were 0/0/1, with the fixed
`widthBounds_expectedType` projection at Consumers.lean:33 rejecting respectively
an absent field and `certificate.widthBounds : True` against the unchanged
quantified width proposition in FIELDS.json. Their Capstone stages took
19.359, 23.567 and 15.825 seconds respectively; no producer failure was counted
as a rejection.

The production command
`powershell -NoProfile -ExecutionPolicy Bypass -File scripts/packed_optimized_certificate_replay.ps1`
then passed `executed=80 expected=80 registry=opt1-certificate-replay-v3`,
wrapper exit 0. [Complete full80 evidence](evidence/full80.json) contains all
80 IDs in frozen order, all raw and parsed case records, all raw stdout/stderr
texts and hashes, the complete 243-stage summary, 160 private producer-object
hashes and the 259-entry dependency snapshot manifest. The actual raw run,
including producer `.olean` files, remains retained under
`.lake/opt1-certificate-replay/20260912T103830Z-b52c64c9512542f292b26ed1c071039d`.

There were exactly 240 Lean compilations: 160 successful producer compilations,
two successful fixed-consumer accept controls and 78 field-specific consumer
rejections. The other three recorded stages were the two tracked-source
status probes and the import-freshness probe. All 39 fixed expected
propositions come from the unchanged [FIELDS.json](FIELDS.json), independently
pinned at its recorded v3 SHA; no expected type was extracted from a mutant.
The maximum observed Certificate, Capstone and Consumers stage durations were
10.141, 29.661 and 12.182 seconds, respectively, within the 180-second limit.
The complete campaign reported no unexpected errors or timeout/output-limit
events.

Every case restored and verified all three isolated source copies, and the
consolidation separately checked all 240 materialized source-copy hashes and
all 160 private producer hashes and non-alias properties. Global original,
import and tracked-status snapshots were exactly equal. The private read-only
dependency snapshot retained all 259 expected hashes. The worktree was still
clean at the frozen HEAD before evidence writes began. Original tracked source
bytes were never mutated by this replay; all actual field/comment mutations
were applied to the isolated source copies. The earlier A01 setup failure and
both synthetic checker-boundary failures remain preserved as separate evidence.

A post-wrapper global process observation briefly listed Lean PIDs 9808 and
26300. Both were absent before their command lines could be read, so their
ownership remains unidentified; no processes were killed. This observation
is retained in the full evidence without claiming either an owned leak or
unrelated activity. The completed executor session was closed and the shared
Lean slot was released to the coordinator.

The final unchanged runner also passes the nine script-only parameter boundary
checks in [final selector evidence](evidence/selector9-final.json). These
launch no Lean. No source, checker or registry bytes changed after the repaired
freeze. No aggregate Lake/gate run was performed by this leaf; that distinct
baseline compatibility purpose and coordinator acceptance remain external.

Final proof digestion: all registered altered producers successfully compiled,
and each unchanged consumer demanded its independently fixed public proposition.
Both expected-accept controls also compiled. This establishes the requested
finite field-dependency evidence and exact restoration record. Live assumptions
are the pinned Lean toolchain, the checked source/object provenance receipt and
the explicitly supported Windows process/filesystem behavior. A skeptical
reader can reconstruct each producer/consumer chain from the committed recipes,
frozen propositions and raw receipts; universal theorem acceptance and broad
compatibility remain the coordinator's responsibility. Worker status is
CANDIDATE_COMPLETE, not coordinator ACCEPTED.
