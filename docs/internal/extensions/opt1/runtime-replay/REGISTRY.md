# OPT-1 runtime registry v1

Version: `v1`. Exactly 27 cases: 23 expected accepts and four expected rejects.
This table is independently pinned by `scripts/packed_optimized_runtime.ps1`;
neither copy is generated from the Lean producer.

| ID | Verdict | Exact rejecting surface |
| --- | --- | --- |
| C01-ZERO-BRANCH | ACCEPT | none |
| C02-NONZERO-BRANCH | ACCEPT | none |
| C03-ZERO-LOOP | ACCEPT | none |
| C04-ONE-LOOP | ACCEPT | none |
| C05-REPEATED-LOAD | ACCEPT | none |
| C06-NESTED-LOOP | ACCEPT | none |
| C07-EARLY-HALT | ACCEPT | none |
| C08-FAILED-LOAD | ACCEPT | none |
| C09-EMPTY-BODY-BOUNDARY | ACCEPT | none |
| C10-NESTED-SEQUENCE | ACCEPT | none |
| C11-INITIALLY-HALTED | ACCEPT | none |
| C12-INITIALLY-FAULTED | ACCEPT | none |
| C13-EMPTY-BRANCHES | ACCEPT | none |
| Q01-EMPTY | ACCEPT | none |
| Q02-SINGLE | ACCEPT | none |
| Q03-LEFTMOST-TIE | ACCEPT | none |
| Q04-REVERSED | ACCEPT | none |
| Q05-OUT-OF-RANGE | ACCEPT | none |
| Q06-DIFFERENT-BLOCKS | ACCEPT | none |
| Q07-SAME-BLOCK | ACCEPT | none |
| Q08-ADJACENT-BLOCKS | ACCEPT | none |
| Q09-MALFORMED-METADATA | ACCEPT | none |
| Q10-WORD-MAX | ACCEPT | none |
| N01-JUMP | REJECT | N01-JUMP: compiler observation mismatch |
| N02-COUNTER | REJECT | N02-COUNTER: compiler observation mismatch |
| N03-BUDGET | REJECT | N03-BUDGET: compiler observation mismatch |
| N04-FRESH-COLLISION | REJECT | N04-FRESH-COLLISION: compiler observation mismatch |

For C cases and all four negatives, the accepted observation predicate is
`actual.final.status == fixture.expected && actual.reads == fixture.receipts`,
where `actual := runArray fixture.memory program.toArray fuel fixture.state`.
Both domains use the same supplied memory/state and fixture expectations.
Expected status and ordered receipts are literals independently checked
against `fixture.source.eval fixture.memory (Data.ofState fixture.state)`.
The negative fixture is the three-load positive scenario C05, with its ID
changed only to identify the perturbation. N01 replaces emitted instruction 2
by `.branchZero 8 0`; N02 replaces instruction 0 by `.constant 8 0`; N03 runs
with zero fuel; N04 emits with fresh base 0 instead of 8, colliding with the
source address register. All must fail the identical observation check before
step/frame checks, with exit 1 and the exact registered error suffix.

Query cases compare `scanWindow` and independently literal indices with the
compact and original query programs on the same `buildMemory` and initial
state. Ordered attempted read/reply lists retain duplicates. The malformed
metadata case also executes altered and missing memory in memory; no tracked
source bytes are edited by any runtime case.

Omitted `-OnlyCase` runs startup C01, known C05, all 23 positive cases in one
Lean process, four separate rejecting Lean processes, real script selector
boundary controls, and direct Lean channel controls. Startup receipts are
separate from the final 27-case expected/executed registry. A valid explicit
selector runs exactly that case; negative selection means one expected reject.
Bound empty, whitespace, malformed, unknown and duplicate script selectors
fail before semantic execution. Every Lean selector is sent through nonempty
`OPT1_RUNTIME_SELECTOR=id:<ID>`; true omission removes the environment entry.

Each actual subprocess has a deadline, 4 MiB output cap, owned-tree cleanup,
separate stdout/stderr artifacts, exact command/environment metadata, and
recorded exit/timeout/ownership. Infrastructure failures cannot count as
semantic rejects. Artifacts live in the ignored `.lake/opt1-runtime-replay`;
the durable report records verified runs and hashes. Source hashes are checked
before and after the campaign even after failure. Because this runner writes
no tracked source bytes, hash equality is a no-mutation check, not evidence
that a tracked-source mutation was restored or that the repository was clean.

Script-only modes are `-RegistrySelfTestOnly`, `-SelectorBoundarySelfTestOnly`,
`-DeadlineSelfTestOnly`, `-ArtifactCheckOnly`, and `-SelectorProbeOnly`. They never launch Lean.
Artifact checking recursively verifies local imports exist and their artifacts
are no older than the source or direct imported artifacts; the emitted manifest
records both source and artifact SHA-256 values. Actual replay includes those
artifact bytes in its before/after snapshots. This is a conservative freshness
guard and immutable-artifact record; the coordinator's checked build supplies
the compilation evidence connecting source to artifact.
`-StartupOnly` runs C01 followed by C05 and is the required first runtime
probe after a new import closure. Full mode also repeats these bounded probes
before its semantic campaign. `-OnlyCase C01-ZERO-BRANCH` provides the smallest
single semantic probe. No mode invokes Lake or builds imports implicitly.
