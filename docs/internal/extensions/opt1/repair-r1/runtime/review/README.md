# Read-only parent regression verdict review

At the parent's request, this leaf reviewed the new repair runner's selector,
verdict, restoration and duplicate-import integration. It made no edits to the
parent-owned scripts. `RESULT.json` preserves three real 60-second/1 MiB owned
children applied to the unique actual `Assert-R1Verdict` function extracted from
parent runner SHA-256
`9f52c599fee4b7bee683ba9a87156a028959e37339afa7ad8e430d04517c71fd`.
`PARENT_SCRIPT_BEFORE.ps1` preserves those exact pre-fix source bytes as review
history; it is not an alternate production path. The three child `.ps1` files
preserve the exact executed fixture source. Final tests use the actual repaired
parent function, never this historical copy.

The sole expected import-error stderr accepted, as intended. The same stderr
with an unrelated uncaught exception on stdout also accepted; the same stderr
with a full certificate success receipt on stdout accepted. The last two are
validator defects, not evidence that a production Lean case had mixed output.
The receipt hash is
`6b94bc821130eaddea08c8818a0a0b485b6610ac6e9e799397ddb346bd555231`.
`replay.ps1` exercises the current actual parent function with these same real
outputs and reports its verdicts; the parent owns the correction and final
registry controls.

The expected setup-negative stdout grammar is the ordered artifact path,
tracked-before stage, import-freshness stage, tracked-after stage, and exact
original-source restoration line. Each occurs once. Boundary negatives should
have no stdout. The intended stderr should be a complete fixed diagnostic where
possible. Missing/stale-artifact and UTF-8 controls also need the nested retained
import-freshness result's precise failure, since the outer wrapper's generic
producer failure alone does not identify the cause. Arbitrary additional output
and completion/success markers must not certify a negative.

Source inspection found that the new duplicate-import detector runs before
map population and rejects duplicate module/source/artifact records, rather
than allowing a dictionary to overwrite them. Selector routing correctly
separates boundary cases and middle-row mutation cases. The genuine typed
weakening path requires the actual selected `W28-stepBound` rejection receipt
and a successful inner replay result. A narrow fixture compatibility mismatch
was also reported: accepting a `.git` file at fixture validation while reading
`.git/index` directly later does not support linked worktrees. Either require a
clone's `.git` directory or resolve the actual index through Git. The parent
decides its supported fixture profile.

After the parent's correction, an independent follow-up ran the actual parent
entry point for `V01-SOLE-SETUP`, `V03-SUCCESS-STDOUT`, `V04-WRONG-STDERR`,
`V06-DUPLICATE-PROGRESS`, `V07-REORDERED-PROGRESS`, `V08-EXTRA-STDERR` and
`V09-PREFIX-HOLDOUT`. All seven passed. The sole setup control accepted; all six
adversarial controls rejected at `Assert-R1Verdict`. The parent script's hash
before and after was
`e9de8689ca8c49f36b1ea4898e0504ee79bc30af6d385d1b370404d7f57dd78d`.
Each focused parent invocation had a 150-second/1 MiB owned outer bound and a
120-second parent campaign bound; its actual child stage used 60 seconds and
the parent's 8 MiB ceiling. Total observed outer process duration was 93.144
seconds. All seven exited 0 with no outer stderr, timeout or overflow.

`fixed-controls.json` contains all seven expected/executed IDs, original child
stream results through the parent receipts, actual classifier outcomes and
source hashes. It is 27,889 bytes with SHA-256
`3eb4611c50e28c0708986c2aba87679cfeec20bcab4b1e00cb4921648bb41fff`.
`run-fixed-controls.ps1` reproduces these focused actual-entry checks in fresh
private receipt directories. The updated helper admits an ordered subsequence
of its explicitly permitted setup progress records and exact sole stderr;
unrelated records, duplicate/reordered progress and padded prefix holdouts
reject. The `.git` directory guard now matches the direct index-path use.
No additional concrete defect was found in this scoped follow-up. The parent's
V02/V05 controls were not repeated here. The later complete 46-case production
campaign remains a separate final-tree consumer, and P07/P08/P15 nested source
failure checks remain unexecuted until the profile build is available. No Lean
process was launched by this review.
