# BV-1 executable validation — frozen production-verdict controls

Status: CANDIDATE_COMPLETE

I found no assigned or inherited acceptance criterion unmet; coordinator
acceptance is still required.

Owner: numeric_reader after explicit transfer from root. Governed continuation
at source HEAD 645a0502b9da9ad6444edbe44759e1c2c5661f25 and governance
0e6a00f654abc64f8b68988fa9675b9a839dca2f. Canonical proof-sprint and completion
gate apply. Scope: RMQ/Validation/PackedBitvector.lean; the probe, selector
controls and crossing scripts; new validation-controls runner, this report
and task-owned replay/evidence records. No Core/Source/Capstone/public consumer
edits. Other agents are active and their changes must remain intact.

## Verbatim task and frozen acceptance

"Close startup→known→full46 including all4 wholeoperation crossing assertions,
exactselector8, crossingv3 all3." "Add frozen5-case same-production-verdict
mutation campaign: baseline accept; wrong independent expected packet (e.g +1);
removed fixture with unchanged golden names => registryfailure; wrong crossing
expectation for a known actualcrossing => runCasefailure; restoredaccept."
"Mutate only immutable copies, committed exactbefore/after replayablefixtures,
scoped hashes/status, owneddeadlines, exactfailurepins, no resourceerrors count
as semanticreject." "Strict8 selectors for any new runner."

No full 46-case run will be repeated on an unchanged final source. The
omitted-selector case in the existing exact eight-case selector campaign is
the full run. Startup and one known case precede it. Root explicitly limits
the first compiler slot to startup, known and initial focused crossing
diagnostics; public mutation checks take the next shared slot.

| ID | Exact expected verdict / object chain | Anti-vacuity boundary | Status |
| --- | --- | --- | --- |
| VAL-START | Production main version2 startup reports expected=46 and passes its independent registry equality; selected mixed-true reports executed=1 expected=1 passed=1 total=46. | Empty selection is rejected; startup cannot substitute for execution. | CANDIDATE_COMPLETE |
| VAL-FULL | Production main omitted selector reports executed=46 expected=46 passed=46 total=46, with all four named whole-operation crossing cases passing crossing=true. | Crossing requires an actual second span-load transition at the exact request, address and reply; correct final packets alone do not pass. | CANDIDATE_COMPLETE |
| VAL-SELECT | Exact ordered selector registry omitted, valid, empty, whitespace, malformed, unknown, padded, incompatible: first two accept; remaining six exit2 at BV1-SELECTOR FAIL. Applies to production probe and new mutation runner. | No omitted/invalid selector silently turns into an empty successful suite. | CANDIDATE_COMPLETE |
| VAL-CROSS | Reader crossing version3 exact three names below execute and pass on final Allocation.memory and its corresponding logical read store. | Earlier Experiment.memory must not substitute; true-target raw case must actually exercise complementation. | CANDIDATE_COMPLETE |
| VAL-MUTATE | Exact five control names below execute immutable production-source copies with unchanged verdict logic and meet their pinned semantic/registry verdicts. | Timeout, missing imports, syntax/elaboration error and output-limit termination never count as expected rejection. | CANDIDATE_COMPLETE |
| VAL-RESTORE | Replayable versioned registry records exact original/replacement bytes and fixture hashes; tracked production inputs have identical scoped hashes/status before and after. | A restoration note without exact byte checks does not pass. | CANDIDATE_COMPLETE |

Frozen 46 production names, in exact order:
empty-false, empty-true, singleton-zero, singleton-one, singleton-missing,
size-two-false, size-two-true, size-two-invalid, zeros-last, zeros-missing-true,
ones-last, ones-missing-false, alternating-false, alternating-true,
mixed-false, mixed-true, threshold-minus-one, threshold,
access-empty, access-singleton-zero, access-singleton-one, access-length,
access-length-plus-one, access-mixed-last, rank-empty-false, rank-empty-true,
rank-empty-invalid, rank-zero-prefix, rank-singleton-false, rank-singleton-true,
rank-length-false, rank-length-true, rank-length-plus-one, rank-zeros, rank-ones,
rank-threshold-minus-one, rank-threshold, access-crossing, rank-crossing,
select-false-crossing, select-true-crossing, rank-max-representable,
select-max-representable, api-access-unrepresentable, api-rank-unrepresentable,
api-select-unrepresentable.

Frozen reader crossing names:
reader-component-crossing, raw-false-crossing, raw-true-crossing.

Frozen five production-verdict controls:
1. baseline: unchanged production source, --case access-crossing; exit0 with
   BV1-CASE access-crossing PASS and executed=1 expected=1 passed=1 total=46.
2. wrong-packet: change only the independent expected packet value by +1,
   --case access-crossing; exit1 with BV1-CASE access-crossing FAIL and
   executed=1 expected=1 passed=0 total=46.
3. removed-fixture: remove only the access-crossing fixture row while keeping
   the literal expected names unchanged; production registry fails exit2 at
   BV1-REGISTRY FAIL version=2 before executing cases.
4. wrong-crossing: change only the crossing request-index expectation from
   19 to 20, --case access-crossing; exit1 at BV1-CASE access-crossing FAIL
   with crossing=false and executed=1 expected=1 passed=0 total=46.
5. restored: exact original production bytes, --case access-crossing; same
   accept verdict as baseline and exact baseline/restored hash equality.

Each replay case retains the actual production main/runCase functions.
Mutation records will materialize whole immutable source fixtures plus exact
before/after text and SHA256 hashes. The runner validates that each fixture
equals the expected literal mutation of the frozen baseline before Lean runs.
It never edits production source. The additional eight selector controls for
the new runner are orchestration checks; their omitted case runs the five-case
campaign once, with selected baseline as the known selector control.

## Same-allocation adjustment and verification plan

The transferred crossing v3 draft opened Experiment and selected its old
memory/genericLogicalWord. Root approved switching that owned script to
Allocation.memory and Allocation.readStore, while retaining the exact names,
same actual physicalReader and actual second-load transition assertions. This
aligns the test with the final counted allocation; no Core implementation or
semantic specification is changed.

Use pinned Lean4.22, LEAN_NUM_THREADS=1 and the repository owned bounded
process helper. Initial deadlines: startup180s, known300s, focused crossing300s.
Inventory warm imports before running. After the first quantum release,
prepare immutable mutation files offline. Calibrate full/campaign deadlines
from observed startup, known and crossing runtimes. Full46 is executed only
through omitted production selector in its final selector campaign. Root owns
public mutation, full project gate and final commit/audit; this leaf owns the
runtime validation evidence and replayable controls.

## Evidence and digestion

Initial startup, known query and all three final-allocation reader crossings
have passed. The production eight-selector campaign subsequently passed,
including its single omitted-selector full46 run. The immutable five-case
replay passed all five pinned verdicts, and its eight-selector campaign also
passed. Both granted campaigns exited0, all owned children closed, and the
shared build slot was explicitly released to root and normalization. No
source verdict was weakened.

| Initial owned stage | Result | Observed production surface |
| --- | --- | --- |
| validation-v2-startup | PASS, exit0, 4.400 seconds / 180 | BV1-STARTUP PASS version=2 expected=46. |
| validation-v2-known | PASS, exit0, 6.900 seconds / 300 | mixed-true: expected7, actual some7, 1969 steps, 118 reads; executed1/expected1/passed1/total46. |
| validation-crossing-v3-first | PASS, exit0, 141.010 seconds / 300 | Exact three cases all pass; each observes one actual second load. Component: segment2/index0 packet1. Raw false: segment0/index19 packet342. Raw true: same request packet171 with complemented=true. |
| selector-omitted-main-v2-final | PASS, exit0, 378.344 seconds / 600 | BV1-REGISTRY version=2 executed=46 expected=46 passed=46 total=46. All four whole-operation crossing fixtures pass with crossing=true. |
| selector-controls-main-v2-final | PASS, exact8/8, no timeouts, exactRestoration=true | Omitted and valid accept; empty, whitespace, malformed, unknown, padded and incompatible each exit2 at the exact selector rejection surface. |
| selector-controls-validation-v1-final | PASS, exact8/8, no timeouts, exactRestoration=true | Omitted runs the exact5 controls once; valid runs baseline only; all six invalid selectors exit2 at BV1-SELECTOR FAIL. |
| validation-controls-selector-valid-validation-v1-final | PASS, baseline only, exit0, 71.490 seconds / 300 | executed1/expected1/passedTrue/total5; exactRestoration=true and statusUnchanged=true. |

The four whole-operation crossing outputs in that single full46 record are:

| Case | Expected / actual packet | Steps | Physical receipts |
| --- | --- | --- | --- |
| access-crossing | 2 / some2 | 122 | 25 |
| rank-crossing | 88 / some88 | 543 | 45 |
| select-false-crossing | 173 / some173 | 1726 | 106 |
| select-true-crossing | 172 / some172 | 1738 | 110 |

Each reports crossing=true. The production predicate requires an actual
`load 8266 8261` transition, request register8193=19, the fixture's segment
register8192, address register8261=208, and the exact reply from memory208.
Thus these assertions inspect the same actual transition trace that produces
the output packet. The full record contains exactly46 BV1-CASE lines; it was
not rerun unchanged. Its enclosing omitted-selector process took390.620
seconds, including process startup and evidence serialization.

The checked crossing source SHA256 is
33FFD328EBC0F80EEBEA279B4904F804D5A54E1FE5CBC2C4A017A75807FE279D.
Its physical reader and expected read store both use final Allocation.memory.
The first shared slot was released after these checks, without a full46 run.
All stages used one-job pinned Lean4.22 and the owned process helper; no
timeouts or surviving owned children occurred.

The immutable replay registry is controls/validation_v2/registry.json.
It references baseline.lean, wrong_packet.lean, removed_fixture.lean,
wrong_crossing.lean and restored.lean and stores exact before/after text,
occurrence counts, arguments, expected exits, exact output pins and hashes.
The baseline/restored/frozen production SHA256 is
333B0A6BD8FB3082051845D2F1BD333668B9D33758A9030A68B25695CFEE068E.
The new runner's startup validated exact five-case ordering, immutable hashes,
each literal source mutation and baseline/restored byte equality without
launching Lean. PowerShell AST parsing of both runners found no errors.

The existing selector campaign now has an explicit Runner parameter, Main or
ValidationControls. Both retain the exact same eight selector categories.
For Main, omitted invokes the only full46 run and valid invokes mixed-true.
For ValidationControls, omitted invokes the five-case campaign once and valid
invokes its baseline control. No selector rejection launches Lean. Invalid
or resource-failed mutation executions cannot count as semantic rejection:
the runner requires the exact production exit and pinned verdict text and
rejects deadline, output-limit and compiler/runtime error surfaces.

The granted final deadlines followed observed 141-second three-crossing runtime:
the production omitted full46 case keeps its existing600-second inner budget
and660-second selector wrapper; each mutation case gets300 seconds and its
omitted five-control wrapper gets660 seconds. These are distinct serial
campaigns in the explicitly granted slot. No unchanged full46 repeat occurred.

The five-case record is
commands/validation-controls-selector-omitted-validation-v1-final.json.
It records exact selected/executed order, all17 pinned surfaces present,
resourceFailure=false for every case, exactRestoration=true and
statusUnchanged=true over all11 watched production/replay paths.

| Immutable control | Expected / actual exit | Seconds / 300 | Exact production surface |
| --- | --- | --- | --- |
| baseline | 0 / 0 | 94.404 | access-crossing PASS, expected=2 actual=some2, crossing=true, passed1/total46. |
| wrong-packet | 1 / 1 | 89.595 | access-crossing FAIL, expected=3 actual=some2, crossing=true, passed0/total46. |
| removed-fixture | 2 / 2 | 8.923 | BV1-REGISTRY FAIL version=2; unchanged independent golden names reject the removed row. |
| wrong-crossing | 1 / 1 | 73.532 | access-crossing FAIL, expected=2 actual=some2, crossing=false, passed0/total46. |
| restored | 0 / 0 | 76.185 | Exact baseline bytes again accept at the baseline surfaces. |

The wrong-crossing case retains the correct final packet and is rejected
solely by its changed request-index expectation. The wrong-packet case
retains the real successful crossing and is rejected by the changed
independent expectation. The missing fixture is rejected by the same
production main's independent registry comparison before selection.
No alternate verdict function, synthetic trace or fabricated runtime result
participates in these controls.

The omitted mutation wrapper took361.060 seconds / 660. Its exact selected
baseline wrapper took80.827 seconds / 660. Every invalid selector completed
with exit2 without launching Lean; their observed runtimes were3.365–5.435
seconds. Both selector records retain each actual exit, full output, expected
surface, timeout/output-limit result and source hashes before/after.

## Replay and evidence map

All names below resolve within docs/internal/extensions/bv1. Records are
persisted inputs to coordinator review and the final root commit, not terminal
transcripts standing in for replay fixtures.

| Acceptance row | Exact evidence |
| --- | --- |
| VAL-START | commands/validation-v2-startup.json; commands/validation-v2-known.json |
| VAL-FULL | commands/selector-omitted-main-v2-final.json |
| VAL-SELECT | commands/selector-controls-main-v2-final.json; commands/selector-controls-validation-v1-final.json |
| VAL-CROSS | commands/validation-crossing-v3-first.json |
| VAL-MUTATE | controls/validation_v2/registry.json and its five full Lean fixtures; commands/validation-controls-selector-omitted-validation-v1-final.json |
| VAL-RESTORE | Both selector records, both validation-control records, and commands/validation-final-static.json |

Replaying the two omitted selectors runs their complete exact registries;
use fresh evidence tags because overwriting an existing record is rejected:

```powershell
& scripts/packed_bitvector_selector_controls.ps1 -Runner Main `
  -EvidenceTag <fresh-lowercase-tag> -DeadlineSeconds 660
& scripts/packed_bitvector_selector_controls.ps1 -Runner ValidationControls `
  -EvidenceTag <another-fresh-lowercase-tag> -DeadlineSeconds 660
```

Run these serially in an explicitly allocated build slot. The immutable
runner pins the Lake/Lean executable, and the registry records the exact
case arguments for individual fixture replay; `-Case` must be one exact
frozen name.

## Proof digestion and integration boundary

Conceptually, the implementation evidence now follows the final allocation
from the actual compiled operation through physical receipts and independent
list-based answers. Forty-three production fixtures exercise the primitive
runner; three additional fixtures check the API's out-of-word argument guard.
The three focused reader fixtures use the same final allocation and logical
read store, including a complemented true-target raw crossing.

The new controls establish that this particular production verdict is
sensitive to wrong answers, a missing required fixture and a wrong physical
crossing expectation. Baseline and restored accepts bracket the rejections,
and exact mutation bytes make each case replayable. These finite executions
support the universal theorem and public-dependency evidence owned by root;
they do not replace those Lean propositions or establish new asymptotic
claims. The live runtime assumptions are the pinned Lean4.22 executable,
current imported source/dependency tree, owned process helper and exact
frozen fixture bytes. No Core definition or proof trust base changed here.

A skeptical reader should next ask whether a fresh final checkout preserves
the recorded bytes, whether the public capstone depends on the same objects,
and whether the full project gate passes at the integrated commit. Root owns
the checkout-byte patch, independent public consumers/mutations and final
gate/commit. No additional core design or workflow decision was introduced
by this leaf: it follows the already frozen source, allocation, process
ownership and mutation contracts. Root can incorporate this digestion in the
final project log. The shared-tree work remains uncommitted until root's
coordinated final commit; all replay fixtures and registries must be included.

The final hygiene scan found no forbidden trust keywords/imports in RMQ or
lakefile.toml and no native_decide/Lean.ofReduceBool occurrences. The owned
diff check passed. Full Lake/gate execution is left to root's final integrated
certification; rerunning it in this narrow validation leaf would duplicate
the coordinated final gate and consume the shared build slot.

## Exact-byte checkout integration

Exact-byte checkout portability is tracked by root: core.autocrlf=true and
unspecified text attributes can otherwise rewrite these frozen Lean fixture
bytes on a fresh checkout. Root prepared four -text attribute rules in
CHECKOUT_BYTES_PATCH.diff, with a successful dry run, and identified a fifth
rule for the existing mixed-line-ending lakefile.toml dependency. Root is
resolving those outside-scope integration changes with the coordinator and
will apply them between campaigns to preserve the scoped status checks.
This leaf retains
strict hash checks; no line-ending normalization or bypass was added to the
runner. Fresh-checkout replay certification depends on the root-owned
attribute patch being integrated with the frozen artifacts.
