Status: CANDIDATE_COMPLETE (owned witness producer); downstream replay OPEN
Phase: SEVEN_ACTUAL_WITNESSES_EXPORTED_AND_PACKAGED

# NATIVE-1 operational occurrence witnesses

Owner `native_policy` may edit only `Native/Witnesses.lean`,
`Native/WitnessExport.lean` and this note for this leaf. Other ongoing ownership
of Binary/Checks and native.cpp is unchanged. The lead retains Execution,
Capstone and Validation/PackedNative. No commits or shared-ledger edits.
The already-passed rmq-proof-sprint governance preflight is
`0e6a00f654abc64f8b68988fa9675b9a839dca2f`. No Lean process starts before the
lead's compiler-slot handoff. The lead explicitly authorized drafting while it
checks the canonical closure.

## Frozen requirements and acceptance IDs

Verbatim lead requirement: "Hard target: replayable both-select,
fringe/interior/final-rank and real cross-cell witnesses feeding the registry;
no labels-as-coverage fallback. Export numeric expectations from connected
independent runArray/queryRun+spec, never limb actual."

| ID | Exact proposition or executable assertion to close | Status |
| --- | --- | --- |
| WIT-STAGES | Concatenating the computed semantic stage traces equals `SuccinctClassic.queryTraceResult xs left right).trace` on every valid range. Stages come from the actual two `packedSelectCloseLeaf` calls, LCA fringe/interior call decomposition, and final `packedRankCloseLeaf(close+1)`. | OPEN |
| WIT-READS | `queryRun_reference_reads` connects 174 actual metadata receipts plus the ordered `readerReceipts` expansion of those exact logical occurrences to the actual canonical query's raw receipts, including repetitions. | OPEN |
| WIT-TRANSITIONS | Each exported physical occurrence selects an actual `queryRun` transition at its exported index; `queryRun_read_at` supplies its exact prefix prestate, source instruction, address register and memory reply. | OPEN |
| WIT-CROSSING | A selected actual logical occurrence has a computed `reviewerLogicalSpan` satisfying `wordWidth n < (174*wordWidth n + position) % wordWidth n + length`; its two physical receipts align with actual load transitions to consecutive addresses. | OPEN |
| WIT-COVERAGE | A fixed exported fixture roster witnesses select-left, select-right, left-fringe window/fold, right-fringe window/fold, interior minimum, final rank and real cross-cell reads. Missing any actual occurrence fails export. | OPEN |
| WIT-INDEPENDENT | Expected result, halt status, steps, six category counts and ordered physical reads come from `runArray`/`queryRun`; reference answer and `scanWindow` are independently checked. No limb/native execution supplies expected numeric data. | OPEN |
| WIT-REPLAY | Committed operational `.fixture` JSON data and exact program/exporter hashes feed the lead/registry's native replay. Positive and fail-closed controls are replayable and exact source/check receipts are retained. | OPEN |

## Chosen construction and output contract

`queryReadyReference_eq_packedWholeQueryRun` connects semantic call composition
to the established query reference. `lcaCandidateReference_close` connects its
fringe/interior decomposition to the actual LCA leaf. Each `fringeReference`
will be split at its real `packedLocalBPSeed` bind, so fringe coverage requires
an occurrence from `fringeWindowReference`, rather than only a seed-rank read.
Both endpoint calls select closes; they are named select-left and select-right,
not select-open/select-close. The interior stage calls
`packedInteriorRangeMinRead`, not a rank operation.

Each logical occurrence records a cumulative logical offset, actual segment and
index, computed physical span and cumulative raw-read offset. Physical offsets
start after the 174 metadata receipts and increase by each exact
`readerReceipts.length`. Transition indices come from the actual ordered
`Run.transitions` receipt projection. Adjacent physical receipts need not be
adjacent primitive steps. Cross-cell witnesses retain both actual transitions.

The agreed JSON schema is `native1-canonical-witness-v1`, with `id`, `width`,
`inputLength`, `registerCount`, `left`, `right`, `fuel`, `memory`, a shared
`program` path and uncompressed SHA256, an independent `expected` observation,
and `witnessEvidence`. Arbitrary Nats and Ints are decimal strings where needed.
The original ListInt input and expected leftmost RMQ position are included.
JSON content uses the already-authorized operational `.fixture` extension;
no broad native fixture JSON path role is introduced.

Initial deterministic candidates are the existing twelve-element cross-block
input at (1,11), (6,10) and (4,8), and the monotone 24-element input at (0,24).
The exporter must inspect actual semantic/physical occurrences and fail if its
bounded candidate set lacks a required witness. No coverage label is inferred
from the fixture's name. A larger candidate search is allowed only when the
missing actual witness is identified, and its chosen input is recorded.

## Evidence and digestion

The exact universal join propositions being checked are:

```lean
flatten (stages xs left right) =
  (SuccinctClassic.queryTraceResult xs left right).trace

-- Given ValidRange, a decomposition prior ++ readWord segment index word :: after,
-- and readerReceipts shape (buildMemory xs) segment index [offset]? = some receipt:
(queryRun (buildMemory xs) xs.length left right).reads[
  174 + (logicalTraceReads shape (buildMemory xs) prior).length + offset]? =
    some receipt

-- Given the actual transition at index, and its actual receipt:
transition.before =
    (run (buildMemory xs) queryProgram index (initialState xs.length left right)).final ∧
  transition.before.status = .running ∧
  queryProgram[transition.before.pc]? = some transition.instruction ∧
  execute (buildMemory xs) transition.instruction transition.before =
    (transition.after, transition.receipt) ∧
  ∃ dst addrReg, transition.instruction = .load dst addrReg ∧
    receipt.address = transition.before.regs addrReg ∧
    receipt.reply = (buildMemory xs)[receipt.address]?

runArray (buildMemory xs) queryProgram.toArray queryBudget
    (initialState xs.length left right) =
  queryRun (buildMemory xs) xs.length left right
```

Here `shape` abbreviates the actual `SuccinctClassic.cartesianShape xs`, not an
independent witness object. The object-composition chain is the canonical
ListInt input → its concrete store and exact public reference → real semantic
call-site traces → ordered logical occurrences → reviewer spans and
readerReceipts → actual queryRun raw receipt ordinals → actual transition
indices and prefix prestates. The exporter uses the checked array evaluator
identity only to execute that same raw run efficiently; the native limb run is
the downstream subject of comparison. Neither the reference evaluator's
temporary transition list nor this validation export has a physical space or
constant-time claim.

The two source modules are drafted. `Witnesses` composes actual select,
fringe/interior and final-rank trace calls, with exact whole-reference equality.
`staged_receipt_at` targets the raw receipt at
`174 + (logicalTraceReads shape memory prior).length + offset`, given a
decomposition at the particular logical occurrence and the particular reader
receipt offset. It preserves repeated addresses by counting occurrences.
`occurrence_source` retains the actual transition index, full functional prefix
prestate, fetched instruction, execution equation, load register, address and
reply. `arrayRun_exact` connects the exporter evaluator to that exact queryRun.
These drafts await their compiler window and are not checked evidence yet.

The operational exporter checks the literal answer against both public
reference and scanWindow, expands all semantic occurrences to raw receipts,
matches them against actual load transitions in order, and selects each of
the seven required kinds from that recorded data. It writes no fixture before
all required kinds exist. It emits the actual canonical program text, whose
hash must equal the shared compressed program's uncompressed hash before replay.
The numeric expected result, halt state, steps, category counts and every raw
read are produced only by the independent raw evaluator; no limb/native result
is used as an oracle.

To avoid redundant preprocessing, a cache keyed by the entire ListInt input
stores only values computed by buildMemory, once per distinct input. Candidates
are inspected in the frozen order and inspection stops once all seven actual
occurrence kinds are found. This does not remove a required witness. The prior
PQ1 validation evidence reports60–169 seconds to build the24-element memory,
so unnecessary candidate construction would materially delay the exporter.
The root requested no compiler use during its initial native build; the first
queued targets are Witnesses followed by WitnessExport.

An independent read-only review by the machine worker found no stage/receipt
composition or oracle-independence error. It confirmed exact prior-trace
physical offsets preserve repetitions, both raw and transition projections
are checked, and crossing requires exactly two successful adjacent physical
receipts. It identified one local anti-vacuity gap: an emptied `kinds` list
could otherwise produce a vacuous zero-fixture PASS. The exporter now checks
the independently literal, ordered seven-ID roster before preprocessing or
creating files. This makes missing, duplicated, reordered or empty kind lists
fail locally, in addition to the registry's separate byte/source identity checks.

### First focused verification boundary

`Witnesses.lean` passed in **12.735 seconds**, checking all the universal join
propositions above. Its five axiom inventories contain only `propext`,
`Classical.choice` and `Quot.sound`. Three unused-simp-argument warnings do not
change the propositions. SHA256:
`8E732E615A9E69646AD6B6D2FDA5F632DF9826D2A22CA1B2DD71C98FF016B642`.
The initial attempt stopped at the absent `Packed/ArrayRun.olean` import in
6.802 seconds; that unchanged direct prerequisite was then checked once in
7.138 seconds. No full build or unchanged failed proof retry was used.

`WitnessExport.lean` elaborated successfully in **8.475 seconds**, SHA256
`4CF5C928FCD784DF112115A8BDFF87A8CA3FFC85AF04B679E320402106466F70`.
Two earlier attempts exited normally in7.256 and4.188 seconds: the reference
event's `isReadWord` property is Prop-valued and has no synthesized Decidable
instance at that interface. The repair uses a direct Boolean match on the
actual trace constructor, with no classical/noncomputable runtime workaround.

All six bounded receipts, including failures, are copied to
`docs/internal/extensions/native1/commands/` as `witness-proofs-01/02.json`,
`witness-arrayrun-01.json` and `witness-export-check-01/02/03.json`. Each check
has a120-second owned-process deadline and full output/source pins. No timeout,
output-limit event, surviving owned process, new axiom or native decision
procedure occurred. Scoped `git diff --check` passed. The compiler was handed
directly to the validator/axiom worker at this boundary.

WIT-STAGES and the universal producers for WIT-READS/WIT-TRANSITIONS are now
checked. Operational WIT-CROSSING, WIT-COVERAGE, WIT-INDEPENDENT and WIT-REPLAY
remain OPEN until the actual exporter produces the seven required fixtures
and the independent consumer validates and replays them. Compiling the exporter
alone is not evidence that the candidate pool contains those occurrences.

### Actual baseline export and durable artifacts

The baseline command
`lean --run RMQ/Core/WordRAM/Native/WitnessExport.lean .lake/native1/binary/witness-export-01`
passed in **403.369 seconds** under its independently chosen 1200-second owned
deadline. The complete receipt is
`docs/internal/extensions/native1/commands/witness-export-01.json`; it records
the exact executable/arguments, source and gzip hashes, complete stdout/stderr,
exit0, no timeout and no output-limit event. All four frozen candidates were
needed: their logical trace lengths were91,60,74 and109. No candidate or
expected answer was changed after the run began. Progress stdout was buffered;
the absence of early output was not treated as a completed or failed stage.

The actual exported canonical program is **10,848,489 bytes**. Its full bytes
equal the decompressed, already committed `native/packed-rmq/fixtures/program.txt.gz`,
with SHA256 `2D978D9D81CC3326F623F3A21AFCDA9FE3329E6F1DB60B2000425C4EF0A0D875`.
The plaintext stays in scratch; the lead chose the existing gzip as the durable
program input. Each final selector checks that gzip's decompressed SHA and the
fixture/source pins, rather than adding a second plaintext program or rerunning
the expensive exporter for every selector. This packaging decision is recorded
explicitly and does not turn the old fixture observations into the new oracle.

Seven new operational files were copied without replacing different existing
content into `native/packed-rmq/fixtures/`. Exact file/source/runtime hashes,
full selected occurrence records, program byte equality and sizes are retained
in `docs/internal/extensions/native1/commands/witness-export-artifacts.json`.
The registry worker received these durable paths and receipts for production
validation and same-checker semantic mutation controls.

| Fixture basename | Actual stage | Logical / raw receipt ordinal | Transition index / source PC |
| --- | --- | --- | --- |
| `canonical-select-left.fixture` | select-left | 0 / 174 | 408 / 1408 |
| `canonical-select-right.fixture` | select-right | 18 / 192 | 2762 / 92656 |
| `canonical-left-fringe.fixture` | left-fringe-window | 39 / 213 | 5556 / 250552 |
| `canonical-right-fringe.fixture` | right-fringe-window | 74 / 248 | 10823 / 784304 |
| `canonical-interior.fixture` | interior | 52 / 226 | 7549 / 292574 |
| `canonical-rank-final.fixture` | final-rank | 86 / 258 | 12579 / 826315 |
| `canonical-cross-cell.fixture` | interior | 68 / 242,243 | 10378,10384 / 310002,310011 |

The first six use the actual twelve-element cross-block input at[1,11), width176.
The independent raw run halts with packet6 (leftmost position5), in13,231 steps,
with263 reads and category vector `[263,4470,2401,2254,3842,1]`. The two select
occurrences deliberately load the same address174 and same reply at distinct
logical, physical and transition offsets; this concretely demonstrates that
the occurrence account preserves repetitions.

The crossing witness uses the monotone24 input at[0,24), width184. Its segment20,
index0 field has absolute bit position33116, cell offset180 and length6:
`184 < 180 + 6`. It actually loads address179 at transition10378/PC310002 into
register8259, then address180 at transition10384/PC310011 into register8266;
both use address register8261 and both replies are successful. Those are two
physical loads separated by six transitions, not two invented adjacent steps.
The run halts with packet1 (leftmost position0), in16,358 steps, with283 reads
and category vector `[283,5395,3037,2874,4768,1]`.

WIT-STAGES, WIT-READS, WIT-TRANSITIONS, WIT-CROSSING, WIT-COVERAGE and
WIT-INDEPENDENT are now CANDIDATE_COMPLETE for this owned producer. WIT-REPLAY's
durable inputs are ready; independent semantic falsification controls and the
actual native replay remain with the registry worker and lead. No coordinator
acceptance or complete NATIVE-1 claim is made by this producer report.

### Design-decision prose and proof digestion

Coverage now follows actual semantic call sites, then exact ordered expansion
into physical receipts and primitive transitions. We rejected classifying
coverage from fixture names, isolated segment numbers or address membership:
those alternatives cannot distinguish repeated select reads or demonstrate
which fringe/interior operation caused a load. The stage decomposition uses
the established reference functions and proves its concatenation equals the
public trace. The reference array evaluator is connected to queryRun and
supplies all numeric expectations, while scanWindow independently checks the
leftmost answer. Native execution supplies none of those expected values.

In plain English, each fixture now identifies where a required query operation
really read memory, with enough data to follow it from its logical field down
to the exact load and the returned cell. The all-input proof gives the
correspondence; the checked export shows the selected concrete cases actually
exist. The live trust boundary is ordinary compiled Lean execution for the
fixture computation, followed by the separately audited native build/replay.
The universal proof uses the project's existing classical quotient/proposition
axioms only, and these exporter runtime costs or retained transition objects
are not included in the succinct numeric payload claim.

A skeptical reader should next ask whether the native loader preserves these
exact program/memory cells, whether Rust and C++ execute the same image, whether
their complete observations match the independent fixture, and whether the
production witness checker rejects falsified geometry or occurrence fields.
Those are the explicit downstream replay consumers, not assumptions silently
discharged by labeling these fixtures.
