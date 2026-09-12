# BV-1 evidence against the frozen requirements

Status: INCOMPLETE — candidate commit, byte round trip and final certification remain.
This companion preserves all 30 IDs and the verbatim requirements in
[ACCEPTANCE_MATRIX.md](ACCEPTANCE_MATRIX.md), SHA256
`80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24`.
The frozen document's historical OPEN cells are unchanged. No row below records
coordinator acceptance or substitutes a weaker endpoint for the assigned target.

The checked producer is
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone`.
It takes no arguments or correctness, readiness, geometry or compatibility
premises. Its exact 23 field propositions are quoted in
[CAPSTONE_COMPOSITION.md](CAPSTONE_COMPOSITION.md), and repeated independently,
with expanded safety and reader predicates, in
[public_expected_type.lean](controls/public_expected_type.lean).
The latter has 23 arbitrary-certificate projections and the exact inhabitant
consumer. It passed in 15.320 seconds after the producer passed in 9.170 seconds.
The precise producer and consumer SHA256 identities are respectively
`1C6CD0A85B77FBA7706C77DA87DE358808A24FA661D5635A3C4B3BBF96005D69` and
`FEA8D045EF0A9CB9679949ED8825F2E04A4542C01E8F056A778BB0B474BF7A9E`.

## Quantified propositions and common object chain

Every positive canonical proposition uses the same chain, with the operation and Boolean parameters shown
in the proposition: original `bits : List Bool` -> both canonical select
directories, four canonical rank sample tables and shared chunk tables ->
`Allocation.allSegments bits` -> `Allocation.memory bits` -> charged setup and
`Experiment.physicalReader` -> existing primitive rank/select/access blocks ->
`source operation` -> existing Structured compilation -> `program operation`
-> actual `run` -> `execute` -> public field -> the independently typed field
projection. `program` and `source` depend only on the finite operation, not on
the input list, target or argument. The checked frontier is 645a050 plus the
reviewed shared working-tree changes from this task's disjoint agents; the
candidate commit is pending. No external worker branch supplies a dependency.
Parameterized exceptions and supplied-memory or sibling negative controls use
their explicitly identified alternate objects and do not claim canonicality.

The allocation proposition quoted by `public_completeCapacity_required` is:

```lean
∀ bits : List Bool,
  ((Allocation.memory bits).length +
    ((program .access).map Instruction.encoding).flatten.length +
    ((program .rank).map Instruction.encoding).flatten.length +
    ((program .select).map Instruction.encoding).flatten.length +
    (8271 + 3)) * Experiment.width bits.length ≤
      bits.length + completeRho bits.length
```

The other two space/width propositions are `LittleOLinear completeRho` and
`∀ n : Nat, Nat.log2 (n + 2) + 1 ≤ Experiment.width n ∧
Experiment.width n ≤ 48 * (Nat.log2 (n + 2) + 1)`.
There are 39 real component arrays, 207 numerical header words, dense body
padding, all three literal encoded programs and 8274 scratch/control words.
The raw view used by rank is an alias for the same physical raw component.
`body_capacity` in Space.lean, `data_capacity` and `complete_capacity` compose these
actual objects; [ALLOCATION_READER_PROOFS.md](ALLOCATION_READER_PROOFS.md)
records the component inequalities and exact accounting derivation.

The unconditional API propositions are:

```lean
∀ (bits : List Bool) (index : Nat), access bits index = bits[index]?
∀ (bits : List Bool) (target : Bool) (endPos : Nat),
  rank bits target endPos =
    if endPos ≤ bits.length then some (Succinct.rankPrefix target bits endPos) else none
∀ (bits : List Bool) (target : Bool) (occurrence : Nat),
  select bits target occurrence = Succinct.select target bits occurrence
```

Access indices and select occurrences are zero-based; rank counts `[0,endPos)`.
The encoding guard is explicit and applies to the unbounded-Nat API. The actual
run fields hold for every natural argument; the five-conjunct physical safety
fields require only `argument < 2 ^ Experiment.width bits.length`. The public
valid-input proposition is `∀ n argument : Nat, argument ≤ n →
argument < 2 ^ Experiment.width n`.

The executable expression is exactly:

```lean
run (Allocation.memory bits) (program operation)
  ((source operation).size + 1) (initial operation target argument)
```

Each execution field fixes that run's result, halted status, result register,
exact ordered setup/controller receipts and literal bound: 132 for access,
1450 for rank and 10030 for select. The independent consumer expands each
packet from the original List specification. Each safety field expands all
encoded instructions, every transition, every fuel prefix up to
`(source operation).size + 1`, final state and
every indexed receipt at those same allocation/program/entry arguments.
Stored values and every addressed reply fit the same declared width. The
reader field fixes actual packet/length/ordered receipts/frame from numerical
descriptors, including present empty words, absent words and inactive segments.

Two further exact propositions prevent a final-state or selected-footprint
substitute for the full execution:

```lean
∀ (memory : Memory) (operation : Operation) (target : Bool)
    (argument fuel r : Nat), 8271 ≤ r →
  (run memory (program operation) fuel
    (initial operation target argument)).final.regs r = 0

∀ (bits : List Bool) (operation : Operation) (target : Bool)
    (argument : Nat) (supplied : Memory),
  (∀ receipt ∈ (execute bits operation target argument).reads,
    supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) →
  run supplied (program operation) ((source operation).size + 1)
    (initial operation target argument) = execute bits operation target argument
```

The second equality is equality of the whole Run, including result, final
state, transitions, costs and ordered receipts. Its agreement predicate
includes failed attempted replies. Six category counts, computed from those
actual transitions, sum to actual steps and are individually bounded by the
same operation constant.

## Requirement-by-requirement evidence

The proposition references in this table refer to the exact quotations above
and the full independently expanded 23-field consumer, rather than theorem
names as stand-alone evidence. The common object chain applies to each positive
canonical claim. The third column specifies the required decisive tests; a
test is completed only when the separate persisted outcome records below say
so. All runtime and public mutation campaigns below have passed. The committed
byte comparison and final certification remain pending; prepared fixtures or
prospective descriptions do not close an obligation.

| Frozen ID | Exact proposition and concrete composition | Required decisive anti-vacuity check (see outcomes) |
| --- | --- | --- |
| REQ-BV-ALLOC | Literal complete-capacity inequality, `LittleOLinear completeRho`, and both logarithmic width inequalities; both directory bounds, four rank tables, header/padding, all encoded code and finite scratch compose into the actual executed memory. | Public `completeCapacity`, `overheadLittleO`, `widthBounds` weakenings; smaller-memory sibling; separately omitted code and scratch charges. |
| REQ-BV-OPS | Three all-Nat API equalities plus actual result/status/register packets and exact receipts for the same list and both target values; explicit representable safety boundary. | Main operation registry covers empty/singleton/two-element, both bits, prefixes at and beyond length, absent occurrences and word-range guard; charged-cell mutations change actual answer projections. |
| REQ-BV-RUN | Literal program/source bounds 132/1450/10030; all five safety conjuncts on the whole compiled run; actual category partition and bounds. | First-load empty-memory faults for all operations; dormant oversized operand rejected by actual whole-program Fits; real crossing loads; public execution/safety/length/category weakenings. |
| REQ-BV-REUSE | Source embeds the existing physical span/decode and rank/select blocks and uses `compileAt`; canonical numerical reader derives packet/length/receipts/frame for arbitrary lists without a shape premise. | Expanded reader consumer and reader sibling mutation; physical crossing receipt checks; all shared Packed source paths remain unchanged. |
| REQ-BV-JOIN | Exact hypothesis-free `fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone`, with all 23 projections at the common object chain. | Every field weakened separately; field deletion; three well-typed siblings; exact public theorem changed to True; expected-accept unchanged/comment controls. |
| CHK-BV-CONTROLS | Main exact 46-case registry executes the final allocation and programs against List expectations; three final-allocation reader crossings; four valid parameterized long/sparse routes. | Wrong expected packet, missing registered fixture, wrong crossing index and wrong route expectation reject the unchanged production verdict; restored controls accept. |
| INV-STORE-IDENTITY | Literal capacity counts `Allocation.memory bits`; every execution and physical safety field uses that identical memory. | Smaller counted prefix remains a true inequality but fails the original capacity consumer; decisive mutations use the actual supplied memory cell. |
| INV-VALUE-DEPENDENCY | Source branch/register values come from evaluated charged setup and physical reads; result/status/register packet conjunction is about the actual Run. | Raw cell 207 changes access packet 1 to 2; rank scalar cell 2 changes packet 2 to 0; select scalar cell 0 changes packet 1 to 0, rejecting the same original packet predicate. |
| INV-SEMANTIC-NONVACUITY | Exact halted result/register/receipts and reader packet/length/frame are derived from primitive evaluation; no advertised semantic field is True. | Each field-to-True constructor compiles, but its same required projection fails with a pinned semantic error; wrong route with a still-correct answer fails operational route checks. |
| INV-TRACE-EXECUTION | `execute` is literal `run`; public reads equal that run's charged setup and physical controller receipts; category partition uses actual indexed transitions. | Crossing checks identify the actual second-load instruction, before-state request, evaluated address and reply; execution and category projection mutations reject. |
| INV-STORE-AGREEMENT | The quoted attempted-receipt agreement implies equality of the entire supplied-memory Run at the same program/fuel/entry. | Public suppliedMemoryAgreement weakening fails its exact equality consumer; decisive changed-cell controls demonstrate disagreement can change the returned value. |
| INV-READ-BACKING | Expanded operation safety quantifies every indexed receipt, its fitting address, exact addressed memory reply and fitting returned word. | All successful finite fixtures check backing; missing supplied memory produces exact address-0/none fault receipt; safety weakenings reject. |
| INV-WORD-WIDTH | Every member of actual memory is below `2^W`; every prefix through the source budget, transition, final register and returned reply fits the same W under the sole argument-fit premise. | Public memoryWordsFit and all operation safety weakenings; max-representable invalid query fixtures. |
| INV-ADDRESS-WIDTH | Constructor-exhaustive whole-program Fits and all indexed transition safety include dormant operands, registers, branch targets, computed sentinel positions and actual load addresses. | Appended unreachable operand `2^W` rejects whole-program Fits while reachable result and reads remain equal; all three operations are exercised. |
| INV-INSTRUCTION-ATOMICITY | Fixed code is the existing primitive ISA after Structured compilation; each counted transition is one accepted primitive, with execution-derived category count. | Exact program-length/category consumers and whole-program operand controls constrain actual code; no shared ISA/evaluator modification. |
| INV-PROGRAM-ACCOUNTING | The quoted capacity includes all three literal instruction encodings and 8274 scratch/control words; metadata is in the 207-word header and charged loads. | Remove code or scratch charge separately; each weaker true constructor fails the unchanged complete-capacity consumer. |
| INV-ORACLE-INDEPENDENCE | Validator expected packets use original List access/rank/select specifications or fixed independent literals; implementation output is only the tested value. | Wrong expected packet mutation must reject the production runCase verdict, while unchanged/restored expectation accepts. |
| INV-VALIDATION-REACH | Main validator runs `program`/`source`/`initial` from final Source against `Allocation.memory`; checked `runArray_toArray` equates execution to actual `run`. | Full main cases and exact request/address crossing witnesses execute the new allocation/program; retained route-v1 artifacts are explicitly historical. |
| INV-ALL-SIZE | All three API equalities and canonical reader/store/space/width fields quantify every List Bool and every Nat; no optional compact readiness or size dispatch premise. | Empty/tiny/threshold fixtures supplement the universal proofs; public API, reader, width and validArgumentFits weakenings fail. |
| INV-PROOF-SEPARATION | Canonical logical stores and directory proofs are consumed only by refinement proofs; executable source accepts numeric memory and loaded registers. | Same-program single-cell corruption changes returned packet and actual receipts, with no replacement semantic callback. |
| INV-NO-SYNTHETIC | Result, transitions, reads and costs are projections of one primitive Run, with exact source/compiler simulation; no post-hoc trace supplies those fields. | Physical second-span loads and precise first-load faults are checked by transition occurrence and addressed reply; public execution mutations fail. |
| INV-CATEGORY-SEPARATION | Actual numerical memory/code/scratch capacity, proof-only fields, unit-cost modeled transitions, preprocessing, API guard and Lean host runtime have separate stated scopes. | Public completeCapacity/category/finiteScratch consumers; documented runtime/model caveat and strict claim-policy check. |
| INV-PUBLIC-COMPOSITION | All 23 expanded fields share the original bits, exact counted memory, operation, target, entry and actual Run, with the explicit safety validity domain. | Smaller-memory, access-for-select safety and access-for-reader siblings are independently true and well-typed, but fail the original required object projections. |
| INV-CERTIFICATE-ANTI-BYPASS | Arbitrary-certificate consumers repeat each exact required proposition; the separate inhabitant consumer fixes the advertised theorem type. | All 23 field weakenings, mandatory-field deletion, three siblings and public theorem proposition mutation require constructor success before consumer rejection. |
| INV-MUTATION-REPRODUCIBILITY | Versioned runners, immutable baseline and fixture bytes, exact replacement strings/hashes, independent verdict registry, pinned failing file/line/class, and finally restoration checks are retained. | Public 32 cases and validation five cases include expected-accept controls; resource errors, wrong surfaces and changed fixtures fail; actual committed blobs and fresh checkout must preserve bytes (comparison pending). |
| INV-GLOBAL-PHYSICAL-MACHINE | One pre-execution complete memory, all 39 regular arrays, numerical target-bank descriptors and exact translation for active/dead/sentinel/outside segments feed whole compiled runs. | Canonical expanded reader consumer covers optional-word distinctions; final-allocation raw/component crossings; whole-operation safety and reader sibling rejection. |
| INV-WIDTH-SCALING | One query-independent `Experiment.width n = 32 + 16 * machineWordBits n` bounds memory, code operands, addresses and all safe states; the same W occurs in complete capacity and logarithmic inequalities. | Width/memory/safety/capacity consumers prevent an unrelated asymptotic width fact; public weakenings and dormant width controls. |
| REPLAY-EXACT-REGISTRY | Each production registry has a fixed version, nonempty independent names/order/count, exact selected output sequence and executed/expected summary. | Main missing-fixture mutation fails registry comparison; all full omitted runs must execute their exact complete registry. |
| REPLAY-SELECTOR-NONVACUITY | Production wrappers distinguish omitted from explicitly bound empty and reject whitespace, malformed, unknown, padded and incompatible selectors before semantic dispatch. | Eight production selector cases per runner, with exactly one full omitted run and one known focused case; no empty selection can pass. |
| REPLAY-SUBPROCESS-DEADLINE | Existing owned-process helper bounds each child, preserves output/exit/ownership, rejects timeout/output caps and checks immutable bytes/scoped status in finally. | Runtime records retain explicit bounds and exact restoration; Windows ownership is observed; unsupported host branches are not claimed. |

## Verification records and remaining work

Checked mathematical composition and standard axiom inventories:
[capstone build](commands/capstone-build-v1.json),
[public consumer](commands/capstone-public-consumer-v2.json),
[allocation/reader consumer](commands/capstone-allocation-reader-consumer-v1.json).
The non-blind [composition review](PREFINAL_COMPOSITION_REVIEW.md) found no
additional mathematical or same-object omission and identified the temporary
leaf-consumer persistence gap. The exact eight retained consumers have now
passed fresh checks: 52 explicit typed assertions, 68 standard-axiom reports,
no warnings/errors and unchanged before/after hashes in
[leaf-replay-20260912130101742-summary.json](commands/leaf-replay-20260912130101742-summary.json).

Completed finite evidence is documented in [MACHINE_CONTROLS.md](MACHINE_CONTROLS.md)
(12 cases and eight selectors), [EXCEPTION_CONTROLS.md](EXCEPTION_CONTROLS.md)
(four valid parameterized routes and 11 selector/wrong-route controls), and
the three-case final-allocation crossing record
[validation-crossing-v3-first.json](commands/validation-crossing-v3-first.json).
The exception construction deliberately uses valid parameterized component
memory; it does not assert that the canonical tiny-input builder selects those
exception routes. Their canonical global coverage follows from universal proof.

The final allocation's complete 46-case registry passed in 378.344 seconds
through the omitted selector: 43 primitive-run fixtures and three explicit
guarded-API fixtures, including all four whole-operation crossings.
All eight production selectors passed in
[selector-controls-main-v2-final.json](commands/selector-controls-main-v2-final.json).
The five validation-verdict controls passed the exact exit sequence 0/1/2/1/0
for unchanged, wrong packet, missing fixture, wrong crossing and restored;
the wrong-crossing case keeps the correct answer and fails its route/receipt
expectation. All eight selectors also passed in
[selector-controls-validation-v1-final.json](commands/selector-controls-validation-v1-final.json).
Their records report exact bytes/status restoration and no resource failures.

The first public campaign is failed diagnostic evidence: case 27's constructor
used the wrong list-length bound; case 31's consumer exhausted the elaborator
heartbeat budget; the owned full-run deadline interrupted case 32 without a
verdict. Cases 1–26 and 28–30 and the other seven selectors passed. The corrected
generation preserves the actual producer and consumer bytes, fixes the
constructor lemma and uniformly prevents elaborator expansion of program,
Allocation.memory and Experiment.width. None of those original failures is
counted as a semantic rejection.

The corrected final campaign passed all 32 cases and all eight selectors in
592.664 seconds, with no timeout, output cap or resource error. All 32
constructors compiled. Both expected-accept consumers succeeded; the 30
negative consumers failed at their independently pinned semantic projections.
The manifest is
`55DAA6A25A1E74050631EAE23A4FDC0F8FA4A467AFE3BF5759291D444350F821`.
The [full registry record](controls/public_mutations/records/campaign-final-v1-20260912131342256-3b473507-omitted/summary.json)
and [selector record](controls/public_mutations/records/campaign-final-v1-20260912131342256-3b473507/summary.json)
verify 276 source/import/control hashes, all 64 final fixtures, exact restoration,
scoped status and whitespace. Root independently checked the counts,
constructor-success flags, zero resource failures and exact sibling/charge/
public-inhabitant error surfaces from those records. This is worker verification,
not a blind coordinator audit or acceptance.

Pending: final committed candidate, Git-blob/fresh-checkout byte comparison,
strict policy/trust/diff checks and coordinator-scheduled aggregate gate.
Final outcomes will be appended here from exact persisted records. Historical
failed development checks remain labeled diagnostics and are never counted as
successful negative semantic controls.

The theorem is a static representation and constant primitive-instruction
query result under the existing unit-cost word-RAM arithmetic/indexed-access
model. Preprocessing time is not bounded here. The unbounded-Nat encoding guard
is outside the charged run. Lean runtime is separate from the modeled bound.
The 8274-word scratch and fixed code contribution vanish asymptotically after
multiplication by logarithmic W, but can be large on small inputs. This result
does not claim a compressed RRR/FID construction or a new RMQ implementation.
