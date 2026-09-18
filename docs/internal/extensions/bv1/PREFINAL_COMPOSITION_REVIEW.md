# BV-1 bounded prefinal composition review

Outcome: no additional mathematical or public-object omission found in the
inspected construction. One leaf-consumer persistence gap was found and
subsequently closed by retaining the files and passing their fresh replay,
as recorded in the final resolution section.

This is a non-blind source review by the worker who implemented several leaves.
It is not an exact-commit independent audit, coordinator acceptance, fresh Lean
verification, or final gate. No Lean process or additional agent was launched
for this review. The original30 requirements remain frozen and their OPEN
statuses are not changed by this report. Runtime campaigns that were queued or
underway during review are separate unfinished checks, not mathematical gaps.

Governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Source checkpoint: `645a0502b9da9ad6444edbe44759e1c2c5661f25`, with the explicitly
shared working-tree changes. Exact reviewed identities:

| Source | SHA256 |
| --- | --- |
| RMQ/Core/WordRAM/Bitvector/Capstone.lean | 1C6CD0A85B77FBA7706C77DA87DE358808A24FA661D5635A3C4B3BBF96005D69 |
| docs/internal/extensions/bv1/controls/public_expected_type.lean | FEA8D045EF0A9CB9679949ED8825F2E04A4542C01E8F056A778BB0B474BF7A9E |
| docs/internal/extensions/bv1/ACCEPTANCE_MATRIX.md | 80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24 |
| docs/internal/extensions/bv1/CAPSTONE_SCHEMA.md | 89B40DF3C68CF7FB50903984CC37D519D0A6EC567E4B6FF29E155C302CF927C4 |

## Exact public inventory

The structure has23 marked mandatory fields. The independent public file has23
distinct `c.field` projections, with no missing or extra field names. Each
consumer accepts an arbitrary `c : FullyChargedBitvectorCapstone` and uses that
specific projection; it does not replace it with an implementation theorem.
The separate inhabitant consumer requires
`fullyChargedBitvectorCapstone_holds : FullyChargedBitvectorCapstone`.

| Field | Independent consumer |
| --- | --- |
| completeCapacity | public_completeCapacity_required |
| overheadLittleO | public_overheadLittleO_required |
| widthBounds | public_widthBounds_required |
| memoryWordsFit | public_memoryWordsFit_required |
| readerGeometry | public_readerGeometry_required |
| readerCorrect | public_readerCorrect_required |
| accessCorrect | public_accessCorrect_required |
| rankCorrect | public_rankCorrect_required |
| selectCorrect | public_selectCorrect_required |
| accessExecution | public_accessExecution_required |
| rankExecution | public_rankExecution_required |
| selectExecution | public_selectExecution_required |
| accessSafety | public_accessSafety_required |
| rankSafety | public_rankSafety_required |
| selectSafety | public_selectSafety_required |
| programLengths | public_programLengths_required |
| sourceBudgets | public_sourceBudgets_required |
| stepsBound | public_stepsBound_required |
| categoryPartition | public_categoryPartition_required |
| categoryBounds | public_categoryBounds_required |
| finiteScratch | public_finiteScratch_required |
| suppliedMemoryAgreement | public_suppliedMemoryAgreement_required |
| validArgumentFits | public_validArgumentFits_required |

The source and public consumer were already checked by their owners; the review
read `capstone-public-consumer-v2.json`, which records the persisted consumer
path and exit0. This report does not substitute its own check for that record.

## Complete retained allocation and optional-word geometry

The exact public capacity proposition is:

```lean
∀ bits : List Bool,
  ((Allocation.memory bits).length +
    ((program .access).map Instruction.encoding).flatten.length +
    ((program .rank).map Instruction.encoding).flatten.length +
    ((program .select).map Instruction.encoding).flatten.length +
    (8271 + 3)) * Experiment.width bits.length ≤
      bits.length + completeRho bits.length
```

`overheadLittleO` projects `LittleOLinear completeRho`. `widthBounds` projects
`log2(n+2)+1 ≤ Experiment.width n ≤ 48*(log2(n+2)+1)` for every natural n.
The literal left side retains all three encoded programs and the complete
numerical memory, rather than a selected payload upper bound standing in for
the executed object.

The source chain is `Allocation.allSegments = Experiment.allSegments ++
rankSegments`, with39 actual arrays: one raw component, sixteen selected
directory arrays for each Boolean target, two shared chunk tables, and four
Jacobson rank sample tables. `body_capacity` in `Space.lean` consumes both target
directory bounds, the exact rank auxiliary payload length, and both shared
table lengths. `data_capacity` adds the207 numerical header words and dense
padding through its208W overhead. `complete_capacity` then adds the literal
code encodings and8274 scratch words. All of these are bounds on the same
`Allocation.memory bits` used by execution.

Logical segment19 is an alias for the raw payload with the rank builder's
empty sentinels. `CompleteLayout.logicalWords_view` proves its flattened bits
equal physical component0, so there is no second raw allocation to charge.
Every active logical view is regular and has first word length below W;
`decode_logicalWords` proves the exact decode at
`207*W + componentOffset + index*stride` with length
`min stride (totalBits-index*stride)`, for every valid word index.
These propositions are derived from actual arrays, including short first words
and trailing empty sentinels, without a supplied regularity/readiness premise.

The public reader consumer quantifies every segment/index through request
registers8192/8193 and, under only the actual target/width metadata equalities,
requires the actual physical reader's running status, packet, length, exact
ordered receipts and frame. Its expanded packet is
`match Allocation.logicalWord ... with | none => 0 | some xs => bitsToNatLE xs+1`.
Consequently a present empty word has packet1 and length0, while absence has
packet0 and length0. `CompleteReader.physicalReader_correct` explicitly handles
active views, inactive segment20, out-of-range indices and outside segments≥23.
The numerical geometry uses the four actual loaded descriptor replies; it does
not assume an unrelated descriptor oracle. `memoryWordsFit` bounds every
member of the complete same memory.

## Same execution, all-natural API and representable safety

The executable definition is literally:

```lean
execute bits operation target argument =
  run (Allocation.memory bits) (program operation)
    ((source operation).size + 1) (initial operation target argument)
```

`program operation` is `(source operation).compileAt 0 ++ [.halt ...]` using
the existing Structured compiler. The source first performs the actual charged
setup; select additionally performs charged target setup. The bodies invoke
the existing primitive rank/select blocks and numerical physical reader.
The source/program depend only on the finite operation, not on bits or query.
The proof-side logical read store is consumed by a physical simulation theorem;
it is not an executable semantic callback.

The three API propositions have no representation, readiness or size premises:

```lean
access bits i = bits[i]?
rank bits target p =
  if p ≤ bits.length then some (Succinct.rankPrefix target bits p) else none
select bits target k = Succinct.select target bits k
```

The API's explicit `queryPacket` word-range guard returns0 outside the machine
input range. `validArgumentFits` proves `argument ≤ n → argument < 2^W n`;
`InterfaceProof` uses the actual execution result in the representable branch
and the independent specification's absence in the unrepresentable branch.
Rank prefixes are inclusive of n at the API boundary; occurrence indices are
zero-based and arbitrary, including absent selects. Both target values are
universally quantified.

Execution fields quantify all natural arguments and require the independently
specified packet simultaneously in `actual.result`, `actual.final.status =
.halted packet`, and the actual result register705/360/513. They additionally
pin exact charged setup/controller receipt lists and bounds132/1450/10030.
Safety is a separate statement for every representable argument, including
representable invalid queries. Each public safety consumer expands all five
`RankExecutionSafety` conjuncts at the exact same allocation/program/initial
state: all dormant instruction fields fit; final state fits; every indexed
transition is safe with fitting after-state; every fuel prefix up to the source
budget fits; and every indexed receipt has a fitting address, exact addressed
memory reply, and fitting returned value. There is no suffix-only or sibling
program substitution in these consumers.

`finiteScratch` strengthens the accounting link with the exact proposition

```lean
∀ memory operation target argument fuel r, 8271 ≤ r →
  (run memory (program operation) fuel
    (initial operation target argument)).final.regs r = 0
```

It covers arbitrary supplied memory and every fuel, not only successful final
runs. Six execution-derived category counts partition actual steps and are
bounded by the same fixed instruction constants. These are modeled steps;
host evaluator time and proof data are not reclassified as payload.

The supplied-memory field assumes agreement at every attempted canonical
receipt, including absent replies, and concludes equality of the entire Run:

```lean
(∀ receipt ∈ (execute bits operation target argument).reads,
  supplied[receipt.address]? = (Allocation.memory bits)[receipt.address]?) →
run supplied (program operation) ((source operation).size+1)
  (initial operation target argument) = execute bits operation target argument
```

That equality includes result, final state, cost, transitions and receipts;
it is stronger than equality of a value or unordered footprint alone.

## Frozen-row coverage and prepared controls

The30 requirement IDs were compared in the following groups. This is a source
mapping, not a change to their acceptance statuses.

| Frozen rows | Inspected composition |
| --- | --- |
| REQ-BV-ALLOC; INV-STORE-IDENTITY; INV-PROGRAM-ACCOUNTING | Literal complete capacity, both directory capacities, four rank tables, shared tables, header/padding and finite scratch links above |
| REQ-BV-OPS; INV-ALL-SIZE; INV-PUBLIC-COMPOSITION | Unconditional API equalities, actual execution packets, explicit representability boundary and same bits/memory/program objects |
| REQ-BV-RUN; INV-READ-BACKING; INV-WORD-WIDTH; INV-ADDRESS-WIDTH; INV-WIDTH-SCALING | Fixed programs, exact halted result/receipts, complete positional safety, numerical metadata/address bounds and logarithmic W |
| REQ-BV-REUSE; INV-INSTRUCTION-ATOMICITY; INV-GLOBAL-PHYSICAL-MACHINE | Actual Packed primitives/span reader/Structured compiler, complete canonical descriptor translation including dead/sentinel cases |
| INV-VALUE-DEPENDENCY; INV-SEMANTIC-NONVACUITY; INV-PROOF-SEPARATION | Executable branches consume actual registers loaded from memory; logical semantics remain proof-side; singleton changed-cell controls check returned packets, not merely changed logs |
| INV-TRACE-EXECUTION; INV-STORE-AGREEMENT; INV-NO-SYNTHETIC; INV-CATEGORY-SEPARATION | Actual Run-derived transitions/receipts/categories, full supplied-store equality, model/runtime distinction |
| CHK-BV-CONTROLS; INV-ORACLE-INDEPENDENCE; INV-VALIDATION-REACH | Main46 registry uses actual Source programs/Allocation memory and independent List packets; exact crossing witnesses; valid parameterized long/sparse exception controls |
| REQ-BV-JOIN; INV-CERTIFICATE-ANTI-BYPASS | Unconditional23-field capstone and independent23 projections plus inhabitant; immutable constructor-first public mutation fixtures |
| INV-MUTATION-REPRODUCIBILITY; REPLAY-EXACT-REGISTRY; REPLAY-SELECTOR-NONVACUITY; REPLAY-SUBPROCESS-DEADLINE | Versioned production registries, strict selector behavior, bounded owned children, exact failure classes and source/restoration hashes; remaining campaigns retain their own execution obligations |

The prepared public campaign has32 literal cases, including every field
weakening, deletion, three well-typed sibling substitutions, public theorem
mutation, and code/scratch charge removal. Constructor success must precede
consumer rejection at the unchanged consumer's pinned projection/type line;
resource/heartbeat/depth failures are excluded. Two expected-accept cases and
strict eight-selector replay are retained. This review does not count prepared
fixtures or queued execution as passing mutation evidence.

The main46 validator reads independent List expectations and runs actual new
programs; its four crossing cases require the actual second-span load at the
pinned request/address/receipt. Reader crossing v3 uses final Allocation.memory
and requires observable complementation for its true raw case. The separate
machine controls already retain twelve actual-operation cases and strict eight
selectors, including same-packet-predicate rejection under memory mutation,
empty-memory first-load faults and dormant operand rejection by actual Fits.
The completed exceptional registry runs all four branches with inhabited
parameterized records, actual full Source.select, charged setup and actual
segment12/16 loads. Its memory is a valid parameterized component allocation;
it does not claim the canonical global builder chooses those routes at size3.

## Found evidence gap and resolution status

The current six external consumers are persisted under bv1, including the
expanded public consumer and allocation/reader consumer. Normalization and
AllocationFacts have retained script consumers. However, eight older successful
leaf typed/axiom checks still named temporary files outside the worktree:
RegularLayout types and dependency diagnostics, SelectSemantics, RankSemantics,
RankLayout, GenericSelectSafety, CanonicalSelectSafety and ScratchFrame.

After the mathematical review, the coordinator authorized exact copies into
`controls/leaf_consumers/` plus `LEAF_CONSUMER_REPLAY.md`. All eight files were
available and copied without byte conversion. Their current source/destination
SHA256 values match; six also match complete consumer text preserved in their
leaf documents. The original records did not hash the external consumer bytes,
so historical byte identity is explicitly PROVENANCE_UNCERTAIN. No historical
identity is invented. The manifest pins current bytes and prepares one exact
eight-case serial replay at the new paths, requiring an exclusive build slot.

Thus the artifact-persistence gap is repaired in the working tree, while fresh
replay of those retained files remains required. This does not undermine the
already persisted and checked final public consumer, but the historical leaf
replay claims should use the fresh records once available. No further
mathematical/object gap was found in this bounded inspection. Root retains
integration, final gate, exact-commit audit and acceptance.

### Subsequent persistence-gap resolution

The exact eight retained consumers subsequently passed fresh checks at their
repository paths: `commands/leaf-replay-20260912130101742-summary.json` records
all8/8,52 typed assertions,68 standard-axiom reports and unchanged before/after
consumer hashes. `LEAF_CONSUMER_REPLAY.md` records the exact per-case commands,
durations and provenance. This closes the current persistence/replay gap;
historical temporary-byte identity remains explicitly uncertain. It does not
change this review's non-blind scope or confer coordinator acceptance.
