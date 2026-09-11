Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

The frozen requirements and completed evidence rows are in
[PQ1_SELECT_PROOF_MATRIX.md](PQ1_SELECT_PROOF_MATRIX.md). This report covers
PQ1-SEL: every scalar select route, canonical select semantics, ordered physical
reads, register frames, and actual compiled primitive instruction bounds.

## Candidate identity

- Worktree: `C:/Users/poin/.codex/worktrees/a84a/RMQ`; branch
  `codex/fully-charged-packed-query-v1`.
- Assigned base: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`.
- Governing workflow: `4639223bc8130b0ef752270b5cbdd74325abcd60`.
  Project skill preflight passed for `rmq-proof-sprint` using the actual runtime
  catalog `rmq-coordinator`, `rmq-proof-sprint`, `rmq-audit-prompt`.
- Checked HEAD: `067b6ffd350aee08f1496335ce957895f0da3fcc`, plus owned working
  changes and the other workers' disjoint changes. No staging or commits by this worker.
- `RMQ/Core/WordRAM/Packed/SelectSource.lean` SHA256:
  `e0f6ea4655d3241ea067fb0c3361f879688906f367fc2e9e87b008589ce59a07`.
- `RMQ/Core/WordRAM/Packed/SelectProof.lean` SHA256:
  `c81b09fc5f6d7a373b5ef0a51a89feac57d1637a3cc995a9c083f32c336bcecb`.

Both source artifacts are emitted and importable. The report and matrix are the
only subsequent edits; the Lean source hashes remain unchanged.

## Exact canonical result

`buildMemory_setup_select_machine` quantifies arbitrary `xs : List Int` and
`regs : Registers`, with no hypotheses. Let

```lean
shape := SuccinctClassic.cartesianShape xs
expected := packedSelectCloseLeaf
  (concreteBPNativeSuccinctRMQGlobalReadStore shape) xs.length (regs 512)
actual := run (buildMemory xs) setupSelectProgram 91591 ⟨regs, 0, .running⟩
```

Its exact conclusion is:

```lean
actual.result = some (optionNatPacket expected.value) ∧
actual.final.status = .halted (optionNatPacket expected.value) ∧
actual.reads = (List.range 174).map (fun i => ⟨i, (metadata shape)[i]?⟩) ++
  logicalTraceReads shape (buildMemory xs) expected.trace ∧
actual.steps ≤ 91591 ∧
(∀ r, r ≠ 6 → (r < 16 ∨ 190 ≤ r) → ¬ SelectWrites r →
  actual.final.regs r = regs r) ∧
ReadOnlyTrace expected.trace
```

`optionNatPacket value = (value.map (fun position => position + 1)).getD 0`:
zero represents absence, while a present position zero is packet one.
`setupSelectProgram` is exactly the compilation at zero of
`.seq metadataSetupBlock (selectCloseBlock logicalReadBlock)`, followed by
`.halt 513`. Thus the result, status, physical receipt sequence, instruction
count and frame are properties of one actual execution on one memory.

`selectCloseRun_canonical` gives the corresponding select-only run on arbitrary
canonical shapes with `MetadataMatches shape regs`, at budget 91243. The charged
setup theorem removes that premise by executing 174 metadata loads. The input
register 512 is preserved by setup and select. `selectCloseRun_expectedType`
independently spells the concrete program, expanded packet encoding, physical
receipt flatMap, numeric frame union and fuel; it does not simply restate an
abstract correctness predicate.

## Semantic and execution composition

The fixed source keeps input close index 512 and output packet 513. Its helper
definitions name existing scalar instruction sequences while preserving their
order and ABI. Runtime source parameters are fixed blocks and register/segment
indices; there is no runtime shape, semantic store, proof callback or answer.

The select-word theorem fixes the reference to
`bpChunkedWordSelectTraceResultAtSegmentsWithStore G 21 22 c false word occurrence`,
where `G` is the canonical global read store and `c` the metadata chunk width.
For arbitrary input words and occurrences, the same source evaluation has
running status, output register 403 equal to the reference Option packet,
exactly `logicalTraceReads shape memory expected.trace`, and a read-only trace.
The proof tracks the eight guarded copies, including early success, complete
unsuccessful traversal and the intentional one-chunk empty-word fold. An absent
select-table response is decoded as offset zero and remains a present result,
as required by the existing supplied-store protocol.

Entry reads are proved by a four-call sequence before any presence test. The
entry theorem constrains both the presence register and all four decoded fields
when present. The concrete super-entry consumer discharges segment 1, index
register 514 and base 560; the local-entry consumer discharges segment 5, index
register 515 and base 590. Their reference layouts have dead segment 29, matching
the old layout; this proof-side field introduces no runtime read. Missing fields
at any position and present zero-valued fields are distinguished explicitly.

`denseSelectBlock_source` establishes exact equality with
`packedDenseTwoWordSelectRead 0 21 22 c false G (regs 32) (regs 640) (regs 641) (regs 642)`.
It consumes the checked rank-word producer for rank before the offset and whole
word rank, then the proved select-word routine on the appropriate first or
second word. `selectLongBlock_source` and `selectSparseBlock_source` consume the
actual checked rank wrappers and derive relative-read addresses from their
returned rank registers. Rank values remain arbitrary in these proofs; no
rare-count-zero condition is introduced.

The local and super entry branches compose these routines, retaining all
presence cases. `packedSelectCloseLeaf_normalForm` identifies this composition
with the existing reference. Consequently `selectCloseBlock_source` proves,
for `A = (selectCloseBlock reader).eval memory ⟨regs, .running⟩` and
`E = packedSelectCloseLeaf G shape.size (regs 512)`:

```lean
A.final.status = .running ∧ A.final.regs 513 = optionNatPacket E.value ∧
A.reads = logicalTraceReads shape memory E.trace ∧ ReadOnlyTrace E.trace
```

The generic theorem takes `ReaderCorrect shape memory reader`,
`ReaderWrites reader` and canonical metadata. The canonical theorem instantiates
the reader with `logicalReadBlock_correct shape` and
`logicalReadBlock_writesOnly`; its rank dependencies are the checked public
`rankWordBlock_source`, `rankLongBlock_source` and `rankSparseBlock_source`
producers. These proof interfaces are fully discharged in the arbitrary-list
setup machine theorem. There is no readiness, minimum-size, successful-read,
desired-result or exception-count hypothesis in that final theorem.

## Same allocation, frames and primitive budget

The execution memory is `buildMemory xs`, definitionally
`shapeMemory (SuccinctClassic.cartesianShape xs)`. The latter is the repacked
array containing the metadata and `packedReviewerMemory shape`, at the declared
`wordWidth shape.size`. `buildMemory_capacity_le` counts precisely
`(buildMemory xs).length * wordWidth xs.length`, bounded by
`2 * xs.length + allocationRho xs.length`; `allocationRho_littleO` is the existing
overhead result. Setup, the concrete physical reader, select execution and the
space theorem therefore refer to the same array. This leaf adds no payload or
sibling lookup store.

`selectCloseBlock_writes` and `selectCloseBlock_frame` expose this writable union:

```lean
(256 ≤ r ∧ r < 311) ∨ (352 ≤ r ∧ r < 371) ∨ (400 ≤ r ∧ r < 412) ∨
(513 ≤ r ∧ r < 551) ∨ (560 ≤ r ∧ r < 571) ∨ (590 ≤ r ∧ r < 601) ∨
(640 ≤ r ∧ r < 660) ∨ (8192 ≤ r ∧ r < 8271)
```

All other registers, including metadata 16 through 189 and input 512, are
preserved. The frame theorem applies also to stopped input states. Setup adds
only scratch register 6 and the metadata bank. Subordinate entry, word, dense
and exception writes/frame theorems are public for composition by the caller.

For `R = reader.size`, checked source sizes are:

| Routine | Primitive syntax size |
| --- | ---: |
| Entry | `43 + 4*R` |
| Word select | `665 + 16*R` |
| Dense select | `2409 + 50*R` |
| Long exception | `572 + 12*R` |
| Sparse exception | `570 + 12*R` |
| Local select | `3042 + 66*R` |
| Close select | `3666 + 82*R` |
| Concrete close select, including halt | `91243` |
| Charged metadata setup then close select, including halt | `91591` |

The concrete reader has size 1068. Source budget 91242 includes all statically
inlined branch code and fixed copies; halt adds one. Setup adds 348 primitive
instructions. These are upper bounds, with no claim that every route attains
them. No rank, select, chunk or decoding operation is charged as a macro step.

`selectCloseBlock_run` consumes `Block.compile_run`. Its hosted counterpart
uses `Block.compile_correct`, returning `used ≤ 3666 + 82*R`, exactly `used`
actual steps, and final PC `codeBase + (3666 + 82*R)`. The halt consumer uses
the generic checked `rank_compile_with_halt` compiler adapter. All transfers
retain the same values, actual receipt sequence and register frame.

## Validation

The final direct Lean 4.22.0 checks emitted both `.olean` and `.ilean` artifacts:
SelectSource passed in 1.355 seconds; SelectProof passed in 15.477905 seconds,
with exit zero and no warnings. The final source uses default proof options.
Earlier bounded diagnostics identified closed evaluator reduction at composition
boundaries; abstraction over the block/evaluation before instantiation repaired
those proof terms without changing the source behavior or raising final limits.

A separate import of the final artifacts checked independently written canonical
select and setup-plus-select machine types in 5.1657153 seconds, exit zero. It
also printed axioms for the public word, entry, dense, long, sparse and whole
source theorems, the independent canonical consumer, and the full charged setup
machine theorem. Every inventory contains only `propext`, `Classical.choice`
and `Quot.sound`.

Durable in-source consumers cover the explicit canonical machine type and both
concrete entry ABIs. Checked edge propositions cover empty and one-word inputs,
ragged chunks, the eight-copy cap, missing fields in all positions, present zero
fields, absent select-table replies, full unsuccessful traversal, out-of-range
close indices, and actual long/sparse address producers with nonzero ranks one
and two. The general source theorems handle arbitrary rank outcomes and both
dense words; the examples do not replace those proofs.

The repository forbidden trust/import scan and `native_decide`/`Lean.ofReduceBool`
scan both return no matches. Scoped Select scans are also empty. Owned whitespace
checks include tracked source and untracked proof/matrix/report; they have no
whitespace errors. Git's LF-to-CRLF advisories are unrelated to proof validity.
The command ledger in the matrix records exact check roles and scope.

Only one coordinated Lean process ran at a time. No full Lake build, aggregate
gate, mutation campaign or external benchmark is claimed. The frozen contract
assigns broad integration, committed-range whitespace and strict design-policy
checks to the lead. Documentation closure does not invalidate the unchanged
Lean artifact checks.

## Proposed design note for the lead

Retain fixed inlined scalar select source with explicit Option packets and
reference-preserving read order. Presence must remain separate from decoded
zero: each entry performs all four reads before testing presence, while the
existing absent select-table reply still selects the supplied-store default
offset zero. Replacing these with short-circuit reads or treating packet one as
absence would change the specified receipts or value. Naming scalar sequences
is useful for proof composition, but each remains ordinary expanded primitive
code. The syntax-derived bound consequently includes inlined rank/reader work.

This is a proof decomposition and preservation decision within the already
frozen architecture. No new ISA, allocation, process policy or runtime callback
was introduced. The lead owns any shared design-ledger append; this worker did
not edit that ledger or public headline claims.

## Proof digestion and outer scope

The conceptual change is that the reference select protocol is now connected
to a concrete fixed program, including the actual metadata reads that prepare
it. Every selected position or absence packet comes from charged entry, rank,
word and exception reads, and the proof retains their order through compilation.
Missing replies, zero fields, empty/ragged words and nonzero exception ranks
are ordinary cases of the same result.

Generic component theorems have reader and metadata interface hypotheses;
the final arbitrary-list theorem discharges them using the checked physical
reader, rank producers and metadata loader. Its live assumptions are only the
project's Lean/Std logic and the definitions of the fixed machine and canonical
allocation, with no data-dependent premise.

A skeptical graduate student can now inspect the independently spelled machine
consumer to check the actual packet, same-memory receipts and primitive bound.
The next research question is the lead's larger join: how both endpoint selects,
LCA/query semantics and every numeric instruction-safety obligation compose in
one full RMQ execution. Whole-query semantics and global word-width safety are
explicit non-goals of PQ1-SEL, not deferred local acceptance criteria. This
candidate claims the completed select semantic and primitive-budget leaf only.
