# PQ1-R frozen acceptance matrix

Base: b0af10d14121c7b11a7d3eb7cb1515c618a0da4b. Governance: 4639223bc8130b0ef752270b5cbdd74325abcd60. Branch: codex/fully-charged-packed-query-v1. Shared worktree; no staging or commits.

## Frozen source and join

RankWord fixed inputs256..259, out260, scratch261..310; whole rank352..359, out360, scratch361..370. Reader is a fixed compile-time Block with ReadInterface correctness and writes hypotheses. Target is complete source value and ordered receipts plus ReadOnlyTrace, register frames and actual generic-compiler runs. Lead owns concrete ReaderCorrect and later arithmetic safety/select/LCA integration. No independent write slot is available: all three sibling tasks are doing required disjoint leaves, while this worker closes the dependent rank chain.

## Verbatim frozen requirements

- REQ-R-FOLD: Under ReaderCorrect shape memory reader and ReaderWrites reader, prove the fixed rankWordBlock returns exactly bpChunkedWordRankTraceResultAtSegmentWithStore at segment21, chunk width from canonical metadata, target encoded as0/1, on arbitrary input bits and limit. Actual ordered receipts equal logicalTraceReads of that old trace, and prove ReadOnlyTrace for that trace so no primitive/synthetic event is discarded. Cover zero limit, ragged words, zero-count boundary behavior and all up-to-eight chunks. No hypothesis that the eight-copy loop already matches the specification.

- REQ-R-WHOLE: Prove rankBlock agrees with WordRAM.packedRankRead for all supplied numeric geometry and canonical metadata, on every position, without successful-read hypotheses. All three seed reads occur before presence guards, and the missing-seed branch returns0 after those reads. Derive canonical rankCloseBlock, rankLongBlock and rankSparseBlock exact values/ordered receipts for every shape and position on the same memory, with canonical metadata bank and reader hypotheses only. No empty-size, rare-count-zero, single-word or readiness premise.

- REQ-R-FRAME: Expose sufficient source frame and WritesOnly theorems so rank preserves metadata, caller inputs outside declared output/scratch/reader banks, and any independent select/LCA bank. Prove metadata survives each read/iteration, rather than assuming it for successive calls. Preserve fixed input/output ABI from RankSource; if a semantic defect requires source correction, show the precise defect and repair inside ownership.

- REQ-R-RUN: Use the generic compiler theorem on these exact source blocks to obtain actual hosted/standalone or appended-halt execution results, ordered raw receipts and uniform primitive instruction budgets from the proved source size. No cost charged as a rank/chunk/domain macro. Each canonical wrapper needs a typed actual-run consumer; static-width safety is explicitly a later join, not an assumption used to obtain value or budget.

- CHK-R-LEAN: Narrow module and independently spelled expected-type consumers, plus empty/ragged/missing-seed boundaries. Hygiene and whitespace checks; no native_decide, semantic callback in program, or claimed full-machine safety without proof.

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;

## Evidence ledger

| ID | Evidence | Status |
| --- | --- | --- |
| REQ-R-FOLD | Surface W below, proved by numeric one-iteration agreement and induction on the actual repeat count, then instantiated at eight; consumed by word machine, whole rank, and ragged consumer. | Closed |
| REQ-R-WHOLE | Surfaces R and C below quantify over all registers/geometries/positions with only the stated metadata/reader/Boolean encoding hypotheses. Three unconditional seed evaluations precede the presence guards. Missing-seed machine consumer retains all three receipt lists. | Closed |
| REQ-R-FRAME | Source and actual-run frames quantify over every register outside the explicitly defined write predicates. Metadata preservation is derived from those frames at initialization, every seed call and every iteration. | Closed |
| REQ-R-RUN | Surface M below relates each exact source block to its appended-halt Primitive.run on the same memory; bounds are source.size + 1, specialized to the five literal formulas. Each canonical wrapper has an independently spelled sameAllocation actual-run consumer. | Closed |
| CHK-R-LEAN | Final RankProof.olean/.ilean and imported explicit-type consumers passed cleanly. Four boundary declarations are kernel checked. Ten axiom inventories contain only the standard three axioms. Final hygiene/UTF-8/whitespace evidence is in the report. | Closed |
| INV-STORE-IDENTITY | All source proofs use one G = concreteBPNativeSuccinctRMQGlobalReadStore shape and one memory argument. SameAllocation consumers pin the compiled run and receipt translation to shapeMemory shape. ReaderCorrect is the assigned physical-reader refinement premise, not a second store or rank-exactness premise. | Closed |
| INV-VALUE-DEPENDENCY | Active iteration output is actual prior accumulator plus bpChunkRankOfEntry of the packet decoded from the actual reader output; the iteration induction feeds that value into the next state. Whole result is the two actual decoded seeds plus that fold. Exact source and actual-run value equalities constrain the returned value itself. | Closed |
| INV-TRACE-EXECUTION | Source reads equal logicalTraceReads of the exact old trace, and the compiler gives equality with the actual run reads. ReadOnlyTrace is proved separately, preventing non-read logical events from being silently discarded. List equality retains order and multiplicity. | Closed |
| INV-READ-BACKING | ReaderCorrect fixes each inlined reader's receipts to readerReceipts shape memory at its actual segment/index registers. Those receipts use reviewerLogicalSpan and spanAttemptReceipts on that same memory. Rank preserves this sequence through actual Primitive.run; it introduces no synthetic reads or sibling memory. | Closed |
| INV-ALL-SIZE | No positive size, successful seed, nonzero width/divisor, full-word length, divisibility, rare-count or readiness premise occurs in W/R/C/M. Empty, ragged, zero remaining count, and missing-seed consumers are checked. | Closed |
| INV-PROOF-SEPARATION | The executed syntax takes only a fixed compile-time reader Block and numeric register inputs. Shape, List Bool words, canonical store and refinement proofs occur only in theorem specifications. Numeric decoder equivalence connects scalar actions to those specifications. | Closed |
| INV-INSTRUCTION-ATOMICITY | The source uses ordinary scalar actions/branches and literal repeated blocks, expanded by compileAt. The reader is inlined and charged at its full size; no rank/chunk/domain instruction or callback was added. The actual-run bounds count the resulting primitive instruction stream. | Closed |

## Verification plan

Preflight PASS before editing. Development: narrow ChunkArithmetic, RankSource and RankProof checks against local imports; explicit shared Lean slot, warm observed module runs approximately 5-15 seconds, resume any running command. Final: exact UTF-8 frozen-row checks, source artifacts, independent exact-type and edge consumers, theorem dependency inventory, repository hygiene/native scans and tracked/new-file whitespace. Full aggregate build and strict integrated design/range checks belong to lead; no mutation campaign assigned.

## Checked propositions and object composition

Let `G = concreteBPNativeSuccinctRMQGlobalReadStore shape`, `c = packedFringeChunkBits shape.size`, and `R = reader.size`. Every source proposition below uses `actual = block.eval memory ⟨regs, .running⟩`. The common assumptions are `ReaderCorrect shape memory reader`, `ReaderWrites reader`, and `MetadataMatches shape regs`; no rank exactness or successful-read assumption is added.

**W — word source.** `rankWordBlock_source` additionally assumes `regs 256 = bitsToNatLE word`, `regs 257 = word.length`, `regs 258 = limit`, and `regs 259 = if target then 1 else 0`, for arbitrary `word : List Bool`, `target : Bool`, and `limit : Nat`. With `expected = bpChunkedWordRankTraceResultAtSegmentWithStore G 21 c target word limit`, its complete conclusion is:

```lean
actual.final.status = .running ∧ actual.final.regs 260 = expected.value ∧
actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace
```

`rankWordRepeat_source` proves the actual repeated body equals `bpChunkedWordRankTraceFromWithStore G 21 c target word e j (total - j) acc`, assuming the explicitly listed register invariant `RankFoldState ...` and coverage `total ≤ j + cycles`. It is proved by induction on `cycles`, with active and inactive source evaluations. `rankWordInit_source` supplies that register invariant, and `bpWordChunkCount_le_eight` supplies coverage for the literal eight-copy source. No repeat agreement is assumed.

**R — whole source.** `rankBlock_source` adds only `regs 359 = if target then 1 else 0`. Here

```lean
expected = packedRankRead (regs 356) (regs 357) (regs 358) 21 c target G
  (regs 353) (regs 354) (regs 355) (regs 352)
```

and the complete conclusion is the W conjunction with output register `360`. Thus bit length, word size, blocks per superblock, all three segment numbers and position are arbitrary supplied numeric inputs. `rankSeeds_source` gives running status, the initialized geometry and output zero, all three exact packets and the word's actual length, and exactly the ordered concatenation of the super, block and word receipt lists. `rankFinish_options` covers all eight option combinations; only the all-present case invokes the proved word fold and adds the two decoded seeds.

**C — canonical sources.** `rankCloseBlock_source`, `rankLongBlock_source` and `rankSparseBlock_source` have the common reader/metadata assumptions only. Their expected results are respectively:

```lean
packedRankCloseLeaf G shape.size (regs 352)
packedRankRead 9 10 11 21 c true G
  (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
packedRankRead 13 14 15 21 c true G
  (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
```

Each concludes running status, exact output `360`, exact translated ordered reads, and `ReadOnlyTrace` of its expected trace. These are obtained from the actual scalar metadata prefix followed by R, not by assuming canonical wrapper correctness.

**M — actual primitive runs.** Each `*_machine` theorem forms `actual = run memory (block.compileAt 0 ++ [.halt output]) fuel ⟨regs, 0, .running⟩` and concludes:

```lean
actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
actual.reads = logicalTraceReads shape memory expected.trace ∧ actual.steps ≤ fuel ∧
(∀ r, ¬ allowed r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace
```

| Exact block | Output | Fuel | Allowed writes |
| --- | ---: | --- | --- |
| `rankWordBlock reader` | 260 | `502 + 8 * R` | `RankWordWrites` |
| `rankBlock reader` | 360 | `552 + 11 * R` | `RankWrites` |
| `rankCloseBlock reader` | 360 | `560 + 11 * R` | `RankWrapperWrites` |
| `rankLongBlock reader` | 360 | `559 + 11 * R` | `RankWrapperWrites` |
| `rankSparseBlock reader` | 360 | `559 + 11 * R` | `RankWrapperWrites` |

`rank_compile_with_halt` consumes `Block.compile_with_halt` for that same block, memory, source state and output register. Source frame evidence comes from `Block.eval_frame` and syntactic `WritesOnly`. The predicates are exactly `RankWordWrites r = (260 ≤ r ∧ r < 311) ∨ (8192 ≤ r ∧ r < 8271)`, `RankWrites r = (256 ≤ r ∧ r < 311) ∨ (360 ≤ r ∧ r < 371) ∨ (8192 ≤ r ∧ r < 8271)`, and the corresponding wrapper predicate with `353 ≤ r ∧ r < 371`. Public source frame and metadata theorems accompany all wrappers.

The three `*_sameAllocation` consumers independently spell the complete M proposition with `memory = shapeMemory shape`, the canonical expected expressions in C, and hypotheses `ReaderCorrect shape (shapeMemory shape) reader`, `ReaderWrites reader`, and canonical metadata. This fixes the same allocation in the actual run and in `logicalTraceReads`.

## Anti-vacuity and boundary evidence

- `rankWordBlock_empty`: numeric word/length/limit/target all zero gives running status, output zero and exactly `readerReceipts shape memory 21 0`. The zero effective limit still performs the reference protocol's one logical chunk lookup; it is not falsely treated as zero copies.
- `rankWordBlock_ragged`: packed value `5`, length `3`, overlong limit `5`, target true is a typed actual-run consumer for the independent logical word `[true, false, true]`. No divisibility or full-word premise is used.
- `rankWordRepeat_zero_count`: eight guard copies with total zero preserve an arbitrary accumulator and issue no reads, proved by the actual loop theorem.
- `rankBlock_missing_seed`: any of the three logical seeds being absent yields actual halted result zero, the full ordered concatenation of all three seed receipt lists, the whole-rank primitive bound, and the frame. It rejects moving presence guards before later seed calls when those calls have observable receipts.
- Present zero-valued words remain distinct from absence: `rankSeedRead_source` returns `logicalPacket`, the present packet is `bitsToNatLE word + 1`, and the all-present branch of `rankFinish_options` is proved even when a decoded seed is zero. Packet decoding is consumed by the value theorem, not just a log theorem.
- The source-to-machine consumers project the returned result, raw reads and frame independently. Replacing them with a sibling memory, a result-only assertion or a read-list-only assertion cannot satisfy their checked expected types. No mutation campaign or finite exhaustiveness claim is made.

## Final verification ledger

Final source HEAD is `067b6ffd350aee08f1496335ce957895f0da3fcc`; RankProof is an uncommitted worker-owned addition. Its SHA-256 is `12991004ce78b86d8dcd114a2dc7d441c391f8a616522bfef785b4ed0c2ab1cd`. RankSource and ChunkArithmetic were independently checked and included by the lead in that construction checkpoint; their hashes are listed in the report and remain unchanged.

The final narrow source artifact command and imported expected-type/axiom check passed cleanly in roughly ten seconds combined. The importer independently spelled all three canonical actual runs on `shapeMemory shape` and the full arbitrary-geometry source type. Ten inspected theorem dependencies were exactly `[propext, Classical.choice, Quot.sound]`. Full repository hygiene/native scans found no matches; tracked diff and untracked owned-file whitespace checks passed. All twelve complete frozen requirement rows match the canonical prompt/gate source in strict UTF-8, with unique IDs and no changes. An initial checker incorrectly included line terminators or neighboring bullets; correcting the extraction boundaries established equality without modifying any frozen row.

Development diagnostics exposed expensive definitional reduction of literal repeated source during proof conversion. Earlier ended/cancelled diagnostics were not counted as passes. The final proof abstracts initialization, repeat count and continuation blocks in private composition lemmas, then instantiates the unchanged fixed source. A bounded full-module check passed in 3.80 seconds before final artifact emission. Only one Lean process held the shared slot at a time. No broad build, aggregate gate or mutation replay was run: these are not assigned to this narrow leaf, and the lead owns integrated certification.
