# PQ1-IC frozen acceptance matrix

Base: 067b6ffd350aee08f1496335ce957895f0da3fcc. Governance: 4639223bc8130b0ef752270b5cbdd74325abcd60. Role preflight PASS. Source edits restricted to InteriorCandidateProof.lean and same-order InteriorSource.lean factors; root owns integration and design-ledger updates.

All thirteen requirements below are frozen before implementation. Final consumer: full close LCA consumes the complete interior range candidate on shapeMemory; full query scalar safety remains explicitly outside this leaf.

## REQ-IC-MIN

- REQ-IC-MIN: Prove interiorMinBlock computes packedMinCandidateComputation exactly from all four entry reads in order, including maxRel's presence check, guarded natural subtraction, missing fields and exact candidate positions. Derive canonical entry-count/width/base inputs from metadata. No successful-read assumption.

Checked evidence: `interiorMinBlock_source` proves the complete common source proposition below with `B = interiorMinBlock reader` and `C = packedMinCandidateComputation shape.size (regs 768)`. The minimum pipeline consumes `interiorReadBlock_spec`, whose exact packet708 is `(entryExecution.value.map (·+1)).getD 0` and whose actual receipts are `entryExecution.reads.flatMap (fun read => readerReceipts shape memory 20 read.1)`. Baseline, minRel, maxRel and argOffset run in that order with metadata-derived counts, widths, bases, and indices. The final packet decoder proves all sixteen Option combinations: if any of packets769..772 is zero the candidate is none; otherwise its score is `regs769-1+(regs770-1)-regs33*regs35` and position is `regs768*regs33+regs772-1`, exactly the reference summary map. Intermediate metadata and saved packets follow from frame theorems.

Consumer chain: actual logical reader -> canonical entry reader -> four-entry minimum -> local/global spans -> two-span calls -> full range -> primitive compiled run. Anti-vacuity outcome: `interiorMinFinish_missingMax` checks that `regs774=1 ∧ regs771=0` forces the actual candidate to none and adds no reads, irrespective of other fields; `interiorMinPacketCandidate_decode` covers every other missing-field pattern. The whole minimum theorem retains all four entry executions even when an earlier field is absent. No successful-read hypothesis. Status: Closed.

## REQ-IC-SPANS

- REQ-IC-SPANS: Prove interiorLocalSpanBlock, interiorGlobalSpanBlock, interiorLocalTwoBlock and interiorGlobalTwoBlock match their packed FlatStoreComputation references, including level lookup, decoded level/span arithmetic, missing entries and repeated calls. Derive the seven-chunk bounds for all eight canonical component widths from InteriorReadProof; do not assume source-loop correctness or readiness.

Checked evidence: the full common source proposition holds for each pair: `(interiorLocalSpanBlock reader, packedLocalSpanCandidateComputation shape.size (regs800) (regs801) (regs802))`; `(interiorGlobalSpanBlock reader, packedGlobalSpanCandidateComputation shape.size (regs816) (regs817))`; `(interiorLocalTwoBlock reader, packedLocalTwoSpanCandidateComputation shape.size (regs832) (regs833) (regs834))`; `(interiorGlobalTwoBlock reader, packedGlobalTwoSpanCandidateComputation shape.size (regs864) (regs865))`. These are the four checked `..._source` theorems and independently typed concrete-reader imports.

Canonical bound consumed: for every shape and every `PackedReviewerInteriorComponentTag`, `fixedWidthNatTableMachineChunkCount (packedReviewerInteriorEntryWidth shape.size component) (packedBpCodeWordWidth shape.size) ≤ 7`. The eight tags are covered universally; shared relative-width components use the same proved bound. Actual packet708 drives both optional continuation and level/span decoding. `candidateTwoCalls_source` composes first span, candidate save, second span and left merge with exactly `first.reads ++ second.reads`. Consumer: the complete macro navigator uses these proofs. Anti-vacuity outcomes: all none/some lookup branches are proved, no readiness premise is introduced, repeated calls remain repeated in list append, and the actual tie machine retains the left value. Status: Closed.

## REQ-IC-RANGE

- REQ-IC-RANGE: Prove interiorRangeBlock_source for every canonical shape and arbitrary startBlock/count, covering zero, one-macro, adjacent-macro, global middle and trailing-right routes. CandidateOfRegs7000 equals the exact packedInteriorRangeMinComputation result, and actual receipts equal logicalTraceReads of flatStoreExecutionTraceResultAtSegment20 of that same execution. Prove ReadOnlyTrace separately. Preserve every repeated read and leftmost equal-score merge.

Checked evidence: `interiorRangeBlock_source` has the exact complete source proposition quoted below; `C = packedInteriorRangeMinComputation shape.size (regs896) (regs897)`, with arbitrary shape/start/count. `interiorRangeBlock_sameAllocation` replaces memory by `shapeMemory shape` and reader by `logicalReadBlock`, discharging both reader hypotheses. `interiorRangeCrossProgram_source` proves the adjacent, global-middle-only, and global-middle-with-right computations for abstract local/global children, including their exact final candidate and concatenated actual receipts. Top-level preparation derives all its control premises from metadata, so these are not additional assumptions of the final theorem.

Consumer: this is the exact `InteriorCandidateCorrect` proposition in the lead's LCA proof. Anti-vacuity outcomes: zero count is proved to return none with no reads; positive single-macro and each symbolic cross guard are proved universally. Optional trailing-right reads occur only when right count is nonzero. Equality is on candidateOfRegs7000 and the entire ordered receipt list, and ReadOnlyTrace is a separate conjunct. Equal-score merges retain the left input, including across three candidates. Status: Closed.

## REQ-IC-FRAME

- REQ-IC-FRAME: Expose WritesOnly, source caller-frame and metadata-preservation for the full navigator and useful subroutines. Preserve global candidate7000..7002, scratch7003, caller bank contracts and existing InteriorSource ABI. Show preservation between successive calls, not as independent assumptions.

Checked evidence: each of the six routines exposes `..._writes`, `..._frame`, `..._metadata`. Full propositions: `ReaderWrites reader → (interiorRangeBlock reader).WritesOnly InteriorRangeWrites`; for arbitrary memory/Data/r, `ReaderWrites reader → ¬ InteriorRangeWrites r → ((interiorRangeBlock reader).eval memory s).final.regs r = s.regs r`; and `ReaderWrites reader → MetadataMatches shape s.regs → MetadataMatches shape ((interiorRangeBlock reader).eval memory s).final.regs`. The actual run consumer proves the identical outside-register equality for its final machine registers.

The allowed set is explicitly the union of InteriorMinWrites, local/global span/two scratch, range832..834/864..865/898..911, output7000..7003, and reader8192..8270. Metadata16..189 and caller registers outside these intervals remain unchanged. Candidate7000..7002 and scratch7003 keep their existing output ABI, rather than being falsely framed as unchanged. Consumer: every sequential child call derives its next metadata, preserved controls and saved candidate from the preceding frame; lead LCA caller banks are outside the set. Anti-vacuity outcome: source proofs explicitly transport saved first and left candidates through later calls and then consume those equalities in merge results. Status: Closed.

## REQ-IC-RUN

- REQ-IC-RUN: Derive an actual compiled appended-halt or terminal three-register candidate run with status, candidate result, ordered raw receipts, fixed source-size budget and frame. Instantiate the concrete logicalReadBlock on shapeMemory with all canonical width bounds discharged. Candidate return may use the presence halt tag plus actual final score/position registers; the theorem must bind all three actual projections. No candidate/range domain operation as a single charged instruction.

Checked evidence: `interiorRangeBlock_canonical_machine` is quoted in full below, including actual result, halted status, all three final candidate registers, decoded value, ordered raw receipts, steps, caller frame and ReadOnlyTrace. It consumes `interiorCandidateSpec_machine` -> `Block.compile_with_halt`, the complete source theorem, and syntactic writes. All reader and seven-chunk hypotheses are discharged for the concrete memory/reader; only MetadataMatches remains.

Proved source sizes are minimum `669+32*reader.size`, local/global span `843+40*reader.size` / `838+40*reader.size`, local/global two `1883+88*reader.size` / `1871+88*reader.size`, cross `7588+352*reader.size`, full range `9490+440*reader.size`. At reader.size1068, full source479410 plus halt gives479411. Anti-vacuity outcome: the independently spelled imported type pins the real `run`, literal compiled program, memory, initial state, all value projections and bound; the source-level reference alone cannot inhabit it. The 13-step tie consumer checks actual compiled merge. Status: Closed.

## CHK-IC-LEAN

- CHK-IC-LEAN: Narrow artifact plus independently spelled exact-type consumers, zero count, missing/dead entry, tie and symbolic cross/global branch coverage. Standard trust footprint, hygiene and whitespace checks. Branch coverage may be universal symbolic proof rather than fabricated concrete rare fixtures.

Checked evidence: actual-path InteriorSource and InteriorCandidateProof `.olean/.ilean` emissions passed with zero errors and zero warnings; imported `.lake/IC-expected.lean` passed independent full source/canonical-machine types, five min/span/two concrete-reader types, zero, frame, and universal component width. Fourteen theorem axiom checks contain only propext, Classical.choice, Quot.sound (missing-max needs only propext and Quot.sound). Durable named source/machine/zero/missing-max/dead/tie consumers are in the owned proof file. Symbolic adjacent/global/trailing branch proof closes every route without fabricated fixtures.

Repository trust and native-decision scans return no matches. `git diff --check` passes; owned untracked-file whitespace and strict UTF-8 checks are recorded in the report. The inherited frozen row bytes match the exact governance blob for all seven inherited IDs, and the six assigned row texts match the frozen prompt; no changed IDs. Initial Windows CRLF row encoding was corrected to the exact source blob's LF bytes without wording changes. No mutation campaign is claimed. Lead owns broad/integration gates. Status: Closed.

## INV-STORE-IDENTITY

- `INV-STORE-IDENTITY`: the exact payload/store executed is the payload/store
  counted by the public space theorem; a theorem about a sibling payload is
  insufficient;

Checked evidence: the canonical source/run propositions below use only `shapeMemory shape`, whose definition is `repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)`. The imported `shapeMemory_capacity_le` proves `(shapeMemory shape).length * wordWidth shape.size ≤ 2*shape.size + allocationRho shape.size`; `allocationRho_littleO` proves its sublinear residual. `logicalReadBlock_correct shape` connects exactly this memory to `(concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord?`, and the navigator reference uses that exact store's segment20.

Consumer chain: counted packedReviewerMemory -> same repackWords allocation -> actual logical reader -> entry/min/spans/two/range -> same compiled run. Anti-vacuity outcome: independent canonical machine type fixes memory in `run`, every logicalTraceReads expansion and the source evaluation to the identical shapeMemory object. A sibling-memory theorem cannot replace that instantiated producer. The positional backing consumer below also uses the same memory. Status: Closed.

## INV-VALUE-DEPENDENCY

- `INV-VALUE-DEPENDENCY`: returned values and routing decisions depend on
  actual charged reads, not a semantic answer computed before the reads. When
  the requirement concerns the returned answer or route, evidence must constrain
  that value, state, or route; inequality of an enclosing trace record can be
  satisfied by its log alone and is insufficient;

Checked evidence: the common source proposition and canonical machine proposition constrain `candidateOfRegs 7000 actual.final.regs = expected.value`, not just an aggregate trace record. Entry proof binds packet708 to the value decoded from actual reader packets; field moves769..772 feed the checked four-field decoder. Table packets drive zero tests and level/span arithmetic. Candidate save/merge theorems bind subsequent output to these actual register values. ReaderCorrect is independently proved for the concrete physical loader, not a semantic callback supplied to source.

Consumer: the entire range source and compiled result consume this chain. Anti-vacuity outcomes: missing maxRel forces candidate none; all Option decoder combinations are checked; equal-score actual merge retains the left position. These concern returned values directly. Source scan finds no CartesianShape/FlatStoreComputation/readWord? callback in InteriorSource. No trace-only corruption experiment or mutation campaign is claimed. Status: Closed.

## INV-TRACE-EXECUTION

- `INV-TRACE-EXECUTION`: traces and footprints are derived from the execution
  they describe;

Checked evidence: for `execution = C.run G20`, `InteriorCandidateSpec` returns an actual block eval equality `B.eval memory ⟨regs,running⟩ = ⟨⟨final,running⟩, execution.reads.flatMap (fun read => readerReceipts shape memory 20 read.1)⟩` together with exact candidate value. `logicalTraceReads_flatExecution` identifies this list with the same execution's trace expansion; flatExecution_readOnly proves the logical trace contains only reads. Compiler theorem transports this exact source list to actual machine `Run.reads`, defined by filterMap over actual transitions.

Consumer: canonical machine receipt equality plus the position-preserving read_at theorem below. Anti-vacuity outcomes: two/three call composition appends lists preserving order and multiplicity, including repeated addresses; zero count yields []. No synthetic replay or set-based replacement participates. Status: Closed.

## INV-READ-BACKING

- `INV-READ-BACKING`: every successful read is backed positionally by the
  counted store;

Checked evidence: `interiorRangeBlock_canonical_read_at` is quoted below with its complete position-indexed premise and conclusion. For every actual transition index k and receipt it retains the prefix final state, running pre-state, fetched instruction, actual execute equality, raw-load operands, receipt address, and `receipt.reply = (shapeMemory shape)[receipt.address]?`. Thus when reply is some word that exact counted-memory index is some word; failed replies are retained as well.

Consumer chain: same allocation capacity theorem -> canonical full run -> its transition[k] -> actual raw load -> indexed backing. Exact full-run receipt equality relates these occurrences to the semantic trace without erasing duplicate occurrences. Anti-vacuity outcome: the checked theorem uses transition position and actual prefix, not List.Mem; arbitrary dead entry consumer retains its exact logical and physical receipts. Status: Closed.

## INV-ALL-SIZE

- `INV-ALL-SIZE`: exactness covers all assigned sizes and edge cases without
  hidden readiness or compatibility dispatch;

Checked evidence: canonical source/machine conclusions quantify over every CartesianShape and arbitrary register bank with MetadataMatches only. Neither count positivity, bounded start/count, readiness, successful lookup nor a supplied source-loop-correctness assumption appears. The component chunk bound is universal in shape and all eight tags and is discharged before concrete instantiation.

Consumer: full range reference equality and actual479411 run cover exactly that domain. Anti-vacuity outcomes: count0, arbitrary out-of-range dead entry, every missing-field/table branch, single-macro, adjacent, middle-only and trailing-right cases are all proved. Source word arithmetic safety is explicitly deferred by the frozen prompt and is not advertised here. Status: Closed.

## INV-PROOF-SEPARATION

- `INV-PROOF-SEPARATION`: proof-only fields never carry answers or uncharged
  routing information;

Checked evidence: InteriorSource definitions take numeric register identifiers and child Blocks only; source scan contains no shape, semantic flat computation, canonical read store or readWord? call. Canonical metadata is stored in the counted allocation and supplied in regs16..189. Reader packets and primitive arithmetic/control determine the output. Proof-only InteriorEntrySpec/InteriorCandidateSpec relate source eval values and receipts to the reference but are never arguments to the source evaluator or compiled program.

Consumer: the canonical source and actual machine types fix the same shape-independent block, with shape used only to select counted memory and state the proof. Anti-vacuity outcome: the actual machine expected-type consumer cannot be discharged by a semantic reference equality without the generic compiler transport and the actual source theorem. No trusted or proof-only answer field was added. Status: Closed.

## INV-INSTRUCTION-ATOMICITY

- `INV-INSTRUCTION-ATOMICITY`: each modeled small step performs the familiar
  primitive operation it advertises. A constructor whose evaluator body hides
  recursion, a variable-length scan, repeated rank/select work, decoding, or
  several arithmetic categories is a macro-step unless that work is expanded
  into charged transitions or bounded by an explicitly accepted primitive;

Checked evidence: canonical machine theorem applies `run` to `(interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt7000]`, and its steps count the actual Transition list. Generic source prefixes, child calls, fixed repeats and conditionals compile to the existing load/constant/move/single-arithmetic/comparison/control instruction constructors. The repeated entry loader expands seven guarded copies; nested span/minimum calls expand in source size. Source contains no candidate/range instruction or semantic evaluator callback. Full compiled bound479411 follows from the exact source-size equation, not an assigned macro cost.

Consumer: complete run theorem plus `interiorRangeBlock_canonical_read_at` ties receipts to actual .load instructions and actual pre-states. Anti-vacuity outcome: candidate merge executes a checked13-instruction run and tie result; full source size counts each repeated read child, so replacing it by one uncharged domain action is incompatible with the proved size/compiled program identity. Scalar operation safety and word bounds remain the explicitly separate next join. Status: Closed.

## Common checked propositions and exact objects

All source rows above use this complete universally quantified proposition, with B/C instantiated as explicitly listed in the row:

```lean
∀ (shape : CartesianShape) (memory : Memory) (reader : Block),
  ReaderCorrect shape memory reader → ReaderWrites reader →
  ∀ (regs : Registers), MetadataMatches shape regs →
  let execution := C.run ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20)
  let expected := flatStoreExecutionTraceResultAtSegment 20 execution
  let actual := B.eval memory ⟨regs, .running⟩
  actual.final.status = .running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace
```

The concrete full source and primitive-machine propositions, all live hypotheses, store-composition definitions, frame predicates, exact route guards, and position-indexed read-backing type are quoted in full in `PQ1_INTERIOR_CANDIDATE_REPORT.md`. They are represented by independently typed checked declarations `interiorRangeBlock_sameAllocation`, `interiorRangeBlock_canonical_machine`, and `interiorRangeBlock_canonical_read_at`, and pinned again by the imported `.lake/IC-expected.lean` consumer. The report is part of this matrix's evidence packet, not an alternate acceptance contract.
## Verification ledger

- Development-loop: narrow InteriorSource and InteriorCandidateProof Lean checks, bounded kernel diagnostics after material proof edits; expected 3-20 seconds warm cache, one shared Lean slot, no aggregate build.
- Final-required: actual module artifact and imported independently spelled source/canonical machine types, axiom inspection, zero/missing/tie consumers; expected 5-25 seconds with 120-second ceiling.
- Final-required: strict UTF-8 frozen-row identity, repository trust/native scans, git diff --check, owned-file whitespace scan.
- Lead-owned: strict design policy and exact committed-range check. Full lake build/gate skipped locally because narrow leaf and lead owns integration.
- No mutation campaign assigned or claimed.

Final outcome: all thirteen frozen rows Closed. Source/proof artifacts and imported exact-type checks PASS; fourteen axiom checks use only the standard footprint. Strict byte identity PASS (13 total/7 inherited/0 changed IDs); trust and native scans have no matches; whitespace checks PASS. No mutation campaign. Coordinator acceptance remains required.
