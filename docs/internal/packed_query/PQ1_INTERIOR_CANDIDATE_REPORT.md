Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# PQ1-IC: complete interior candidate navigator

Worker `numeric_span`, returning after PQ1-R. Shared worktree `C:/Users/poin/.codex/worktrees/a84a/RMQ`, branch `codex/fully-charged-packed-query-v1`, assigned base `067b6ffd350aee08f1496335ce957895f0da3fcc`; governance `4639223bc8130b0ef752270b5cbdd74325abcd60`. Runtime catalog contains `rmq-proof-sprint`, `rmq-coordinator`, and `rmq-audit-prompt`; the tracked proof-sprint skill and completion gate were applied and role preflight passed. No staging, commits, shared-ledger edits, task rename, branch change, or worktree change by this worker.

Owned changes are `InteriorCandidateProof.lean`, same-order navigator factors in `InteriorSource.lean`, and this report/matrix. The entry-reader proof, actual logical reader, compiler, source frame calculus, and candidate primitives are consumed from the other workers' checked artifacts. Parallel execution was restricted to disjoint proof leaves, with explicit serial Lean-slot handoffs.

## Result and exact interface

Every source routine computes its old flat-store reference result and the physical receipts of that same reference execution. The full source theorem `interiorRangeBlock_source` has precisely these hypotheses and conclusions:

```lean
∀ (shape : CartesianShape) (memory : Memory) (reader : Block),
  ReaderCorrect shape memory reader → ReaderWrites reader →
  ∀ (regs : Registers), MetadataMatches shape regs →
  let actual := (interiorRangeBlock reader).eval memory ⟨regs, .running⟩
  let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
  actual.final.status = .running ∧
    candidateOfRegs 7000 actual.final.regs = expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧
    ReadOnlyTrace expected.trace
```

The two reader hypotheses are discharged by `logicalReadBlock_correct shape` and `logicalReadBlock_writesOnly` in `interiorRangeBlock_sameAllocation`. Its only hypothesis is `MetadataMatches shape regs`. This is the exact source proposition required by the lead's `LCAProof.InteriorCandidateCorrect` interface. The semantic expected value unfolds to `flatStoreExecutionTraceResultAtSegment 20 ((packedInteriorRangeMinComputation shape.size (regs 896) (regs 897)).run ((concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20))`.

The independently written `interiorRangeBlock_canonical_machine` binds the actual halt result, halted status, all three candidate registers, decoded candidate, exact ordered raw reads, fixed step bound, caller frame, and read-only logical trace:

```lean
∀ (shape : CartesianShape) (regs : Registers), MetadataMatches shape regs →
  let expected := packedInteriorRangeMinRead concreteBPNativeInteriorTraceSegments
    (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 896) (regs 897)
  let source := (interiorRangeBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩
  let actual := run (shapeMemory shape)
    ((interiorRangeBlock logicalReadBlock).compileAt 0 ++ [.halt 7000])
      479411 ⟨regs, 0, .running⟩
  actual.result = some (source.final.regs 7000) ∧
    actual.final.status = .halted (source.final.regs 7000) ∧
    actual.final.regs 7000 = source.final.regs 7000 ∧
    actual.final.regs 7001 = source.final.regs 7001 ∧
    actual.final.regs 7002 = source.final.regs 7002 ∧
    candidateOfRegs 7000 actual.final.regs = expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 479411 ∧
    (∀ r, ¬ InteriorRangeWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace
```

The number is a proved uniform bound on primitive transitions, not a claim about Lean runtime or an exact path cost. The source size is `9490 + 440 * reader.size`; `logicalReadBlock.size = 1068`, so the source has size `479410` and the halt-inclusive bound is `479411`.

## Construction and route coverage

The source now exposes numeric prefix and continuation factors for minimum, local/global span, local/global two-span, and full macro navigation. These factors preserve primitive order, registers, branch meanings, and the existing public `...Block reader` ABI. They receive only numeric data and child `Block`s. `CartesianShape`, semantic stores, and `FlatStoreComputation` appear only in proof statements and reference specifications.

`InteriorEntrySpec` binds the actual entry block's packet708 and receipts to `packedInteriorReadNatOf`. `interiorReadBlock_spec` derives it from the checked seven-copy reader. The imported universal bound

```lean
∀ shape component,
  fixedWidthNatTableMachineChunkCount
    (packedReviewerInteriorEntryWidth shape.size component)
    (packedBpCodeWordWidth shape.size) ≤ 7
```

covers every one of the eight component tags. Metadata supplies counts, widths, bases, and BP word width. Minimum uses baseline, minRel, maxRel, and argOffset in that order; maxRel and argOffset share the reference relative-width representation. There is no successful-read premise. The finished candidate is absent if any packet769..772 is zero, including maxRel. Otherwise guarded subtraction computes the reference natural score and exact position. `interiorMinPacketCandidate_decode` checks all sixteen presence/absence combinations against the independent option-valued summary specification.

The five source families below all prove, for arbitrary `shape`, `memory`, `reader`, and registers with `ReaderCorrect`, `ReaderWrites`, and `MetadataMatches`, the full conjunction `actual.final.status = running ∧ candidateOfRegs 7000 actual.final.regs = expected.value ∧ actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace`. Here `actual` is the named block evaluation, and `expected = flatStoreExecutionTraceResultAtSegment 20 (computation.run G20)` with `G20 = (concreteBPNativeSuccinctRMQGlobalReadStore shape).readWord? 20`:

| Source theorem/block | Exact computation and inputs |
| --- | --- |
| `interiorMinBlock_source` | `packedMinCandidateComputation shape.size (regs 768)` |
| `interiorLocalSpanBlock_source` | `packedLocalSpanCandidateComputation shape.size (regs 800) (regs 801) (regs 802)` |
| `interiorGlobalSpanBlock_source` | `packedGlobalSpanCandidateComputation shape.size (regs 816) (regs 817)` |
| `interiorLocalTwoBlock_source` | `packedLocalTwoSpanCandidateComputation shape.size (regs 832) (regs 833) (regs 834)` |
| `interiorGlobalTwoBlock_source` | `packedGlobalTwoSpanCandidateComputation shape.size (regs 864) (regs 865)` |

Local/global span first loads its table entry and branches on the actual packet. Two-span routines load and decode level/span data, call the span routine twice, save the first candidate, and merge it with the second. Both calls retain their own reads, including repeated equal addresses; receipts compose by list append, never by sets or membership.

For full range navigation let `m = macroSize`, `s = startBlock`, `c = count`, `left = m - s % m`, `middle = (c-left)/m`, and `right = (c-left)%m`. The checked universal symbolic split is:

| Guard | Exact reference route |
| --- | --- |
| `c = 0` | `pure none`, no reads |
| `c ≠ 0` and `c ≤ left` | local two-span at `s/m`, `s%m`, `c` |
| crossing with `middle = 0` | adjacent-macro candidate |
| crossing with `middle ≠ 0` and `right = 0` | left local candidate followed by global middle candidate |
| crossing with `middle ≠ 0` and `right ≠ 0` | left local, global middle, trailing right local candidate |

`interiorRangeCrossProgram_source` proves the last three routes for abstract local/global children and consumes their exact value/receipt and syntactic frame specifications. `interiorRangeProgram_source` derives its control inputs from metadata and covers zero/single/cross dispatch. `interiorRangeBlock_spec` substitutes the actual hierarchy, then the source and primitive-run consumers close the full target.

## Frame, backing, and store identity

All six routines expose `..._writes`, `..._frame`, and `..._metadata`. For the full routine the propositions are:

```lean
ReaderWrites reader → (interiorRangeBlock reader).WritesOnly InteriorRangeWrites

ReaderWrites reader → ∀ memory s r, ¬ InteriorRangeWrites r →
  ((interiorRangeBlock reader).eval memory s).final.regs r = s.regs r

ReaderWrites reader → ∀ memory s, MetadataMatches shape s.regs →
  MetadataMatches shape ((interiorRangeBlock reader).eval memory s).final.regs
```

The precise allowed set is the union of the local/global two-span banks, range inputs832..834/864..865, and range scratch898..911. It includes global output7000..7003 and logical-reader bank8192..8270; metadata16..189 and caller banks outside the set are preserved. Candidate score/position/presence are outputs, not registers claimed unchanged. Every successive call obtains metadata and saved/control register preservation from the preceding call's checked frame, rather than independent final-state assumptions.

The concrete memory is definitionally `shapeMemory shape = repackWords (metadata shape) (wordWidth shape.size) (packedReviewerMemory shape)`. Its imported allocation theorem proves `(shapeMemory shape).length * wordWidth shape.size ≤ 2 * shape.size + allocationRho shape.size`, with `allocationRho_littleO`. The executed logical reader is proved correct for that exact memory and canonical global store. No sibling store or reconstructed answer enters the navigator source.

`interiorRangeBlock_canonical_read_at` specializes the generic transition theorem to this same halt-inclusive program, memory, budget479411, and initial state. For every `k`, `t`, and `receipt`, if `actual.transitions[k]? = some t` and `t.receipt = some receipt`, it proves:

```lean
t.before = (run (shapeMemory shape) program k initial).final ∧
  t.before.status = .running ∧ program[t.before.pc]? = some t.instruction ∧
  execute (shapeMemory shape) t.instruction t.before = (t.after, t.receipt) ∧
  ∃ dst addrReg, t.instruction = .load dst addrReg ∧
    receipt.address = t.before.regs addrReg ∧
    receipt.reply = (shapeMemory shape)[receipt.address]?
```

This preserves occurrence position, actual prefix/pre-state, instruction, address operand, and indexed numeric backing for successes and failures. `Run.reads` is the ordered `filterMap` of these transitions. The run theorem also equates this actual list to the flat reference's expanded reads; `ReadOnlyTrace` proves the projection does not discard other logical events.

## Boundary and anti-vacuity evidence

- `interiorRangeBlock_zero`: any canonical shape and arbitrary other registers with count897=0 give running status, `none`, and `[]` actual reads. There is no positive-size or valid-query premise.
- `interiorMinFinish_missingMax`: with constant774=1 and maxRel packet771=0, the actual finishing block gives `none` and no additional reads, regardless of the other packets. The full four-read theorem and all sixteen decoder cases establish that the check is live, not a trace-only claim.
- `interiorEntry_dead_request`: for every canonical component width and arbitrary entry index with `entryCount704 ≤ index707`, the full actual reader returns the canonical dead logical request's packet and exactly its physical receipts. The seven-chunk bound is discharged; no present-entry assumption occurs.
- `interiorNavigator_tie_machine`: for arbitrary equal score and left/right positions, the actual 13-instruction compiled merge retains the saved left candidate. A right-biased equal-score result is inconsistent with its value conclusion.
- Missing local/global lookup entries are covered by the `none` branches of both optional-read composition lemmas and all four universal span/two-span source theorems. Repeated requests remain repeated through exact list append equalities.
- Cross/global coverage is universal over the symbolic route guards above, including arbitrary start/count and all canonical sizes. No fabricated rare fixture is used.

These are checked boundary consumers and universal source refinements, not a mutation campaign. No deletion/mutation replay verdict is claimed.

## Verification

All thirteen frozen matrix rows are Closed. Verification results:

| Check | Outcome |
| --- | --- |
| Full bounded development diagnostic | PASS, 7.85 seconds; new compositional joins checked with 30,000 heartbeats, existing minimum proof retained its default limit |
| Actual-path `InteriorSource.lean` artifact | PASS; zero errors/warnings; `.olean` and `.ilean` emitted |
| Actual-path `InteriorCandidateProof.lean` artifact | PASS; zero errors/warnings; `.olean` and `.ilean` emitted |
| Imported independently spelled exact-type consumers | PASS; source, full canonical machine, five min/span/two routines, zero, frame, and all-component width type |
| Fourteen imported axiom inspections | Only `propext`, `Classical.choice`, `Quot.sound`; missing-max theorem uses only `propext`, `Quot.sound` |
| Strict UTF-8 frozen-row check | PASS; 13 rows, 7 inherited, 0 changed IDs against governance blob and frozen prompt |
| Required repository trust and native-decision scans | No matches |
| `git diff --check` and owned untracked-file whitespace | PASS |
| Source independence scan | No `CartesianShape`, `FlatStoreComputation`, semantic computation, `shapeMemory`, or `readWord?` in `InteriorSource.lean` |

Fourteen unused simp arguments found in the development diagnostic were removed before final artifact generation. The initial strict frozen-row check detected Windows CRLF bytes in inherited rows; those were restored to the exact governing blob's LF bytes without wording changes, and exact byte equality was rerun successfully. This is not a normalized-text substitute for the byte check.

Reproducible narrow commands use the installed Lean4.22 binary with `LEAN_PATH=.lake/build/lib/lean`, compiling each owned module with `-o` and `-i`, then importing `RMQ.Core.WordRAM.Packed.InteriorCandidateProof` in `.lake/IC-expected.lean`. Local logs are `.lake/IC-source-final.log`, `.lake/IC-artifact-final.log` (both empty, clean runs), and `.lake/IC-expected.log` (the fourteen axiom readouts). `.lake/IC-frozen-check.ps1` reads the exact governance blob as strict UTF-8 and compares complete extracted row bytes. These `.lake` files are local validation artifacts; durable statements and all named boundary consumers are in the owned Lean module.

Final source SHA256:

| File | SHA256 |
| --- | --- |
| `InteriorCandidateProof.lean` | `cb7c8baf7f03f82cc2d6d79abf2ea69c800dee23c380cd29eecccdca8d32b014` |
| `InteriorSource.lean` | `177295eb1f5604a236bbe2d339928e0276751b1d8a99460553241cacb3273d37` |

The final imported consumer file spells the full source and canonical-machine types independently, all five minimum/span family result/order types, zero-count consumer, caller frame, and universal component-width bound. Durable source consumers include the same-allocation source and concrete machine theorem. The narrow checks target only the two changed Lean modules and their direct imported consumers. Broad build and gate are skipped here because this is a leaf in an active shared construction; the lead owns integration certification, strict design policy, and the exact committed-range check.

## Proof digestion and proposed design rationale

Conceptually, the navigator proof follows actual register states through charged entry reads, packet decoding, span calls, saved candidates, and left-biased merges. The flat-store computation supplies the independent specification. Generic child-block evaluation equalities allow each call to be composed without asking the kernel to unfold an enormous concrete interpreter term.

In plain English: the fixed primitive program now has a proof that every interior-range route returns the expected candidate and performs exactly the expected reads in the expected order. The proof also identifies the final candidate fields and the registers left untouched.

Live assumptions are canonical metadata at entry and, in reusable generic theorems, the stated correct-reader and reader-write contracts. The concrete wrappers discharge both reader contracts. Arbitrary start/count remain permitted. No readiness, successful-read, array-bound, source-loop-correctness, or semantic-answer assumption is introduced.

The next skeptical question is whether every intermediate arithmetic operand/result of this same full navigator fits the declared word width and obeys safe division/subtraction/shift conditions. This maps directly to the prompt's explicit separate scalar-safety join and non-goal of asserting whole-query scalar safety. PQ1-IC claims the Nat-valued primitive semantics, exact result/trace, frame, and finite instruction bound; it does not claim that pending safety theorem.

Proposed lead design entry: factor numeric source prefixes and child continuations while preserving the public block ABI and primitive order; prove exact source semantics bottom-up and instantiate the unchanged generic compiler only after the full source joins. An alternative proof by unfolding the whole interpreter caused severe kernel conversion growth; theorem-level eval equalities and pure flat-bind run equations resolved it without new trusted constants, heartbeat increases, semantic callbacks, or a weaker endpoint. No new ADD/process policy was introduced. Lead owns the shared design ledger and public frontier wording.
