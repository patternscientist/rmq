Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

PQ1-RS, branch `codex/fully-charged-packed-query-v1`, shared worktree `C:/Users/poin/.codex/worktrees/a84a/RMQ`. Assigned base `067b6ffd350aee08f1496335ce957895f0da3fcc`; governance `4639223bc8130b0ef752270b5cbdd74325abcd60`. The canonical proof-sprint preflight passed with actual runtime RMQ catalog `rmq-coordinator, rmq-proof-sprint, rmq-audit-prompt` and the 13-row matrix was frozen before implementation. Only RankSafety.lean and this matrix/report are changed. RankSource, RankProof, ReaderSafety, ScalarSafety, the ISA, metadata, allocation and width remain unchanged by this leaf. No staging, commits, shared-ledger edits or public-claim updates were made.

## Composition and bounds

Write `w = packedReviewerCellWidth n`, `W = wordWidth n = 32+8*w`, `Q = 2^w`, and `E = metadataEnvelope n = 64*Q^2`. Canonical metadata supplies positive chunk width `c≤w`. Every entered word-loop copy has index `j<8`, so its right-shift count `j*c≤7*w<W`; the mask shift also has `c<W`. The address proof bounds every intermediate in `(value*(c+1)+length)*(c+1)+length`, not merely the final table index. It uses the masked value `value<2^c`, `length≤c`, and `32*E^3<2^W`. The last inequality is the elementary exponent comparison `23+6*w<32+8*w`.

The chunk decoder contribution is at most `c` for every numeric entry and either branch of the target test, including entry zero. Modulo reduces the relevant field below `2*(c+1)` before adding the slice length. Guarded subtraction and division by two then establish the contribution bound. It does not require the table reply to be present or well formed. The source still computes the original exact decoder.

The eight-copy invariant includes fitting data, matching metadata, running status, total and index at most eight, the installed constant one, and `accumulator≤index*c`. Inactive copies preserve this invariant; active copies add at most `c` and advance the index once. The public numeric output bound is `8*w`. Select confirmed that this bound suffices, so no additional table-validity theorem is required for safety. The exact rank value remains supplied by RankProof.

Whole rank executes its existing position clamp before division. Hence `(clamped/wordSize)*wordSize≤clamped≤E`, even when the original position is any fitting word. Canonical word-size and superblock divisors are positive at every size. Each charged reader seed is bounded by `Q`, and the returned logical length by `w`. After the in-word fold, the two decoded seeds plus the word contribution are bounded by `2*Q+8*w≤E`. Missing seeds select the existing skip path with output zero. The close wrapper's `2*n` satisfies `2*n≤packedReviewerCellBound n<Q` by the canonical size/width bounds; long and sparse lengths come directly from matching metadata. Final wrapper safety therefore needs only fitting Data and MetadataMatches.

All proof composition uses actual evaluated states and existing frame/source summaries. Fixed repeat counts, continuation Blocks, and whole-program equality transport are abstracted before specializing the concrete reader and wrappers. These are proof-side parameters. No executable callback, extra source input, new instruction, or altered register ABI is introduced.

## Same-run proposition and allocation identity

`RankExecutionSafety memory W program budget state` expands to all encoded program fields fitting W; final State.Fits; indexed Instruction.Safe and fitting after-state for every actual transition occurrence; State.Fits after every fuel prefix up to the same budget; and, for every positional receipt occurrence, address fit, exact `receipt.reply = memory[receipt.address]?`, and fitting successful reply values. The last clause includes failed attempts and comes from the actual transition occurrence through `run_read_fits` and `run_read_at`.

The four `*Run_safe` consumers combine that complete runtime predicate with exact result, halted status, ordered physical receipts, actual step bound, caller frame, read-only reference trace and numerical output bound. They consume RankProof and Safety on the identical compiled block, appended halt, initial registers, fuel and shapeMemory. The budgets are 9046 for in-word rank, 12308 for close rank and 12307 for long or sparse rank. All dormant fields are checked before `compile_fits` resolves branch and jump PCs.

The allocation consumer uses that same shapeMemory for all three wrappers, joins its payload-capacity theorem and raw word fit, and retains `W≤192*(log2(n+2)+1)`. The semantic reference store is connected by the already checked physical logical-reader producer; no sibling store replaces the memory executed here. Full-query code/scratch accounting, aggregate gates, replay and exact-commit independent acceptance remain root-owned.

## Boundary and dependency consumers

The durable consumers cover all three canonical wrappers on arbitrary fitting Data, independent fixed numerical prefix budgets, empty input, a zero-length/zero-limit word, and numeric entry zero after an absent reply. The empty false-rank word intentionally retains the one zero-length table lookup specified by RankProof and its exact ordered receipts; the proof does not incorrectly erase that read. The word-safe interface is stronger internally than its requested entry contract: after Data.Fits, only logical length needs an additional bound; the masked word and clamped limit need no further arithmetic-safety hypothesis.

## Verification ledger

Final RankSafety.lean artifact PASS cleanly in 7.8346049 seconds with `-DmaxHeartbeats=30000`, emitting local .olean/.ilean. Independent imported expected-type and 16-theorem axiom check PASS cleanly in 6.5903014 seconds with the same cap. The printed trust inventory contains only subsets of `propext`, `Classical.choice`, and `Quot.sound`. Repository-wide trust and native-decision scans return no matches; `git diff --check` and owned untracked whitespace checks pass. The generated .lake check is reproduced below for replay; no mutation campaign is claimed. Development checks were serialized with explicit RS/SS/IC/root handoffs. The shared chunk helpers emitted successfully in 5.13 seconds; later diagnostics narrowed register projection and whole-block conversion issues. A 55.71-second check exposed literal continuation reduction. Subsequent checks lowered the diagnostic heartbeat cap to 30000 and changed the abstraction boundary; the unchanged expensive proof was not retried with a larger budget.

## Proof digestion

Conceptually, scalar safety now follows the same states and read operations as rank correctness. Masking and small loop counters bound addresses; clamping bounds whole-rank offsets; logical-reader bounds reset the numerical range after every charged call. The resulting source judgment is transported to real primitive execution and all of its prefixes.

The live canonical assumptions are fitting initial data and metadata matching the counted shape. The in-word interface additionally states its requested word/length/limit bounds; the internal theorem needs only the length bound beyond fit. No minimum-size, successful-read, readiness, target Safe certificate or answer hypothesis is accepted by a final canonical wrapper. Generic composition lemmas expose reader properties and continuation proofs only to discharge them with the canonical producers.

A skeptical graduate student should ask why the coarse output bound is sufficient for later arithmetic, and whether any real read or empty-case transition was lost. Select consumes the explicit `8*w`/E bounds; exact ordered receipts and indexed raw backing remain in the same-run theorem. The numerical safety proof does not replace RankProof's semantic value theorem, and modeled instruction counts are not claims about executable Lean runtime.

## Proposed design rationale for root

Use a robust numeric decoder bound (`contribution≤c` for arbitrary entries) and the invariant `accumulator≤index*c`, then reset whole-rank bounds using logical seed packets. This avoids reproving canonical table validity inside safety while retaining RankProof's independent exact value and read guarantees. Reject a mere arbitrary-word envelope for shifts and multiplication: explicit chunk index, mask and source-clamp facts are necessary. Keep generic block/evaluation/count parameters and propositional whole-block transport in proof helpers to prevent kernel reduction of fixed nested reader loops. Consequence: one unchanged width declaration supports all rank operands, results, code fields and actual read addresses, with reusable source/output interfaces for select and fringe. No ADD/process policy changed.


## Frozen matrix integrity and exact artifacts

All 13 IDs occur once. Every ID/requirement prefix is byte-identical to the frozen matrix immediately before evidence filling; all four explicit requirements also match the prompt verbatim. Only evidence/status cells changed. No inherited requirement was narrowed. The matrix was created in this shared-worktree task rather than inherited from a committed base blob. The frozen requirement-prefix SHA256 is `2e368c84b78f8bdac92e98d60a0cde8be884fecd9ae4f7bc4ccb010350839cd6`.

- `RMQ/Core/WordRAM/Packed/RankSafety.lean`: SHA256 `96be9dd9816325bd5f5648703677937d5662bf464c7bf2576cd318ca0e451121`.
- `.lake/build/lib/lean/RMQ/Core/WordRAM/Packed/RankSafety.olean`: SHA256 `daabf13cf3c3a13990655e62697d3d8e8020b14bd40fbc554dff2692671f0abb`.
- `.lake/build/lib/lean/RMQ/Core/WordRAM/Packed/RankSafety.ilean`: SHA256 `bebf30692c54f87d6228196a64ebeaaa28b6a0299962ef4f270d3d05227f2191`.
- `.lake/rs-imported-check.lean`: SHA256 `c64cd06c1f64bcaecfcc8a6f41ae60341f71bdddf8094f402cd8edf2e6e7b5cd`.
- `docs/internal/packed_query/PQ1_RANK_SAFETY_MATRIX.md`: SHA256 `2291a8862031b009073cc8cdc1dfa2641d516e10a815a0100cc084fde0f12b8f`.

The full narrow compiler command used the pinned Lean 4.22.0 binary and `LEAN_PATH=$PWD/.lake/build/lib/lean`; no shared read-only cache was written. No source changed after that successful artifact check. Broad Lake/gate, strict design scan, public-claim integration and exact-commit acceptance remain root-owned because this leaf changes only one narrow proof module.

## Complete checked proposition inventory

The following signatures are extracted verbatim from the successfully compiled source. Consumer declarations at the end are in namespace `RankSafetyConsumers`.

```lean
theorem chunkRank_le_chunk (c length entry target : Nat) (hl : length ≤ c) :
    chunkRank c length entry target ≤ c
```

```lean
theorem chunkSlotBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (hc : s.regs (base + 1) < width)
    (shift : s.regs (base + 2) * s.regs (base + 1) < width)
    (cap : (2 ^ s.regs (base + 1) * (s.regs (base + 1) + 1) +
      s.regs (base + 1)) * (s.regs (base + 1) + 1) + s.regs (base + 1) < 2 ^ width) :
    (chunkSlotBlock base).Safe memory width s
```

```lean
theorem chunkRankBlock_safe (base width : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits width) (length : s.regs (base + 1) ≤ s.regs base)
    (cap : 4 * (s.regs base + 1) < 2 ^ width) :
    (chunkRankBlock base).Safe memory width s
```

```lean
theorem chunkSlotBlock_canonical_safe (base n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n))
    (hc : s.regs (base + 1) ≤ packedReviewerCellWidth n)
    (hj : s.regs (base + 2) < 8) :
    (chunkSlotBlock base).Safe memory (wordWidth n) s
```

```lean
theorem chunkRankBlock_canonical_safe (base n : Nat) (memory : Memory) (s : Data)
    (fit : s.Fits (wordWidth n)) (hc : s.regs base ≤ packedReviewerCellWidth n)
    (hl : s.regs (base + 1) ≤ s.regs base) :
    (chunkRankBlock base).Safe memory (wordWidth n) s
```

```lean
theorem rankWordBlock_safe_invariant (shape : CartesianShape) (memory : Memory)
    (reader : Block) (readerSafe : ReaderSafe shape memory reader)
    (readerCorrect : ReaderCorrect shape memory reader) (readerWrites : ReaderWrites reader)
    (regs : Registers) (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (hl : regs 257 ≤ packedReviewerCellWidth shape.size) :
    (rankWordBlock reader).Safe memory (wordWidth shape.size) ⟨regs, .running⟩ ∧
      RankWordInvariant shape ((rankWordBlock reader).eval memory ⟨regs, .running⟩).final
```

```lean
theorem rankWordBlock_safe (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs)
    (_word : s.regs 256 ≤ 2 ^ packedReviewerCellWidth shape.size)
    (length : s.regs 257 ≤ packedReviewerCellWidth shape.size)
    (_limit : s.regs 258 ≤ metadataEnvelope shape.size) :
    (rankWordBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s
```

```lean
theorem rankWordBlock_output_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 257 ≤ packedReviewerCellWidth shape.size) :
    ((rankWordBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 260 ≤
      8 * packedReviewerCellWidth shape.size
```

```lean
theorem rankCloseBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankCloseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size
```

```lean
theorem rankLongBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankLongBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size
```

```lean
theorem rankSparseBlock_safe_bound (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) ⟨regs, .running⟩ ∧
      ((rankSparseBlock logicalReadBlock).eval (shapeMemory shape) ⟨regs, .running⟩).final.regs 360 ≤
        metadataEnvelope shape.size
```

```lean
theorem rankWordBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankWordBlock reader).FieldsFit width
```

```lean
theorem rankCloseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankCloseBlock reader).FieldsFit width
```

```lean
theorem rankLongBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankLongBlock reader).FieldsFit width
```

```lean
theorem rankSparseBlock_fieldsFit (width : Nat) (reader : Block)
    (readerFields : reader.FieldsFit width) (cap : 8280 < 2 ^ width) :
    (rankSparseBlock reader).FieldsFit width
```

```lean
theorem rank_compiled_safety (memory : Memory) (width : Nat) (block : Block)
    (output budget : Nat) (regs : Registers) (size : block.size + 1 = budget)
    (bound : budget < 2 ^ width) (fields : block.FieldsFit width)
    (haltFields : (Instruction.halt output).Fits width)
    (fit : (⟨regs, .running⟩ : Data).Fits width)
    (safe : block.Safe memory width ⟨regs, .running⟩) :
    RankExecutionSafety memory width (block.compileAt 0 ++ [.halt output]) budget
      ⟨regs, 0, .running⟩
```

```lean
theorem rankWordBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) (length : regs 257 ≤ packedReviewerCellWidth shape.size) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260])
      (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankCloseBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankLongBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankSparseBlock_execution_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankWordRun_safe (shape : CartesianShape) (word : List Bool) (target : Bool)
    (limit : Nat) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hword : regs 256 = bitsToNatLE word) (hlength : regs 257 = word.length)
    (hlimit : regs 258 = limit) (htarget : regs 259 = if target then 1 else 0)
    (length : word.length ≤ packedReviewerCellWidth shape.size) :
    let expected := bpChunkedWordRankTraceResultAtSegmentWithStore
      (concreteBPNativeSuccinctRMQGlobalReadStore shape) 21
      (packedFringeChunkBits shape.size) target word limit
    let program := (rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260]
    let actual := run (shapeMemory shape) program (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 502 + 8 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWordWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ 8 * packedReviewerCellWidth shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (502 + 8 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankCloseRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape) shape.size (regs 352)
    let program := (rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 560 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankLongRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    let program := (rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankSparseRun_safe (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    let program := (rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let actual := run (shapeMemory shape) program (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 559 + 11 * logicalReadBlock.size ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem rankWrappers_sameAllocation_safety (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    (shapeMemory shape).length * wordWidth shape.size ≤ 2 * shape.size + allocationRho shape.size ∧
    wordWidth shape.size ≤ 192 * (Nat.log2 (shape.size + 2) + 1) ∧
    (∀ value ∈ shapeMemory shape, value < 2 ^ wordWidth shape.size) ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (560 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩ ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
      (559 + 11 * logicalReadBlock.size) ⟨regs, 0, .running⟩
```

```lean
theorem canonical_wrappers (shape : CartesianShape) (s : Data)
    (fit : s.Fits (wordWidth shape.size)) (hm : MetadataMatches shape s.regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s
```

```lean
theorem canonical_prefixes (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs) :
    (∀ k, k ≤ 12308 →
      (run (shapeMemory shape) ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ k, k ≤ 12307 →
      (run (shapeMemory shape) ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size)) ∧
    (∀ k, k ≤ 12307 →
      (run (shapeMemory shape) ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360])
        k ⟨regs, 0, .running⟩).final.Fits (wordWidth shape.size))
```

```lean
theorem empty_word_zero_limit (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hword : regs 256 = 0) (hlength : regs 257 = 0) (hlimit : regs 258 = 0) (htarget : regs 259 = 0) :
    let program := (rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260]
    let actual := run (shapeMemory shape) program ((rankWordBlock logicalReadBlock).size + 1)
      ⟨regs, 0, .running⟩
    actual.result = some 0 ∧ actual.reads = readerReceipts shape (shapeMemory shape) 21 0 ∧
      RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program
        ((rankWordBlock logicalReadBlock).size + 1) ⟨regs, 0, .running⟩
```

```lean
theorem absent_entry_packet (base n : Nat) (memory : Memory) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth n))
    (hc : regs base ≤ packedReviewerCellWidth n) (hl : regs (base + 1) ≤ regs base)
    (missing : regs (base + 2) = 0) :
    (chunkRankBlock base).Safe memory (wordWidth n) ⟨regs, .running⟩ ∧
    ((chunkRankBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 4) =
      chunkRank (regs base) (regs (base + 1)) 0 (regs (base + 3)) ∧
    ((chunkRankBlock base).eval memory ⟨regs, .running⟩).final.regs (base + 4) ≤ regs base
```

```lean
theorem empty_input_prefixes (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth (SuccinctClassic.cartesianShape []).size))
    (hm : MetadataMatches (SuccinctClassic.cartesianShape []) regs) :
    ∀ k, k ≤ 12308 →
      (run (shapeMemory (SuccinctClassic.cartesianShape []))
        ((rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) k
        ⟨regs, 0, .running⟩).final.Fits (wordWidth (SuccinctClassic.cartesianShape []).size)
```

```lean
structure RankWordInvariant (shape : CartesianShape) (s : Data) : Prop where
  fits : s.Fits (wordWidth shape.size)
  metadata : MetadataMatches shape s.regs
  running : s.status = .running
  total : s.regs 263 ≤ 8
  index : s.regs 261 ≤ 8
  accumulator : s.regs 260 ≤ s.regs 261 * s.regs 34
  one : s.regs 265 = 1
```

```lean
def RankExecutionSafety (memory : Memory) (width : Nat) (program : Program)
    (budget : Nat) (s : State) : Prop :=
  (∀ instruction ∈ program, instruction.Fits width) ∧
  (run memory program budget s).final.Fits width ∧
  (∀ (index : Nat) (t : Transition), (run memory program budget s).transitions[index]? = some t →
    Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
  (∀ index, index ≤ budget → (run memory program index s).final.Fits width) ∧
  (∀ (index : Nat) (t : Transition) (receipt : Receipt),
    (run memory program budget s).transitions[index]? = some t → t.receipt = some receipt →
    receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width))
```


## Independent imported expected-type check

This check imports the emitted module, independently states the expected canonical propositions and fixed budgets, expands every runtime-safety field for the close wrapper, and consumes the public theorems. It is a positive exact-type/dependency check, not a mutation campaign.

```lean
import RMQ.Core.WordRAM.Packed.RankSafety

namespace RMQ.SuccinctFinal.PackedWordRAM
open Cartesian PackedCellProbe Structured SuccinctSpace SuccinctClose

example (shape : CartesianShape) (s : Data) (fit : s.Fits (wordWidth shape.size))
    (hm : MetadataMatches shape s.regs) :
    (rankCloseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankLongBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s ∧
    (rankSparseBlock logicalReadBlock).Safe (shapeMemory shape) (wordWidth shape.size) s :=
  RankSafetyConsumers.canonical_wrappers shape s fit hm

example (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    let expected := packedRankCloseLeaf (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      shape.size (regs 352)
    let memory := shapeMemory shape
    let width := wordWidth shape.size
    let program := (rankCloseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]
    let initial : State := ⟨regs, 0, .running⟩
    let actual := run memory program 12308 initial
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape memory expected.trace ∧ actual.steps ≤ 12308 ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    (∀ instruction ∈ program, instruction.Fits width) ∧ actual.final.Fits width ∧
    (∀ (index : Nat) (t : Transition), actual.transitions[index]? = some t →
      Instruction.Safe width t.before t.instruction ∧ t.after.Fits width) ∧
    (∀ index, index ≤ 12308 → (run memory program index initial).final.Fits width) ∧
    (∀ (index : Nat) (t : Transition) (receipt : Receipt),
      actual.transitions[index]? = some t → t.receipt = some receipt →
      receipt.address < 2 ^ width ∧ receipt.reply = memory[receipt.address]? ∧
      (∀ value, receipt.reply = some value → value < 2 ^ width)) := by
  have checked := rankCloseRun_safe shape regs fit hm
  simpa only [RankExecutionSafety, logicalReadBlock_size, locateBlock_size] using checked

example (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 9 10 11 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSuperSlots shape.size) (packedLongFlagWordSize shape.size) 1 (regs 352)
    let actual := run (shapeMemory shape)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) 12307 ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 12307 ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankLongBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) 12307 ⟨regs, 0, .running⟩ := by
  have checked := rankLongRun_safe shape regs fit hm
  simpa only [logicalReadBlock_size, locateBlock_size] using checked

example (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size))
    (hm : MetadataMatches shape regs) :
    let expected := packedRankRead 13 14 15 21 (packedFringeChunkBits shape.size) true
      (concreteBPNativeSuccinctRMQGlobalReadStore shape)
      (packedSparseSlots shape.size) (packedSparseWordSize shape.size) 1 (regs 352)
    let actual := run (shapeMemory shape)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) 12307 ⟨regs, 0, .running⟩
    actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
    actual.reads = logicalTraceReads shape (shapeMemory shape) expected.trace ∧
    actual.steps ≤ 12307 ∧
    (∀ r, ¬ RankWrapperWrites r → actual.final.regs r = regs r) ∧
    ReadOnlyTrace expected.trace ∧ expected.value ≤ metadataEnvelope shape.size ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size)
      ((rankSparseBlock logicalReadBlock).compileAt 0 ++ [.halt 360]) 12307 ⟨regs, 0, .running⟩ := by
  have checked := rankSparseRun_safe shape regs fit hm
  simpa only [logicalReadBlock_size, locateBlock_size] using checked

example (shape : CartesianShape) (regs : Registers)
    (fit : (⟨regs, .running⟩ : Data).Fits (wordWidth shape.size)) (hm : MetadataMatches shape regs)
    (hword : regs 256 = 0) (hlength : regs 257 = 0) (hlimit : regs 258 = 0) (htarget : regs 259 = 0) :
    let program := (rankWordBlock logicalReadBlock).compileAt 0 ++ [.halt 260]
    let actual := run (shapeMemory shape) program 9046 ⟨regs, 0, .running⟩
    actual.result = some 0 ∧ actual.reads = readerReceipts shape (shapeMemory shape) 21 0 ∧
    RankExecutionSafety (shapeMemory shape) (wordWidth shape.size) program 9046 ⟨regs, 0, .running⟩ := by
  have checked := RankSafetyConsumers.empty_word_zero_limit shape regs fit hm hword hlength hlimit htarget
  simpa only [rankWordBlock_size, logicalReadBlock_size, locateBlock_size] using checked

#print axioms chunkRank_le_chunk
#print axioms chunkSlotBlock_canonical_safe
#print axioms chunkRankBlock_canonical_safe
#print axioms rankWordBlock_safe
#print axioms rankWordBlock_output_bound
#print axioms rankCloseBlock_safe_bound
#print axioms rankLongBlock_safe_bound
#print axioms rankSparseBlock_safe_bound
#print axioms rank_compiled_safety
#print axioms rankWordRun_safe
#print axioms rankCloseRun_safe
#print axioms rankLongRun_safe
#print axioms rankSparseRun_safe
#print axioms rankWrappers_sameAllocation_safety
#print axioms RankSafetyConsumers.absent_entry_packet
#print axioms RankSafetyConsumers.empty_input_prefixes

end RMQ.SuccinctFinal.PackedWordRAM

```

The 16 printed axiom inventories passed with only the standard Lean axioms listed above. The complete output is retained in `.lake/rs-imported-check.log`.
