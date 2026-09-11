Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.

# PQ1-R compiled rank proof report

Worker: `numeric_span` / PQ1-R, continuing in the shared worktree `C:/Users/poin/.codex/worktrees/a84a/RMQ` on `codex/fully-charged-packed-query-v1`. Base: `b0af10d14121c7b11a7d3eb7cb1515c618a0da4b`. Governance: `4639223bc8130b0ef752270b5cbdd74325abcd60`. Report HEAD: `067b6ffd350aee08f1496335ce957895f0da3fcc`. I performed no staging, commits, branch changes or shared-ledger edits. The lead included the checked RankSource/ChunkArithmetic snapshots in its construction checkpoint; RankProof and this report/matrix remain worker-owned additions for integration.

The complete frozen acceptance matrix is [PQ1_RANK_PROOF_MATRIX.md](PQ1_RANK_PROOF_MATRIX.md). It records all twelve requirements, full source/actual-run propositions, object identity, boundary challenges and verification evidence.

## Result and composition

The fixed word-rank source now agrees with `bpChunkedWordRankTraceResultAtSegmentWithStore` at segment 21. The proof starts with scalar chunk-address and chunk-entry decoder agreement, proves one actual reader iteration, inducts over the actual guarded repeat, and supplies its invariant from the executed initialization. The fixed eight-copy fold is proved; it is not a premise.

Whole rank agrees with `packedRankRead` for arbitrary supplied numeric geometry and every position. `rankSeeds_source` proves all three reads in order, their actual value packets, the word's actual length and the computed geometry. Only after those calls does `rankFinish_options` inspect presence. Every missing-seed case returns zero after all three seed calls; the all-present case consumes the proved word fold and adds the two decoded counters. The canonical close, long and sparse wrappers execute their scalar metadata prefixes and consume that whole-rank theorem.

For each source result, the complete source conjunction is:

```lean
actual.final.status = .running ∧ actual.final.regs output = expected.value ∧
actual.reads = logicalTraceReads shape memory expected.trace ∧ ReadOnlyTrace expected.trace
```

Here `actual` is the evaluation of the exact owned source block on `memory` and the supplied register state. `expected` is the existing logical rank interpreter on `concreteBPNativeSuccinctRMQGlobalReadStore shape`; the complete expected expressions and quantifiers are quoted in the matrix. `ReadOnlyTrace` is proved separately, so translating the old trace does not hide non-read events.

`rank_compile_with_halt` consumes `Block.compile_with_halt` for that same block, source state, output and memory. The five public `*_machine` theorems concern the actual run of `block.compileAt 0 ++ [.halt output]`, returning:

```lean
actual.result = some expected.value ∧ actual.final.status = .halted expected.value ∧
actual.reads = logicalTraceReads shape memory expected.trace ∧ actual.steps ≤ fuel ∧
(∀ r, ¬ allowed r → actual.final.regs r = regs r) ∧ ReadOnlyTrace expected.trace
```

With `R = reader.size`, the bounds are:

| Routine | Output | Primitive instruction bound, including halt |
| --- | ---: | --- |
| `rankWordBlock` | 260 | `502 + 8 * R` |
| `rankBlock` | 360 | `552 + 11 * R` |
| `rankCloseBlock` | 360 | `560 + 11 * R` |
| `rankLongBlock` | 360 | `559 + 11 * R` |
| `rankSparseBlock` | 360 | `559 + 11 * R` |

These are uniform upper bounds obtained from the literal expanded source size. The reader is charged at its complete inlined size; no rank or chunk macro is charged as one instruction. They are not Lean runtime measurements or tight-step claims.

The durable `rankCloseBlock_sameAllocation`, `rankLongBlock_sameAllocation` and `rankSparseBlock_sameAllocation` consumers independently spell all six actual-run conclusions with `memory = shapeMemory shape`. They pin the executed allocation and receipt translation to the same object. The lead can instantiate its already proved concrete `logicalReadBlock_correct` and `ReaderWrites` theorem directly; this rank proof does not modify that physical reader.

## Frames and live assumptions

The source and actual runs preserve every register outside the declared write banks. Word rank may write registers 260–310 and the reader bank 8192–8270. Whole rank may additionally write the word input bank 256–259 and whole scratch/output bank 360–370. Canonical wrappers may also write their parameter bank 353–359. Position 352, metadata 16–189 and independent caller banks outside these ranges are preserved. Public `WritesOnly`, frame and metadata-preservation theorems accompany the routines; successive calls derive their metadata premise from these frames.

The live premises are exactly the assigned `ReaderCorrect shape memory reader`, `ReaderWrites reader`, and canonical metadata. Word rank additionally relates its four numeric input registers to the arbitrary logical word, actual length, limit and Boolean encoded as 0/1. Whole rank relates its target register to that Boolean. Canonical wrappers set their own parameters and target and therefore need no extra parameter or success premise. No positivity, divisibility, full-word, readiness, nonzero count or successful seed premise is used.

The source contains numeric actions and a fixed compile-time reader `Block`. The shape, logical `List Bool` values, old read store and correctness proofs occur only in specifications. In particular, the returned value is obtained by decoding the actual reader packet, computing the scalar chunk result and updating the actual accumulator; it is not precomputed by the old interpreter and followed by decorative reads.

Numeric instruction/operand/address width safety and the full select/LCA/query composition are the explicitly separate subsequent joins in the frozen prompt. This leaf proves actual primitive value/receipt/budget agreement without assuming those safety theorems, and does not claim the complete bounded-word query capstone.

## Boundary and dependency checks

- Empty word and zero limit: `rankWordBlock_empty` proves zero output and the exact segment-21 slot-0 reader receipts. The reference count is one at zero effective limit, so the proof preserves that logical lookup.
- Ragged word: `rankWordBlock_ragged` is a fully typed actual-run consumer for numeric word 5, length 3, limit 5 and target true, against the independent logical word `[true, false, true]`.
- Zero remaining count: `rankWordRepeat_zero_count` proves eight inactive guard copies preserve an arbitrary accumulator and produce no reads.
- Missing seed: `rankBlock_missing_seed` proves actual halted result zero while retaining the ordered receipt lists for all three seed attempts, plus the primitive bound and frame.
- Present zero remains distinct from absence: source seed calls return the `logicalPacket` tag, and the all-present option case still runs the local fold when the decoded seed value is zero.
- The independent canonical consumers mention the actual result, status, ordered reads, bound, frame and logical read-only property, rather than merely the name or truth of an enclosing certificate.

These checked boundaries and typed consumers are the anti-vacuity evidence. No mutation campaign, exhaustive replay registry or unversioned mutation experiment is claimed.

## Verification and source identity

The canonical proof-sprint skill preflight passed before edits, with the actual runtime RMQ catalog and the exact governance ref. RankSource and appended ChunkArithmetic frame lemmas were checked narrowly before the lead's construction checkpoint. Final source hashes are:

| File | SHA-256 |
| --- | --- |
| `RMQ/Core/WordRAM/Packed/RankProof.lean` | `12991004ce78b86d8dcd114a2dc7d441c391f8a616522bfef785b4ed0c2ab1cd` |
| `RMQ/Core/WordRAM/Packed/RankSource.lean` | `1fe17b4bb472adb34c2bc56032f3c584ed93cc7e2504c4b7134190450e23853e` |
| `RMQ/Core/WordRAM/Packed/ChunkArithmetic.lean` | `fb4c68a617629791e9023f8e37c37a802b35ab97cb63e2f2c0af6d3a76cc3d41` |

Final verification used the pinned Lean 4.22 executable and `.lake/build/lib/lean` import cache:

```text
lean -o .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/RankProof.olean
     -i .lake/build/lib/lean/RMQ/Core/WordRAM/Packed/RankProof.ilean
     RMQ/Core/WordRAM/Packed/RankProof.lean
lean .lake/RankProof-expected.lean
```

Both final commands passed cleanly, roughly ten seconds combined. The importer independently spelled the three canonical complete actual-run types on `shapeMemory shape` and the arbitrary-geometry whole-source type. It inspected the axioms of the word/whole source theorems, the word and three canonical machine theorems, and the four boundary consumers. Every inspected result reported exactly `[propext, Classical.choice, Quot.sound]`; no additional trust mechanism was introduced.

The final hygiene scan over `RMQ` and `lakefile.toml` found no forbidden declarations or Mathlib import. The `native_decide|Lean.ofReduceBool` scan found no matches. Tracked `git diff --check` and explicit untracked owned-file whitespace checks passed. All twelve complete frozen rows compare byte-for-byte in strict UTF-8 against their canonical prompt/gate text, with unique IDs and no requirement changes. The initially incorrect row extractor was repaired without changing requirements.

Development checks were narrow and used the shared single Lean slot. Earlier failed or deliberately stopped diagnostics were not counted as validation. A recurring kernel reduction problem arose when proof conversion expanded the literal eight-copy evaluator. The final proof abstracts initializer, repetition count and continuation blocks in private lemmas, then instantiates the unchanged fixed source; the bounded full-module check passed in 3.80 seconds before final artifact emission. Source and imported consumer logs are `.lake/RankProof-artifact.log` and `.lake/RankProof-expected.log`.

No full Lake build or aggregate gate was run because this is the assigned narrow proof leaf. The lead owns the integrated strict design check, committed-range whitespace check and final certification; documentary matrix/report edits do not invalidate the checked Lean artifacts.

## Proof digestion and design note

Conceptually, the work closes the gap between a numeric register program and the existing charged logical rank interpreter. A numeric packet from each actual read now determines the scalar fold state, and those state transitions determine the returned rank. The ordered physical receipts survive the same composition and are identified with the actual compiled run.

In plain English: the fixed machine program now provably performs the intended rank routines, including short and missing-data paths, while preserving its callers' unrelated state. The proof also counts the ordinary instructions used to do that work.

A skeptical graduate student should next examine the lead's arithmetic-width proof and how the fixed concrete reader/rank routines are joined into the complete query on the counted allocation. Those are the subsequent joins explicitly assigned to the lead, not unproved premises hidden in this rank result.

No new semantic model, payload representation or instruction category was chosen. RankSource was factored into named subblocks with the same fixed ABI and checked size formulas to make the proof compositional. No shared design ledger was edited. Suggested note for the existing packed-query decision: preserve the compile-time reader interface and packet/length/ordered-receipt/frame contract, and compose generic proof lemmas before instantiating large fixed repetition. The repetition/continuation abstraction is proof organization only; it does not change the executed program or its charges.
