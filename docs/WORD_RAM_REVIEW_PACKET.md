# Word-RAM Review Packet

This packet distinguishes the fully charged packed primitive query from the
earlier traced payload-access theorem and from compiled-runtime claims.

## Fully charged packed query (PQ1)

`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, imported through `RMQPaper`,
has the exact proposition
`RMQ.SuccinctFinal.PackedWordRAM.FullyChargedPackedQueryCapstone`. Its producer
is `fullyChargedPackedQueryCapstone_holds` in
`RMQ/Core/WordRAM/Packed/Capstone.lean`. The theorem has no canonical safety,
correctness, readiness, successful-read or route premise.

For each ordinary `xs : List Int`, `buildMemory xs` is one numeric allocation.
The same `run` takes that memory, the fixed `queryProgram`, `queryBudget` and
`initialState xs.length left right`. No input values, Cartesian shape, semantic
store callback or answer are machine inputs. Preprocessing densely repacks the
existing canonical packed store and prefixes174 counted metadata words, which
the query reads using charged loads. All-size rank/select, both endpoint
fringes, every interior route and final rank refine the existing half-open
leftmost reference semantics.

The complete capacity statement counts memory cells, the literal flattened
instruction encoding, and8271 registers plus three control words. Their total
capacity is at most `2*n + queryCompleteRho n`, with checked
`LittleOLinear queryCompleteRho`. The same width satisfies
`log2(n+2)+1 ≤ wordWidth n ≤ 192*(log2(n+2)+1)`. Every stored word, allocated
or first-missing address, dormant encoded field, actual instruction operand,
arithmetic result and fuel-prefix state fits that width.

At most837572 actual primitive instructions execute, including guards, loads,
register operations, arithmetic, comparisons, decoding, branches and halt.
The exact six-category partition is derived from the run. Multiplication,
division, remainder, variable shifts and bitwise operations are explicitly
unit-cost word operations in this arithmetic word-RAM model. Rank, select,
popcount, local scans and whole controller steps are not primitive operations.
The instruction bound is a model theorem, not measured Lean runtime.

Every valid mathematical endpoint pair is representable. Representable invalid
pairs halt with rejection and no memory reads. The total `queryNat` wrapper
also rejects endpoints outside the word domain; that outer mathematical check
has no primitive parsing-cost claim. Ordered physical receipts refine the
public logical trace, preserving repetitions and missing replies. Agreement
with the canonical memory at all actual attempted reads determines the entire
run, including its result, transitions and cost.

`RMQ/Validation/PackedQueryContract.lean` independently consumes all30 fields
and the actual public aliases. `scripts/packed_query_replay.ps1` checks the
frozen mutations, exact failure locations, restoration and actual runtime
fixtures, and is reached by the aggregate gate. The theorem and all30 public
consumers check; final replay/gate/blind-audit certification remains recorded
separately in `docs/internal/packed_query/PQ1_ACCEPTANCE_MATRIX.md`.

## Earlier trace-model boundary

The following sections describe the earlier210 charged-trace theorem. Its
charge policy remains unchanged by the additional PQ1 primitive theorem.

## Machine Objects

`RMQ.Core.WordRAM` supplies the first-order payload-read and word-primitive
substrate used by the query components. A `TraceResult` contains a value and an
ordered event list; `TraceResult.toCosted` assigns cost equal to the event-list
length.

`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` proves
that the canonical whole-query trace emits only `readWord` events for attempted
indexed payload-word reads.

The compatibility constructor `syntheticCostOnlyPrimitive` exists in the trace
datatype, but the canonical execution proves that it is absent.

## Canonical Physical Store

The reviewer route has one pre-execution physical word list. Its component
regions have checked offsets, and flattening the list recovers exactly the
public `SuccinctClassic.buildPayload`. The physical supplied-store adapter
translates logical component addresses into this list; it does not append an
uncounted execution payload.

For the physical execution, the checked surface provides:

- refinement to the canonical logical execution;
- preservation of value, cost, event order, failures, repetitions, and
  footprint;
- successful-read backing by an in-bounds physical word;
- complete-execution equality under agreement on the consumed ordered
  footprint; and
- value-level sensitivity to a consumed decisive-word change.

## Operational Provenance

Every indexed read occurrence can be followed from the global trace to its
producing instruction occurrence and prefix-folded state, then to its
component-local occurrence, invocation parameters, source, and global offset.
The source manifest is exhaustive for the canonical payload. Separate
nonvacuity theorems witness every counted source and shared-BP consumer in some
valid closed whole-query execution, while fresh segment `23` is rejected by
the same operational relation and live segment `21` is the fringe chunk table.

This is stronger than event-value membership or a category-only label: the
evidence is attached to the indexed occurrence that was actually emitted.

## Width Discipline

The query-independent reviewer capacity is linear in input size, and its
derived word width has a checked logarithmic upper bound. The same bound covers:

- every stored and returned physical word;
- translated live and sentinel addresses;
- segment encodings;
- query indices;
- word-rank/select operands and results; and
- every address in the consumed physical footprint.

Arithmetic in the present register layer is mathematical `Nat` arithmetic with
explicit fit/no-overflow side conditions. It is not implicit machine-word
wraparound.

## Cost Theorem

The canonical component cap is:

```text
2 * select35 + (2 * rank11 + 2 * endpointFringe37 + interior33) + rank11 = 210
```

The same execution proves:

1. every emitted event is `readWord`, by the strong public theorem
   `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`;
2. the synthetic marker is absent;
3. the `nonSyntheticWeight` sum equals event-list length;
4. that sum equals the same execution's `Costed.cost`; and
5. the sum is at most `210`.

The construction-facing theorem
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`
joins items 2–5 and its own explicit three-constructor event classification to
payload size, physical erasure, read backing, and exact query semantics. The
separate strong theorem in item 1 strengthens that exact same trace; the
capstone's own checked type does not contain the readWord-only conjunct.

## Uncharged Boundary

The event language does not currently charge controller dispatch,
input/register access, option tests, arithmetic, branches, fixed-width decode,
local BP scans, candidate merges, trace assembly, or the public validity guard.
The checked `210` result is therefore a charged-trace theorem. It is not a claim
about compiled Lean time or a complete conventional word-RAM instruction
count.

PQ1 supplies the machine-level strengthening above. Its primitive run refines
this reference query and its ordered reads on a densely repacked allocation;
the837572 instruction bound does not reinterpret the earlier210 trace weight.

## Compatibility

Older readiness, route-split, large-regime, zero-block, and transitional cost
theorems remain available only through the compatibility surface. Their exact
chronology is in
[`digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md).
They are not premises of the canonical reviewer route.

## Checks

```powershell
lake build RMQPaper
lake env lean scripts/wordram_axiom_check.lean
lake env lean scripts/headline_axiom_check.lean
lake exe rmq_succinct_classic_cost_harness
powershell -ExecutionPolicy Bypass -File scripts/review_wordram.ps1
```

The cost harness reports model events, not wall-clock benchmarks. The axiom
inventories and review script are curated regression checks; the theorem types
remain the authoritative evidence.
