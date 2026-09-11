# Word-RAM Review Packet

This packet separates three things: the candidate primitive-machine query
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, the earlier traced
payload-access theorem with its `210` charged-trace bound, and
compiled-runtime claims, which neither theorem makes.

## Packed primitive query (candidate)

`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, imported through `RMQPaper`,
has the exact proposition
`RMQ.SuccinctFinal.PackedWordRAM.FullyChargedPackedQueryCapstone`. Its producer
is `fullyChargedPackedQueryCapstone_holds` in
`RMQ/Core/WordRAM/Packed/Capstone.lean`, and its axioms are `propext`,
`Classical.choice` and `Quot.sound`. The theorem has no canonical safety,
correctness, readiness, successful-read or route premise. Status: CANDIDATE,
pending the committed replay campaign, the aggregate gate and a fresh blind
exact-commit audit; nothing here records acceptance.

### Machine

The machine state is a register file, a program counter and a status
(running, halted with a value, or fault); memory is a list of natural numbers.
There are nine instruction forms: `load`, `constant`, `move`, `arithmetic`
(add, sub, mul, div, mod, shl, shr, and, or, xor), `comparison` (lt, le, eq),
`jump`, `jumpRegister`, `branchZero` and `halt`. Each executed instruction is
one step and belongs to one of six categories (memory read, register write,
arithmetic, comparison, branch, control); the step count is the sum of the six
category counts. This is an arithmetic word-RAM: multiplication, division,
remainder, variable shifts and bitwise operations are unit-cost word
operations. Addition, multiplication, Boolean operations and shifts by a
register-held distance are the multiplication model of the word-RAM
literature; integer division and remainder go beyond it and are an explicit
additional assumption, which the span decoder uses (DD-20260911-PQ1-018
records the sources). Rank, select, popcount, local scans and whole controller steps are
not primitive operations. The evaluator computes with natural numbers, but for
representable endpoints the certificate proves, on every executed transition,
that the result fits `wordWidth n` bits, that subtraction does not underflow,
that divisors are nonzero and that shift amounts are below the width. On these
runs the natural-number evaluator therefore coincides with `w(n)`-bit
arithmetic. A load from a missing address faults the machine.

### Allocation and space

For each ordinary `xs : List Int`, `buildMemory xs` is one numeric allocation:
174 metadata words (sizes, widths, counts, layout parameters and segment
descriptors serialized from the shape) followed by the existing packed
allocation of the canonical payload, densely repacked into `wordWidth n`-bit
words. Here
`wordWidth n = 32 + 8 * packedReviewerCellWidth n` and
`log2(n+2)+1 ≤ wordWidth n ≤ 192*(log2(n+2)+1)`. The run takes that memory,
the fixed `queryProgram`, `queryBudget` and `initialState xs.length left right`.
No input values, Cartesian shape, semantic store callback or answer are
machine inputs; query-dependent data come only from the endpoints, the size
and charged loads. The allocation satisfies
`(buildMemory xs).length * wordWidth n ≤ 2*n + allocationRho n` with checked
`LittleOLinear allocationRho`. The complete statement also counts the literal
flattened instruction encoding and 8,271 registers plus three control words,
and stays at most `2*n + queryCompleteRho n` with checked
`LittleOLinear queryCompleteRho`; every register outside that bank is proved
to stay zero. The code and scratch part is roughly 1.68 to 4.2 million words
of `wordWidth n` bits, which exceeds `n` for every `n` below about `2^28`, so
it is lower order only asymptotically.

### Program, budget and width

`queryProgram`, the program of
`RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, is one closed program of
837,572 instructions, independent of `xs` and `n`, and `queryBudget = 837572`.
It is straight-line: it contains forward jumps only and no `jumpRegister`. For
every list and every representable endpoint pair the run halts within at most
837,572 steps. Because the program is straight-line, that budget is its length
rather than a measured cost: the committed valid-query fixtures observe 6,003
steps (`n = 1`) to 16,358 steps (`n = 24`), and every representable invalid
input stops within six guard steps (certificate field `invalidGuardSteps`;
`queryRun_invalid_steps` gives exactly four when `left >= right` and six when
`right > n`). The budget is not claimed tight. Every encoded
field of every instruction, including dormant branch arms and the appended
halt, fits `wordWidth n` for every `n`. Every stored word, allocated or
first-missing address, executed operand, arithmetic result, receipt address
and reply, and the state after every fuel prefix fit the same width.

### Inputs and correctness

Every valid half-open range is representable, and for it the run returns the
packet `scanWindow xs left (right - left) + 1`, the leftmost minimum. The
certificate field `specResult` states this on the run itself, without going
through `queryNat` or the RC6 reference value.
Representable invalid, empty or reversed ranges halt with packet `0` and make
no memory read. The total wrapper `queryNat` equals
`if ValidRange xs left right then some (scanWindow xs left (right - left)) else none`
for all natural endpoints, because endpoints outside the word domain are
rejected by the value-level check `encodeInputs` before any machine step. That
outer check is uncharged, and no instruction bound is claimed for parsing
unbounded integers.

### Reads and provenance

For a valid range, the ordered load receipts of the run are exactly the 174
metadata loads followed by the physical expansion of the canonical logical
trace of the same query: one load for each present logical read, two when its
stored bit span crosses a word boundary, and none for a logically absent or
dead read or a zero-length span.
Repeated logical reads repeat their loads. A representable invalid range makes
no load at all. Each receipt is positionally backed: its transition's
pre-state is the run's state at that index, the instruction is the program's
load at that program counter, and the reply is `buildMemory xs` at the
address. A failed load faults the machine and the canonical run halts, so
canonical runs perform no failing load (certificate field `noFailedLoads`;
`queryRun_reads_reply` proves it for every endpoint pair). Any supplied memory that agrees with
`buildMemory xs` at every read address produces the identical run: result,
steps and trace.

### Relation to the other theorems

The instruction bound is a model theorem about this machine; Lean runtime is
not measured or bounded. It is distinct from the `210` charged-trace
certificate below, which counts ticks on the logical controller trace, and
from the `427` packed-probe bound, which counts structural probes with free
computation between them; it reinterprets neither. Preprocessing time and
space are unbounded and unclaimed.

### Evidence

`RMQ/Validation/PackedQueryContract.lean` independently states each
certificate field as an expected-type consumer of the public alias.
`scripts/packed_query_replay.ps1` weakens one field at a time, requires the
named consumer to fail, restores the tree, and runs the numeric-memory runtime
fixtures; the aggregate gate invokes it on a clean committed tree. The theorem
and the consumer check today. The replay campaign, the aggregate gate and the
blind audit have not yet certified this candidate; their status is recorded in
`docs/internal/packed_query/PQ1_ACCEPTANCE_MATRIX.md`.

## Earlier trace-model boundary

The following sections describe the earlier `210` charged-trace theorem. Its
charge policy is unchanged by the separate primitive-machine candidate.

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

The event language of this theorem does not charge controller dispatch,
input/register access, option tests, arithmetic, branches, fixed-width decode,
local BP scans, candidate merges, trace assembly, or the public validity guard.
The checked `210` result is therefore a charged-trace theorem. It is not a claim
about compiled Lean time or a complete conventional word-RAM instruction
count.

The candidate `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` at the top of
this packet charges those operations for a different execution: its primitive
run returns the same answers and its ordered loads expand the same logical
trace, but over a densely repacked allocation. Its 837,572-step budget does
not reinterpret the `210` trace weight.

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
pwsh -NoProfile -File scripts/packed_query_replay.ps1   # clean committed tree
```

The cost harness reports model events, not wall-clock benchmarks, and the
replay's runtime fixtures report primitive steps and reads. The axiom
inventories, review script and replay are curated regression checks; the
theorem types remain the authoritative evidence.
