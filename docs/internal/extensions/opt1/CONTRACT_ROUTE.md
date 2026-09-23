# OPT-1 contract and route evidence

Source/governance: `0e6a00f654abc64f8b68988fa9675b9a839dca2f`.
Phase: contract/feasibility, before compact compiler implementation.
This document proposes a construction for independent review; it is not a
proved compiler, acceptance record, or emitted-code measurement.

## Source facts and the first consumed theorem

`Packed/Structured.lean` defines source `Block` and independent `Block.eval`.
Its `compileAt` expands repeats into a list of ordinary instructions. For a
conditional at base p, it emits branchZero, the nonzero arm, a jump past the
zero arm, then the zero arm. Thus the zero path executes at most 1+T(zero),
and the nonzero path at most 2+T(nonzero). Stopping suppresses subsequent work.
`Compiler.lean`'s `Realizes` retains a primitive `RunsTo` transition list,
exact final data, exact ordered receipts, a length bound, and the continuation
PC when running. Layout addresses must continue to use Block.size.

The first proof target is, for every memory/program/block/base/state hosted at
that base, Realizes of the same source evaluation, finish base+block.size, with
budget T(block), where T has the recurrence frozen in REQ-OPT-BUDGET. The
owned proof will recreate small private composition helpers, since shared
Packed modules are read-only. A standalone segment finishes at code.length
or in a stopped state. Consequently it can be extended to any two fuels at
least T(block), with full Run equality. The original complete run's step bound
comes from the witnessed transitions' length, never merely fuel truncation.

Instantiate Block.seq querySource (.exit 3). Its emitted code is exactly the
existing queryProgram and its size is queryBudget. The proposed 150739 closed
equation still requires kernel checking. Canonical halt/result and safety
follow by rewriting existing queryRun theorems along full Run equality.
This comparison can quantify over arbitrary memory, including malformed
metadata, with no valid-query or successful-load premise.

## Proposed compact emitter

Use the existing Primitive Instruction datatype, evaluator, transition log,
Memory and Registers. No new primitive or alternate machine is proposed.
`compactAt block fresh depth base` is a fixed source compiler; it does not
receive xs, query endpoints, metadata, an answer or a correctness witness.

For source repeat 0, emit no code. For repeat count with count>0, let
c=fresh+2*depth, u=c+1, and L be the recursively emitted body length:

| Relative PC | Actual instruction |
| --- | --- |
| 0 | constant c count |
| 1 | constant u 1 |
| 2 | branchZero c (base+5+L) |
| 3 through 2+L | body compiled at depth+1, base+3 |
| 3+L | arithmetic sub c c u |
| 4+L | jump (base+2) |

The positive loop adds five emitted instructions. Running loop control costs
at most 3+count*(Tcompact(body)+3): two initial constants, count+1 branch tests,
and one decrement and jump for each completed iteration. Faults/halts end the
actual machine and can only shorten the segment. The body must preserve c,u;
subtract executes only after the branch established c>0. Count zero has size
and cost zero. Other constructors keep the original layout schema, resolving
addresses from compact sizes and using the corresponding branch maximum.

The six-instruction historical estimate includes an avoidable scratch reset.
Adding a reset would not restore scratch after an early halt/fault; the model
already requires explicit scratch accounting. Reusable subroutines would
introduce return-address/frame obligations unnecessary for the repeat-only
size reduction. Neither alternative is ruled out by the frozen contract.

## Exact relation and safety obligations

At depth d, relate source and machine data by equal status and equal registers
at every r<fresh+2*d. All source operand identifiers must be below fresh,
including reads, branch conditions and exit registers. maxDestination alone
does not suffice. The body induction uses depth d+1, preserving both parent
loop registers. A source-evaluation congruence lemma propagates this relation
and exact ordered receipts; a source frame theorem preserves fresh registers.
The realized segment retains actual primitive transitions and continuation PC.
Full machine-state equality to the source is not claimed for fresh scratch.

The composed query relation requires exactly equal ordered Receipt lists,
including attempted failures and duplicate occurrences. It does not allow
dropping redundant reads. Positional backing refers to compact transition
indices and folded pre-states, obtained from the common primitive calculus.
Source instruction safety is transported from Block.Safe through the register
relation; loop control requires separate fitted count, fitted c/u identifiers,
positive decrement and fitted target proofs. Final-state equality alone cannot
replace every-transition or every-prefix safety.

`querySource_maxEncodedField = 8270` supplies all original encoded identifiers;
fresh=8271 is the proposed first scratch index. Depth one, if checked on actual
source, needs two added registers: bank 8273, plus PC/status words gives 8276.
Every dormant encoded field is checked, including count constants, targets,
operation tags and register identifiers. Input size does not specialize code.

## Composition and accounting

The compact program remains query-independent, uses initialState and executes
exactly buildMemory xs at wordWidth xs.length. The residual is
allocationWithMachineRho of actual flattened compact encoding length and the
proved finite register bank plus three. Existing buildMemory_with_machine_
capacity_le and allocationWithMachineRho_littleO accept any fixed natural code
and scratch constants. This does not exempt emitted code from measurement.
Prove literal emitted length/encoding recurrences, then independently evaluate
the emitted list and compare with 837572 instructions. The historical 213038
six-wrapper estimate is not evidence of an actual emitted program.

The final inhabited capstone must combine the same actual compact code,
adequate run, original allocation, word width, complete capacity, exact result,
ordered reads and all-prefix/transition safety. It must consume the first
branch bound, retain original aliases, and have independently pinned exact
field consumers. No public-root migration is assigned.

## Review and lifecycle boundaries

RMQ_PROGRAM_PLAN.md C.3 requires C1-C4 gated and blind-audited before builder
construction. Those are the PRE builder contract; OPT-1 does not implement a
builder and cannot satisfy or waive that sibling prerequisite. OPT-1 still
requires review of this evidence-dependent compact route before dependent
implementation. The bound proof is independent of the compact route and may
proceed while review is pending. The full exact-commit candidate audit and
coordinator-scheduled aggregate remain later external phases.

Review must challenge fresh-counter collisions, nested loops, count zero/one,
empty bodies, early halt/fault, branch and code-boundary targets, original-fuel
equality, malformed memory, counted scratch, all encoded operands, and the
consumer's exact guard/object identity. A smaller helper or estimate does not
close any composed target row.
