# BV-1 final capstone schema

Status: implementation specification. No constructor or acceptance closure is
claimed by this file. The original 30-row acceptance matrix remains frozen.
This schema fixes the final proof composition and typed consumer surfaces
before creating `Capstone.lean`.

All fields use `Allocation.memory bits`, `Experiment.width bits.length`,
the literal `program operation`, `source operation`, `initial operation target
argument`, and `execute bits operation target argument`. The semantic input is
the same arbitrary `bits : List Bool`; there is no shape, readiness or size
premise. Access uses the false input-bank selector and returns either Boolean;
rank and select quantify both targets. API statements quantify every natural
argument. Machine-safety statements explicitly require
`argument < 2 ^ Experiment.width bits.length`, including representable invalid
arguments. Every valid argument is proved representable.

Required field groups and their independent consumer obligations:

1. **Complete retained capacity** (`REQ-BV-ALLOC`, `INV-STORE-IDENTITY`,
   `INV-PROGRAM-ACCOUNTING`, `INV-WIDTH-SCALING`). Literal memory length plus
   the flattened `Instruction.encoding` length of each of the three compiled
   programs plus `8271+3` scratch words, all multiplied by W, is at most
   `bits.length + completeRho bits.length`. `LittleOLinear completeRho` and
   `log2(n+2)+1 ≤ W n ≤ 48*(log2(n+2)+1)` are separate projected fields.
   Consumer must retain all three code terms, the entire data and scratch.
2. **Numerical allocation and reader** (`REQ-BV-REUSE`, `REQ-BV-RUN`,
   `INV-GLOBAL-PHYSICAL-MACHINE`). Every member of actual memory fits W;
   actual four loaded descriptor replies yield a safe computed position and
   strict logical stride bound for every active request, including empty
   sentinels. The actual reader on this memory has exact packet, length,
   ordered actual descriptor/span receipts and register frame under only its
   loaded target/width metadata. The independent consumer expands these
   predicates, retaining exact memory and request registers.
3. **All-natural API correctness** (`REQ-BV-OPS`). `access bits i=bits[i]?`;
   `rank bits target p=if p≤bits.length then some(rankPrefix target bits p)
   else none`; `select bits target k=Succinct.select target bits k`.
   Each gets its own independent expected-type projection.
4. **Actual compiled answers** (`REQ-BV-OPS`, `INV-VALUE-DEPENDENCY`,
   `INV-TRACE-EXECUTION`, `INV-PUBLIC-COMPOSITION`). The actual run halts with
   the encoded independent specification, places that packet in the same
   result register used by the API, has the exact charged setup/controller
   receipts, and stays within the fixed literal instruction bound. Access,
   rank and select are separate fields so their validity conventions cannot
   silently change through a generic guard. Receipt lists include actual
   setup loads and are never attached by post-hoc replay.
5. **Complete execution safety** (`REQ-BV-RUN`, `INV-WIDTH-SCALING`). For each
   operation and representable argument, the public consumer expands all five
   existing `RankExecutionSafety` conjuncts: every dormant instruction field
   fits; final state fits; every indexed transition has safe instruction and
   fitting after-state; every fuel prefix fits; every receipt-producing
   occurrence has fitting address, exact memory reply and fitting returned
   value. No independent sibling program or restricted suffix may substitute.
6. **Uniform cost and finite scratch** (`REQ-BV-RUN`, `INV-CATEGORY-SEPARATION`).
   Literal program lengths/budgets are access132, rank1450, select10030.
   Actual six category counts partition actual steps and each is bounded.
   Every fuel prefix of actual programs, even over arbitrary supplied memory,
   keeps every register at index≥8271 equal to zero from the actual initial
   state. This supplies the finite support behind the counted scratch bank.
7. **Supplied-memory agreement** (`INV-VALUE-DEPENDENCY`,
   `INV-GLOBAL-PHYSICAL-MACHINE`). Agreement at every attempted receipt,
   including absent replies, implies equality of the complete actual run on
   supplied memory. The consumer uses actual program, budget and initial state
   and observes result, transitions, costs and receipts through that equality.

The constructor must inhabit `FullyChargedBitvectorCapstone` without any
correctness, memory-fit, readiness, geometry or representation hypotheses.
The exact public name remains
`RMQ.PackedBitvector.fullyChargedBitvectorCapstone_holds`.

The independent public consumer is written against these expanded
propositions and projects every mandatory field. The public mutation campaign
must keep a mutated constructor type-correct while deleting/weakening a field
or replacing it with a sibling proposition, then require the separate
consumer to fail at the expected projection/type surface. A failure confined
to an outdated constructor is insufficient evidence. Expected-accept controls,
exact literal mutation/restoration bytes, versioned case registry and clean
restoration checks are mandatory. The final report quotes the resulting
propositions and exact object chains, not merely theorem names.

Finite validation is separate from universal proof. Version2 main validation
has 46 exact cases on the complete allocation; the previous 18-case select
route registry is preserved under controls. Parameterized exceptional-route
fixtures must use valid components when small canonical cases cannot reach
long/sparse branches. Universal proofs cover those canonical-global cases;
finite coverage must not claim to reach them without an observed transition.
