# PQ1 concrete model and proof DAG

Contract freeze: RC6 `4639223bc8130b0ef752270b5cbdd74325abcd60`.
This is an implementation contract and proof plan, not a proved public claim.
Every acceptance requirement remains in `PQ1_ACCEPTANCE_MATRIX.md`.

## Machine choice

Use a distinct physical instruction vocabulary under
`RMQ.SuccinctFinal.PackedWordRAM`. Its memory input is a flat numeric word list.
It has no segmented store, input values, shape, or semantic query callback.
The state contains scalar registers, a PC, and running/halted/fault status.
The result of halt is the selected register's value. A failed physical load
produces a receipt with `none` and enters fault status. Receipts and category
logs are observations of the run, not executable scratch state.

Instructions: raw load, immediate constant, move, add, subtract, multiply,
integer quotient/remainder, variable left/right shifts, AND/OR/XOR, scalar
comparison, conditional jump, direct/indirect jump, and halt. Each instruction
performs one advertised operation. Calls are explicit moves and transfers;
saturating source subtraction is lowered to compare/branch/subtract.
Execution proofs establish non-underflow for ordinary subtraction and exact
arithmetic representability, so no unbounded result is used as a word.
Instruction fetch and a single register write are the usual instruction
mechanism; they are not additional query primitives. A memory attempt,
including failure, is charged. The program never uses invalid instruction fetch
as a successful termination route.

The model explicitly assumes constant-cost word multiplication, quotient,
remainder, Boolean operations and variable shifts. This is the arithmetic
word-RAM convention in Pat Morin's [Open Data Structures, section 1.4](https://opendatastructures.org/ods-python/1_4_Model_Computation.html),
which lists multiplication, division, remainder and Boolean operations.
James Aspnes's [RAM model notes](https://www.cs.yale.edu/homes/aspnes/pinewiki/RandomAccessMachine.html)
also specify quotient/remainder, register-addressed memory, control operations
and logarithmic registers. Variable shifts are the explicit word operation
used by the prototype and the existing E1 bit-window refinement; they are not
popcount, rank, select, or a controller transition. This model does not assert
that a source-language division or shift has constant Lean wall-clock cost.

## Allocation and width route

Keep the exact RC6 `packedReviewerMemory shape`, flatten it and densely re-chunk
at the new width. Prefix a fixed finite list of counted metadata words. Metadata
contains size geometry, direct long/sparse counts, and the finite descriptors
needed by the old logical-address planner. It is computed during preprocessing
and read by explicit load instructions. Even size-only values are counted.
The fixed code contains descriptor field locations, never per-input geometry.

For old allocated bit length B, H metadata words and positive width W, prove
the exact capacity bound `(H + ceil(B/W))*W <= B+(H+1)*W`.
Use RC6's `B <= 2*n+packedReviewerRho n` and prove the additional term little-o.
The old header and padding remain counted; their redundant logarithmic space
avoids changing the old universal logical-read specification.

Choose one size-only logarithmic width with sufficient polynomial capacity
and a constant floor for fixed code and scratch addresses. The planned starting
width was `64 * (Nat.log2 (n+2)+1)`. After the source inventory, the concrete
builder uses `32 + 8 * packedReviewerCellWidth n`, with a proved upper bound
`192 * (Nat.log2 (n+2)+1)` and checked little-o closure. Its final adequacy still
requires the explicit intermediate-value proof, not this formula alone.
Raising width means re-chunking
the dense bit string, never multiplying the old cell count by the new width.
Logical absence uses a separate presence value where needed; raw physical loads
never add one to an all-ones physical cell.

## Concrete capstone statement to inhabit

The intended exported theorem is
`RMQ.SuccinctFinal.PackedWordRAM.fullyChargedPackedQueryCapstone_holds`.
The literal expected type will name the concrete builder `buildMemory`, fixed
`queryProgram`, `wordWidth`, `initialState` and `run`, and a closed budget `K`.
It will assert all of the following together (no correctness, width, readiness,
budget or store-agreement premise on the canonical builder):

1. `LittleOLinear rho` and explicit logarithmic bounds on `wordWidth n`.
2. For every `xs : List Int`, the allocation `buildMemory xs` has capacity at
   most `2*xs.length+rho xs.length`; every stored cell and instruction field
   fits `wordWidth xs.length`; fixed code/scratch bits are also absorbable in
   an explicitly given little-o term.
3. For all endpoints `l,r < 2^(wordWidth xs.length)`, the *same* actual
   `run (buildMemory xs) queryProgram K (initialState xs.length l r)` halts,
   returns the encoded total half-open leftmost reference answer, has at most K
   instructions, exact six-category partition, width-valid prefix states and
   position-preserving read backing. Guard rejection is part of that run.
4. Its logical-read refinement covers both selects, every LCA branch and final
   rank, with one physical translation into `buildMemory xs`, including missing
   reads, repetitions and empty logical words.
5. Every valid mathematical endpoint pair is representable. The total Nat API
   rejects out-of-word endpoints at value level; no machine cost is claimed for
   parsing unbounded external integers.
6. Agreement on the actual ordered read observations determines the full run
   result, categories and receipts on supplied memories.

This conjunction will be pinned by a separately written expected-type consumer
projecting each exact object argument and property. Defining a record with these
fields does not discharge any field. A prior theorem will not be renamed.

## Proof DAG and ownership

* Lead: primitive physical instruction definitions, acceptance/model freeze,
  experiment provenance, integration and whole-query consumer.
* PQ1-SM (read-only): exact RC6 packing/width lemma inventory. Its report feeds
  arbitrary-width packing and old-cell refinement.
* PQ1-SC (read-only): controller/refinement/loop inventory. Its report feeds
  uniform program construction and the constant instruction budget.
* First proof leaves: primitive execution calculus and category/read provenance;
  arbitrary-width dense packing; fixed header arithmetic/width.
* Derive old absolute logical bit geometry from the counted descriptors, then
  use the proved direct span assembly on the new allocation. The initial
  two-old-cell recovery route remains a helper; direct spans avoid that
  redundant decode layer now that their compilation is proved. Preserve exact
  logical value/length and ordered actual new-cell receipts, then consume the
  read block in the uniformly compiled rank/select/fringe/interior controller.
* Prove finite program/operand/scratch bounds and all-size controller loop
  bounds; compose them with the actual run and value refinement.
* Only after the conjunction closes: add public alias, expected-type consumer,
  replay controls, affected claim inventory, gates and fresh exact-commit audit.

Each producer precedes its consumer. Evidence-dependent choices follow source
inspection or experiments; they do not prevent producing that evidence.

## Experiment provenance

`experiment-rc6/` is an unchanged copy of all 45 manifest entries plus the
manifest from the isolated prior experiment. Entry byte lengths and SHA256s
were checked before copying. The original ZIP's verified SHA256 is
`f108739ea4029fc94fbc2a6c5e4b6c8e420c3fad5553f42a02689b57ba8c802e`.
Source: `C:/Users/poin/Documents/RMQ/wordram-whole-path-spike-20260910`.
The commissioning source synthesis is copied as `RC6_SOURCE_SYNTHESIS.md`.
The original files are read-only inputs to this task. Prototype counts and
fixtures are finite evidence, never universal proof premises.
