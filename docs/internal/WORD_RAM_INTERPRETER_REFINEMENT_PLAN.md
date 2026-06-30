# Word-RAM Interpreter Refinement Plan

Snapshot: 2026-06-29.

This note records the current fixedpoint plan for adding a first-order
Word-RAM interpreter to the repository.  It is a planning document, not a
claim that the interpreter layer already exists.

The goal is to harden the existing succinct RMQ and rank/select cost story:
move selected headline query paths from "a `Costed` function has the right
answer and cost" to "a small first-order program runs against counted payload
memory and produces that answer with that trace length."

## Verdict

Build the interpreter as an anti-oracle refinement layer, not as a replacement
for the current reference theory.

Keep:

- the value-level `List` RMQ specification;
- the half-open, leftmost RMQ contract;
- `Costed` as the theorem-facing cost projection;
- `RAM.Exec` as the existing shallow primitive-trace substrate;
- `TableModel`, `PayloadView`, `StoredSeq`, and `StoredMatrix` as refinement
  and payload-accounting surfaces; and
- the current payload/proof/cost/runtime separation in theorem statements.

Add:

- a small first-order `WordRAM` language;
- a deterministic interpreter whose value and trace are computed together;
- a payload-only memory environment; and
- component refinement theorems saying existing concrete query definitions are
  equal to, or cost-bounded by, interpreted programs.

Do not attempt a global rebase first.  The right first capstone is the final
succinct RMQ query path, large-regime if needed, with rank/select and table
reads interpreted before the close/LCA join consumes them.

## Why This Is The Respectable Direction

The current model is honest but shallow.  `Costed.tickValue` can pair any value
with any cost, and `RAM.Exec` still stores a value next to a trace even though
the constructor is private.  That is fine for reusable proof engineering, but a
skeptical reviewer will still ask whether final query values are really forced
to come from payload reads and word primitives.

The interpreter layer answers that question by construction: the only way to
produce the final value is to execute instructions against memory.

This matches the broad pattern in serious verified-systems work:

- CompCert defines source/target semantics and proves semantic preservation for
  compilation rather than trusting a backend by convention:
  https://xavierleroy.org/publi/compcert-CACM.pdf
- CakeML and Bedrock2 use first-order languages with formal semantics and then
  connect those semantics to lower-level compilation paths:
  https://cakeml.org/
  https://github.com/mit-plv/bedrock2
- Isabelle's refinement stack and CoqEAL show the data-refinement pattern that
  fits this repository best: keep high-level reference semantics, refine
  representations behind interfaces, and prove the executable representation
  implements the abstract one:
  https://www.isa-afp.org/entries/Refine_Monadic.html
  https://www.isa-afp.org/entries/Refine_Imperative_HOL.html
  https://github.com/coq-community/coqeal

The immediate target should not be a CompCert-sized compiler.  It should be a
small, Mathlib-free, first-order query machine that can later grow into a
compiler-style story if that becomes useful.

## Non-Goals For The First Pass

The first interpreter pass should not:

- replace the RMQ reference spec;
- replace the full `Costed` API;
- migrate every existing query and builder;
- model Lean runtime;
- prove cache behavior or real CPU execution;
- compile to C/RISC-V;
- solve union-find mutation/amortization;
- add a whole-bitvector `rank`, whole-bitvector `select`, `rmM`, or `RMQ`
  primitive; or
- certify small-input semantic fallback branches unless they are routed through
  explicit finite payload tables.

## Core Design

### Values

Use a small typed or statically indexed value layer.  The first pass only needs:

- `Nat`;
- `Bool`;
- `Option Nat`;
- words as `List Bool`;
- small products, either structurally or via monadic sequencing; and
- `Unit`.

The word representation should initially follow the repository's existing
`List Bool` word lemmas.  A later packed-`Nat` or `BitVec` representation can be
introduced as a refinement of this word view.

### Memory

The memory must be payload-only.  It must not contain `CartesianShape`, proof
certificates, arbitrary function fields, or uncharged auxiliary structures.

Recommended first design:

```lean
namespace RMQ.WordRAM

structure WordSegment where
  words : List (List Bool)
  wordBound : forall w, List.Mem w words -> w.length <= machineWordBits

structure NatSegment where
  cells : List Nat
  width : Nat
  cells_fit : forall x, List.Mem x cells -> x < 2 ^ width

structure OptionNatSegment where
  cells : List (Option Nat)
  width : Nat
  cells_fit : forall x, List.Mem (some x) cells -> x < 2 ^ width

structure Store where
  wordSegments : List WordSegment
  natSegments : List NatSegment
  optionNatSegments : List OptionNatSegment

end RMQ.WordRAM
```

The exact names can change, but the crucial property cannot: all query reads
come from finite payload segments with explicit width/word bounds.

Typed region handles are acceptable.  They are less machine-like than a single
untyped heap, but much more Lean-friendly and close to a statically typed IR.
If later desired, a flattening theorem can map typed regions to one untyped
word-addressed memory.

### Instructions

The instruction set should be fixed before proving query correctness.  It can
be expressed as a monadic syntax tree or as a typed command language.  The first
pass should include:

- constants and returns;
- sequencing;
- bounded arithmetic needed for indices;
- comparisons and branches;
- reads from word/nat/option-nat segments;
- fixed-width decode operations for payload table cells;
- word-local `rankBoolWordPrefix`;
- word-local `selectBoolWord`; and
- option case analysis.

It must not include:

- `scanWindow`;
- `bpRangeMinExcess`;
- whole-bitvector rank/select;
- Cartesian-shape lookup;
- generic callbacks;
- proof-field reads; or
- an instruction whose reference meaning is already the target query.

### Semantics

The interpreter should compute value and trace together:

```lean
def eval : Program a -> Store -> Result a
```

where `Result a` contains a value, a trace of primitive operations, and perhaps
an error state for out-of-bounds or ill-typed reads.

The compatibility theorem with the current ecosystem should be:

```lean
def Result.toCosted : Result a -> Costed a
```

with:

```lean
theorem toCosted_cost_eq_trace_length :
    (eval program store).toCosted.cost =
      (eval program store).trace.length
```

The point is directional: `Program -> eval -> Costed`.  Avoid a general
`Costed -> Program` adapter, because that would recreate the oracle problem.

## First Theorem Chain

### Phase 0: Syntax, semantics, and provenance

Candidate module:

```text
RMQ/Core/WordRAM.lean
```

Target theorem surfaces:

```lean
theorem WordRAM.eval_toCosted_cost_eq_trace_length ...
theorem WordRAM.eval_reads_subset_payload ...
theorem WordRAM.eval_word_reads_length_le_machine ...
```

This phase is successful only if the interpreter cannot inspect proof-only
fields by construction.

### Phase 1: Payload word and fixed-width table reads

Candidate module:

```text
RMQ/Core/SuccinctSpace/WordStoreRAM.lean
```

Targets:

```lean
theorem PayloadWordStore.readProgram_exact ...
theorem BoundedPayloadWordStore.readProgram_word_length_le ...
theorem FixedWidthNatTable.readProgram_exact ...
theorem FixedWidthOptionNatTable.readProgram_exact ...
theorem FixedWidthSelectSampleTable.readProgram_exact ...
```

The purpose is to force "read a table cell" to become an interpreted payload
read plus decode, not a direct call to `table.get?`.

### Phase 2: Rank/select leaf programs

Candidate modules:

```text
RMQ/Core/SuccinctSpace/RankSelectRAM.lean
RMQ/Core/GenericSelect/RAM.lean
```

Targets:

```lean
theorem StoredWordRankData.rankProgram_refines_rankCosted ...
theorem PayloadLiveStoredWordRankData.rankProgram_profile ...
theorem GenericSelect.sparseExceptionSelectProgram_refines_selectCosted ...
theorem GenericSelect.sparseExceptionSelectProgram_profile ...
```

This is the best first useful slice because the current code already uses
payload word reads and the word-local `RAM.selectBoolWord` primitive.  The
missing hardening is occurrence-to-word routing and table reads as first-order
code.

### Phase 3: BP close/LCA query skeleton

Candidate modules:

```text
RMQ/Core/SuccinctClose/RAM.lean
RMQ/Core/SuccinctSelect/TwoLevel/BPCloseNavigationRAM.lean
```

Targets:

```lean
theorem ConcreteCompactBPCloseLCADirectory.lcaCloseProgram_refines_costed ...
theorem ConcreteCompactBPCloseLCADirectory.lcaCloseProgram_profile_of_large ...
```

Large-regime first is acceptable.  Small-regime semantic fallbacks should be
handled later by explicit finite payload tables or excluded from this first
interpreter theorem with a clear premise.

### Phase 4: Final succinct RMQ query program

Candidate module:

```text
RMQ/Core/SuccinctFinalRAM.lean
```

Targets:

```lean
theorem concreteBPNativeSuccinctRMQQueryProgram_refines_costed ...

theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_queryProgram_profile :
    ...
```

The final program should execute:

1. select-close for the left endpoint;
2. select-close for the right endpoint;
3. BP close/LCA navigation;
4. rank-close back to inorder index; and
5. return the RMQ answer index.

It must consume the concrete built access family, not an arbitrary
`BPCloseAccessDirectory` inhabitant.

### Phase 5: Broader rebasing

Only after the query capstone is interpreter-backed:

- expose public headline aliases with an interpreter-backed variant;
- port the public rank/select spoke;
- consider sparse-table/Fischer-Heun query paths;
- add writes/arrays/build loops for preprocessing;
- consider union-find mutable-state semantics; and
- optionally target a Bedrock2/Rupicola-style downstream compilation story.

## Hard Risks And Required Guards

### Risk: the instruction set is too powerful

Guard: no instruction may compute the target query directly.  The interpreter
may have word-local rank/select, but not whole-vector rank/select, RMQ, rmM, or
Cartesian-shape primitives.

### Risk: routing hides the answer

Guard: route computations must be arithmetic or decoded from payload reads.
Any route table must have a payload-length theorem and a read-provenance theorem.

### Risk: proof-only fields leak into memory

Guard: `Store` constructors for final theorems must be built from payload bits
and encoded tables only.  No `shape`, certificates, or function-valued fields.

### Risk: word-size assumptions drift

Guard: every word read by the interpreter must be covered by a bounded-word
theorem.  Reuse the current `machineWordBits` discipline.

### Risk: small-regime fallbacks poison a global claim

Guard: the first interpreter theorem may be explicitly large-regime.  A total
interpreter theorem requires either an interpreted linear scan/fallback or a
finite payload-backed table for small cases.

### Risk: this turns into a giant migration

Guard: every milestone must end in a named refinement theorem consumed by the
next layer.  Syntax-only interpreters, wrapper records, and unconsumed exactness
lemmas do not count as closure.

## Parallel Work Plan

The work can be parallelized, but only along real leaves.

### Worker A: interpreter core and provenance

Owned files:

```text
RMQ/Core/WordRAM.lean
docs/internal/WORD_RAM_INTERPRETER_REFINEMENT_PLAN.md
```

Targets:

```lean
WordRAM.eval_toCosted_cost_eq_trace_length
WordRAM.eval_reads_subset_payload
WordRAM.eval_word_reads_length_le_machine
```

Stop condition: only stop when the core theorem surfaces exist and build, or a
formal obstruction shows the proposed syntax cannot express the first rank-read
program without adding a forbidden primitive.

### Worker B: payload table/read compilation

Owned files:

```text
RMQ/Core/SuccinctSpace/WordStoreRAM.lean
RMQ/Core/SuccinctSpace/TablesRAM.lean
```

Targets:

```lean
PayloadWordStore.readProgram_exact
BoundedPayloadWordStore.readProgram_word_length_le
FixedWidthNatTable.readProgram_exact
FixedWidthOptionNatTable.readProgram_exact
```

Stop condition: do not stop at an adapter around `getCosted`; the read must go
through the interpreter's store.

### Worker C: rank/select compiled leaves

Owned files after A/B land:

```text
RMQ/Core/SuccinctSpace/RankSelectRAM.lean
RMQ/Core/GenericSelect/RAM.lean
```

Targets:

```lean
StoredWordRankData.rankProgram_refines_rankCosted
PayloadLiveStoredWordRankData.rankProgram_profile
GenericSelect.sparseExceptionSelectProgram_refines_selectCosted
```

Stop condition: the result must be consumed by a concrete payload-live family,
not merely exposed as a generic callback interface.

### Worker D: final BP/RMQ integration

Owned files after C lands:

```text
RMQ/Core/SuccinctClose/RAM.lean
RMQ/Core/SuccinctFinalRAM.lean
```

Targets:

```lean
ConcreteCompactBPCloseLCADirectory.lcaCloseProgram_refines_costed
concreteBPNativeSuccinctRMQQueryProgram_refines_costed
builtGenericSparseExceptionBPNativeSuccinctRMQFamily_queryProgram_profile
```

Stop condition: the final theorem must route through the concrete built access
family and interpreted select/rank leaves.

## What This Would Mean In Plain English

Today the headline theorem says, honestly: under an explicit word-RAM-style
cost model, this concrete payload-accounted construction has exact RMQ answers,
constant modeled query cost, and `2n + o(n)` payload bits.

After the interpreter capstone, the stronger statement would be: the query
answer is not merely supplied by a costed Lean function.  It is produced by
running a fixed first-order program that can only read the counted payload and
perform counted word operations.  That is the difference between a disciplined
model and an executable-model refinement.

## Fixedpoint Conclusion

The architecture does not need a broad redesign.  It needs one new layer:
first-order payload-memory execution, connected to the existing construction by
component refinement theorems.

The best order is:

1. interpreter core;
2. payload word/table reads;
3. rank/select leaves;
4. BP close/LCA query path;
5. final succinct RMQ query program; and
6. only then broader rebasing or compiler-style targets.

