# Word-RAM Interpreter Refinement Plan

Snapshot: 2026-06-30.

This note records the current fixedpoint plan for adding a first-order
Word-RAM interpreter to the repository.  Phases 0-3 now have an initial
checked implementation: the core interpreter, payload table reads,
interpreter-backed rank/select leaves, and a BP close/LCA table-read skeleton.
The remaining frontier is the whole final succinct RMQ query program.

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
theorem PayloadLiveStoredWordRankData.rankProgram_profile ...
theorem PayloadLiveStoredWordSelectData.selectInterpreted_profile ...
```

Status: initial leaf bridge landed in
`RMQ/Core/SuccinctSpace/RankSelectRAM.lean`, with the select-locator table
bridge in `RMQ/Core/SuccinctSpace/SelectSamplesRAM.lean`.

Rank is a genuine first-order `WordRAM.Program`: it reads the sampled rank word
and the packed bitvector word from a payload-only store, then applies the
word-local rank primitive.  Select keeps the domain-specific sample decoder
outside the generic interpreter, but every sample and payload word it consumes
is now read through interpreted payload memory and then proved to refine the
existing costed surface.

Remaining Phase-2 hardening: push the same pattern through the deeper generic
select/sparse-exception directories and expose a public rank/select spoke
variant whose query functions route through the interpreted leaves.

### Phase 3: BP close/LCA query skeleton

Candidate modules:

```text
RMQ/Core/SuccinctClose/RAM.lean
RMQ/Core/SuccinctSelect/TwoLevel/BPCloseNavigationRAM.lean
```

Targets:

```lean
theorem PayloadLiveBPCloseLCADirectory.lcaCloseProgram_profile ...
```

Status: initial table-read skeleton landed in
`RMQ/Core/SuccinctSpace/BPCloseLCARAM.lean`.

The current theorem interprets the payload-live optional-close table read and
proves it refines the existing BP close/LCA costed surface.  This is the right
Phase-3 bottom layer, not the final BP navigation interpreter: endpoint
select-close, rank-close, seeded local BP windows, and final RMQ join still
need to be sequenced as a whole query program.

Large-regime first remains acceptable for the final query capstone.  Small-
regime semantic fallbacks should be handled later by explicit finite payload
tables or excluded from the first interpreter theorem with a clear premise.

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

Status: the first whole-query interpreted consumer has landed at the BP
close-navigation layer in
`RMQ/Core/SuccinctSpace/BPCloseRMQNavigationRAM.lean`:

```lean
theorem PayloadLiveBPCloseRMQNavigationDirectory
  .queryBuiltInterpretedCosted_refines_queryBuiltCosted ...
theorem PayloadLiveBPCloseRMQNavigationDirectory.interpreted_profile ...
theorem WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily
  .two_n_plus_o_interpreted_word_bounded_query_profile ...
```

This closes the nontrivial sequencing step for select-close, select-close,
LCA-close, rank-close, and answer reconstruction over the payload-live
close-navigation family.  It does not yet retarget the final
`SuccinctFinal` capstone, whose current query still runs through the newer
compact close-access surface and a rank callback into
`lcaCloseCostedWithRankSeed`.

### Phase 5: Broader rebasing

After an interpreted query layer exists:

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

## Parallel Work Plan And Status

The work can be parallelized, but only along real leaves.

### Phase 0 landed: interpreter core and provenance

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

Status: landed in `RMQ/Core/WordRAM.lean`, including word-local rank/select
program constructors and the core provenance lemmas.

### Phase 1 landed: payload table/read compilation

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

Status: landed in `RMQ/Core/SuccinctSpace/WordStoreRAM.lean`,
`RMQ/Core/SuccinctSpace/TablesRAM.lean`, and
`RMQ/Core/SuccinctSpace/SelectSamplesRAM.lean`.

### Phase 2 landed: rank/select interpreted leaves

Owned files:

```text
RMQ/Core/SuccinctSpace/RankSelectRAM.lean
```

Targets:

```lean
PayloadLiveStoredWordRankData.rankProgram_profile
PayloadLiveStoredWordSelectData.selectInterpreted_profile
```

Status: landed for the core payload-live stored-word rank/select leaves.
Generic select and sparse-exception select directories remain later consumers.

### Phase 3 initial skeleton landed: BP close/LCA interpreted table read

Owned files:

```text
RMQ/Core/SuccinctSpace/BPCloseLCARAM.lean
```

Targets:

```lean
PayloadLiveBPCloseLCADirectory.lcaCloseProgram_profile
```

Status: landed for the payload-live optional-close table read.

### Phase 4 landed: interpreted BP close-navigation query

Owned files:

```text
RMQ/Core/SuccinctSpace/BPCloseRMQNavigationRAM.lean
```

Targets:

```lean
PayloadLiveBPCloseRMQNavigationDirectory.queryBuiltInterpretedCosted_refines_queryBuiltCosted
PayloadLiveBPCloseRMQNavigationDirectory.interpreted_profile
WordBoundedSampledEncodedPayloadLiveBPCloseRMQNavigationFamily.two_n_plus_o_interpreted_word_bounded_query_profile
```

Status: landed for the payload-live BP close-navigation family.  This is a
whole-query consumer of the interpreted rank/select and LCA table-read leaves.

### Phase 5 landed: public interpreted headlines

Owned files:

```text
RMQ/Headlines.lean
scripts/headline_axiom_check.lean
```

Targets:

```lean
RMQ.Headlines.succinctRMQTwoNPlusOConstantQueryInterpreted
RMQ.Headlines.bpCloseNavigationInterpretedTwoNPlusOConstantQuery
```

Status: landed.  The BP close-navigation alias remains a component-level
checkpoint, while `succinctRMQTwoNPlusOConstantQueryInterpreted` exposes the
additive final BP-native succinct RMQ capstone whose close-select, compact
close/LCA, and final answer-rank leaves route through the current `WordRAM`
bridge layer.

### Phase 6 landed: final `SuccinctFinal` integration

Owned files:

```text
RMQ/Core/SuccinctFinalRAM.lean
```

Targets:

```lean
SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_cost_le
SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_exact
SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
```

Status: landed as an additive final-capstone theorem.  The compact
close-access layer has the narrow bridge
`RMQ/Core/SuccinctClose/RelativeRmmMacro/ConcreteDirectoryRAM.lean`, where
`ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithInterpretedRankSeed`
builds the false-rank seed callback from
`PayloadLiveStoredWordRankData.rankProgramClamped` and
`rankWordRAMStore false`, then proves equality with the existing rank-seeded
close/LCA wrapper.  `SuccinctFinalRAM` then sequences the interpreted
generic sparse-exception close-select leaf, the compact LCA leg, and the final
answer-rank leaf into the built generic BP-native final query and proves it
refines the existing costed query.

## What This Would Mean In Plain English

Today the headline theorem says, honestly: under an explicit word-RAM-style
cost model, this concrete payload-accounted construction has exact RMQ answers,
constant modeled query cost, and `2n + o(n)` payload bits.

After the current interpreter capstone, the stronger statement is: the final
query path is replayed through component bridges whose payload-word reads,
rank/select word operations, and fixed-width table reads are interpreted and
proved equal to the existing costed query.  This closes the main oracle-shaped
gap in the public succinct RMQ theorem without changing the reference
semantics, payload accounting, or public cost bound.

The remaining stronger target is a single closed first-order program for the
whole final branch structure.  That would be a compiler/interpreter
presentation polish, not a prerequisite for the current payload-live
interpreter-backed capstone.

## Fixedpoint Conclusion

The architecture did not need a broad redesign.  It needed one new layer:
first-order payload-memory execution, connected to the existing construction by
component refinement theorems.  That layer now exists for the public succinct
RMQ query path.

The best order from here is:

1. continue BP/tree-navigation APIs over the reusable rank/select surface; and
2. design the flatter whole-query AST or compiler-style target only after the
   public BP operations identify which dynamic-address patterns are actually
   needed.

The standalone compressed/FID rank-select spoke has now been replayed through
the same `WordRAM` layer.

## 2026-06-30 Stress-Test Fixedpoint

Two read-only audits of the current repository converged on the same
architecture: keep the current theorem-facing `Costed` and profile surfaces,
but do not treat them as the final trust boundary. The interpreter layer should
be a one-way refinement:

```lean
Program -> eval -> Result -> Costed
```

There should be no general adapter in the other direction. A theorem saying a
`Costed` query can be represented by some program would recreate the oracle
gap; the point is that the value and trace are computed together from a fixed
syntax tree and payload-only store.

### Public Surfaces To Preserve

The migration should add interpreter-backed variants underneath existing names
and re-alias only after equivalent statements exist. Preserve:

- `ValidRange`, `LeftmostArgMin`, `CandidateExact`, `RMQBackend`, and
  `RMQBackend.queryBuilt_eq`;
- the headline aliases in `RMQ.Headlines`, especially
  `rankSelectWordBoundedNPlusOConstantQuery`,
  `rankSelectCompressedFIDFixedWeightFamilyProfile`, and
  `succinctRMQTwoNPlusOConstantQuery`;
- `ExactRMQStateEncoding`, `PayloadLosslessEncoding`, and
  `PayloadSpaceBounds`;
- `RankSelectSpec.BitVectorRankSelectDirectory` and
  `BitVectorRankSelectFamily.n_plus_o_constant_query_profile`;
- the public BP navigation surfaces in `RMQBPNavigation`; and
- the reusable hub boundary exposed by `RMQHub` and `VerifiedDS`.

Interpreter-backed theorem names should be additive at first, for example
`succinctRMQTwoNPlusOConstantQuery_interpreted` or a similarly explicit alias,
not an in-place semantic strengthening hidden behind the old name.

### Stress-Test Risks

The current code is disciplined but still has five migration risks:

1. `Costed.tickValue`, `TableModel.IndexedAccess.getCosted`, and similar
   surfaces can attach a cost to a value without execution.
2. Abstract profile records such as rank/select directories, broadword-RMQ
   directories, close-access directories, and select-source records are useful
   theorem interfaces but are too weak to be the interpreter trust boundary.
3. Proof-only routing facts, certificates, and exactness fields are legitimate
   proof artifacts, but the interpreter must not be able to read them as
   memory.
4. Static payload-provenance fields such as `payload`, `readWords`, and
   word-bound proofs do not by themselves prove that every dynamic read came
   from payload memory.
5. Small-regime fallbacks and compatibility branches can accidentally re-route
   through semantic helpers unless the first interpreted theorem either
   excludes them with an explicit large-regime premise or implements them as
   payload-backed/interpreted programs too.

### Non-Negotiable Gates

An interpreter milestone is not closed by syntax alone. It must close a named
consumer theorem. In particular:

- no instruction may compute `scanWindow`, whole-bitvector rank/select, rmM,
  Cartesian-shape RMQ, or BP LCA directly;
- every table/routing value used by a query must be simple arithmetic or
  decoded from charged payload reads;
- every dynamic word read must have a payload membership theorem and a
  machine-word-bound theorem;
- final RMQ interpreter theorems must consume the concrete built access family,
  not an arbitrary inhabitant of an abstract directory record;
- proof-only fields may appear in theorem statements and correctness proofs,
  but not in `Store`;
- the first capstone may be large-regime, but the statement must say so; and
- a public headline alias should change only after the interpreted theorem has
  the same user-facing correctness/cost/space content as the current alias.

### Landed First Milestone Shape

The first implementation loop should be deliberately small but theorem-shaped.
The target is a core `RMQ.Core.WordRAM` module with a payload-only store,
first-order programs, deterministic evaluation, and these theorem surfaces:

```lean
theorem WordRAM.eval_toCosted_cost_eq_trace_length ...
theorem WordRAM.eval_reads_subset_payload ...
theorem WordRAM.eval_word_reads_length_le_machine ...
```

That is the smallest layer that changes the trust story. A syntax tree without
read-provenance and word-bound theorems is only scaffolding.

That first loop has landed.  The next layer also interpreted the existing
payload primitives:

```lean
theorem PayloadWordStore.readProgram_refines_readWordCosted ...
theorem BoundedPayloadWordStore.readProgram_word_length_le ...
theorem FixedWidthNatTable.readProgram_exact ...
theorem FixedWidthOptionNatTable.readProgram_exact ...
```

Rank/select leaves and the BP close/LCA table-read skeleton have also landed.
The next fixedpoint loop should therefore attack the first whole-query
consumer, not more syntax or table wrappers.  This preserves the same
refinement style used in mature formalization projects: keep the abstract
reference semantics, prove a representation/execution layer implements it,
and compose the refinements one consumer at a time.

### 2026-07-01 whole-query flattening assessment

The first whole-query consumer has landed, but it is intentionally
leaf-interpreted rather than one closed first-order program:

```lean
SuccinctFinal.concreteBPNativeSuccinctRMQQueryInterpretedCosted_refines_queryCosted
SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_interpreted_profile
```

The current `WordRAM.Program` syntax is adequate for payload table reads,
sampled rank, and word-local select.  It is not yet adequate for the whole
final RMQ branch structure, because the query uses interpreted values as later
addresses:

1. select-close on the left endpoint produces `leftClose`;
2. select-close on the right endpoint produces `rightClose`;
3. `(leftClose, rightClose)` address the compact close/LCA table;
4. `answerClose + 1` addresses the final rank-close query.

A single closed program therefore needs a first-order register/branch layer:
registers for `Nat`/`Option Nat`, fixed arithmetic on registers, option tests,
and payload-read instructions whose segment/index arguments are register
expressions.  The design should not add a higher-order continuation
`bind : Program Nat -> (Nat -> Program ty) -> Program ty`, because such a
constructor stores an arbitrary Lean function inside the program and would
weaken the anti-oracle story.

The next interpreter-hardening milestone should be a small register-machine
extension plus one consumed theorem on a narrow component, not a direct rewrite
of the final capstone.  A good first target is the compact close/LCA wrapper:
prove that a register-program reading endpoint close registers, consulting the
optional-close table, and returning the answer close refines the current
`lcaCloseInterpretedCosted` path.  After that, the final RMQ query can be
flattened by composing the already interpreted close-select and rank leaves
through the same register layer.
