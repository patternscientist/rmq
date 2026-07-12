# U2 Final-Route Migration Audit (W16)

Date: 2026-07-11
Exact base: `27a4514152f2ce5680542e712d8c652263a08010`
Scout branch: `codex/rmq-u2-final-route-scout`
Mode: report-only; no Lean source, public documentation, or existing design record changed

## Status

**Scout local report — Status: COMPLETE.**

No assigned or inherited acceptance criterion remains unmet.

**U2 roadmap state: INCOMPLETE / ACTIVE.** The isolated uniform-directory and
composed-store rung is substantial, but the reviewer close/LCA route does not
consume it. The legacy zero-block route remains reachable there. `U3` therefore
remains blocked on `U2`.

This dual status is intentional. It follows
`WDD-20260711-002`: completing an audit report is not completing the roadmap
consumer that the report audits.

## Executive Verdict

At this base, `canonicalRelativeRmmInteriorDirectory` is not merely partially
wired into the final route. It has **no call-graph edge into the production final
RMQ stack**. Its only bridge to the old implementation is
`canonicalRelativeRmmInteriorDirectory_agrees_with_legacy_of_compactReady`,
which is deliberately conditional on `CompactReady` and cannot justify an
all-size migration.

The production stack still uses:

1. the legacy `ConcreteCompactBPCloseLCADirectory`, whose interior type is
   indexed by Active-gated block geometry;
2. the Ready / active-non-Ready / inactive three-way interior replay;
3. the zero-block same-block BP-code scan in `lcaClose`;
4. the corresponding supplied-store replay;
5. conditional Active/Ready close sources in the global and flat stores; and
6. the route-split cost and paper aliases built on those paths.

The current U2 component itself has the right local shape: one raw canonical
hierarchy, a counted six-table component store, returned values derived from
physical reads, an execution-derived dynamic footprint, supplied-store
agreement, successful-read backing, bounded returned words, unconditional
range exactness, a 240-read cap, and an exact raw little-o payload theorem.
Two blockers remain before it may own the reviewer path:

- its physical addresses, including the canonical dead address, are not proved
  to fit a principled machine address word; singleton and size two concretely
  fail the current input-only capacity; and
- the component has not been lifted through the structural WordRAM trace,
  cross-block merge, `lcaClose`, final supplied-store replay, counted global
  flat store, list API, headline aliases, and `RMQPaper`.

## 1. Requirement-to-Evidence Matrix

| Requirement | Exact evidence at this base | Audit result |
|---|---|---|
| Total positive geometry for every shape | `RelativeRmm.canonicalLayout` and `RelativeRmm.canonicalLayout_valid`, `RelativeSummary.lean:1270-1323,2593-2612` | Closed locally |
| One all-size two-level interior hierarchy | `canonicalRelativeRmmInteriorDirectory`, `InteriorDirectory.lean:3415-3446` | Closed locally |
| One counted physical store for all six tables | `canonicalRelativeRmmInteriorComponentStore` and offsets, `InteriorDirectory.lean:1493-1545` | Closed locally |
| Returned candidates depend on actual indexed reads | `canonicalRelativeRmmInteriorRangeMinExecutionWithStore` and refinement chain, `InteriorDirectory.lean:2058-2099,2102-2559` | Closed locally |
| Execution-derived ordered footprint | `canonicalRelativeRmmInteriorRangeFootprintWithStore`, `InteriorDirectory.lean:2096-2100`; store profile `3663-3721` | Closed locally |
| Store agreement determines result, cost, and adaptive continuation | `canonicalRelativeRmmInteriorRangeMinCostedWithStore_eq_of_agree`, `InteriorDirectory.lean:2671-2687` | Closed locally |
| Successful reads are in range and counted-store backed | `canonicalRelativeRmmInteriorRange_successful_read_backed`, `InteriorDirectory.lean:2701-2733` | Closed locally |
| Returned words fit `machineWordBits shape.bpCode.length` | `canonicalRelativeRmmInteriorRange_returned_word_bounded`, `InteriorDirectory.lean:2735-2745`; profile `3703-3709` | Closed locally |
| Every executed and dead address fits the modeled address word | Existing theorem ends at `address < componentStore.store.words.size`, `InteriorDirectory.lean:3690-3702`; no capacity theorem follows | **Open; concrete tiny failure** |
| Exactness covers small and Ready shapes with one theorem | `canonicalRelativeRmmInteriorDirectory_rangeMinCosted_erase_exact`, `InteriorDirectory.lean:3448-3462`; all-size profile `3748-3781` | Closed only for isolated interior component |
| Exact raw payload is little-o | `canonicalRelativeRmmInteriorRawPayloadOverhead_littleO`, `InteriorDirectory.lean:3464-3477,3594-3628` | Closed locally |
| Final abstract close directory consumes U2 | `ConcreteCompactBPCloseLCADirectory.interior` still has legacy gated indices and old cost, `ConcreteDirectory.lean:15-24,1358-1363` | **Fail** |
| Final costed cross-block and LCA route uses raw layout | Both use `canonicalBPRelativeSummaryBlockSize`; LCA branches on zero, `ConcreteDirectory.lean:76-136` | **Fail** |
| Structural trace consumes U2 | Three-way legacy interior replay, `ConcreteDirectoryRAM.lean:1119-1131`; structural LCA zero branch, `2985-3000` | **Fail** |
| Supplied-store structural trace consumes U2 | Legacy counterparts at `ConcreteDirectoryRAMStoreParam.lean:3624-3637,4466-4500,4926-4943` | **Fail** |
| U2 store is a counted global/flat close-store slice | Final store still uses legacy summary/local/global tables, `Segments.lean:84-150`; `FlatPayload.lean:256-350,412-663` | **Fail** |
| Final successful reads are backed by the U2 slice | Current backing theorems are strong for the legacy conditional sources, not the U2 component store | **Fail** |
| Old zero-block route is unreachable from reviewer path | Live in costed, structural, supplied-store, route-cost, public alias, docs, and harness surfaces | **Fail** |
| Public all-size cost is rederived from the uniform physical route | Roadmap `U3` remains blocked on `U2`, `RMQ_FINAL_ROADMAP.md:141-155` | Blocked downstream |
| `RMQPaper` consumes the U2 route | `RMQPaper.lean` imports `RMQ.Headlines.RMQ`; those aliases still reduce to the legacy route | **Fail** |

The repository describes this boundary honestly. `docs/FAMILY_SUMMARY.md:61-84`
says the first U2 rung is independent of final dispatch, and
`DD-20260710-004` says final `lcaClose`, the zero-block route, and public
constants are unchanged (`DESIGN_DECISIONS.md:1641-1671`).

## 2. Exact Call Graph

### 2.1 The disconnected U2 component

```text
RelativeRmm.canonicalLayout
  -> canonicalRelativeRmmSummaryTable
  -> canonicalRelativeRmmInteriorLocalTable
  -> canonicalRelativeRmmInteriorGlobalTable
  -> canonicalRelativeRmmInteriorComponentStore + offsets
  -> canonicalRelativeRmmInteriorRangeMinComputation
  -> canonicalRelativeRmmInteriorRangeMinExecutionWithStore
  -> canonicalRelativeRmmInteriorRangeMinCostedWithStore
  -> canonicalRelativeRmmInteriorDirectory
  -> canonicalRelativeRmmInteriorDirectory_profile_allSize
```

The store order is baseline, min-relative, max-relative, arg-offset,
local-offset, global-block. The directory's `rangeMinCosted` and
`payloadWordsRead` are projections of the same supplied-store execution
(`InteriorDirectory.lean:1493-1598,2058-2100,3415-3446`).

The only current edge toward the legacy implementation is:

```text
canonicalRelativeRmmInteriorDirectory
  -- CompactReady only -->
concreteBPRelativeRmmInteriorDirectory
```

through
`canonicalRelativeRmmInteriorDirectory_agrees_with_legacy_of_compactReady`
(`InteriorDirectory.lean:3783-3810`). There is no occurrence of the canonical
directory in the production Lean modules below.

### 2.2 Actual production costed route

```text
concreteBPRelativeRmmInteriorDirectory                 [legacy three-way]
  -> concreteCompactBPCloseLCADirectory.interior       [legacy indices/cost]
  -> ConcreteCompactBPCloseLCADirectory.crossBlockCloseCostedWithRankSeed
  -> ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed
       zero block -> zeroBlockSameBlockCloseCosted
       same block -> localBPSameBlockCloseDecodedCostedWithRankSeed
       cross block -> crossBlockCloseCostedWithRankSeed
  -> SuccinctFinal.concreteBPNativeCloseDirectory
  -> SuccinctFinal.concreteBPNativeLCACloseCosted
  -> SuccinctFinal.concreteBPNativeSuccinctRMQQueryCosted
```

Evidence: `InteriorDirectory.lean:898-937`,
`ConcreteDirectory.lean:15-24,76-136,1358-1363`, and
`SuccinctFinal.lean:119-122,1525-1560`.

The legacy block size is the root of the zero route:
`canonicalBPRelativeSummaryBlockSize` is raw only when `Active` and zero
otherwise (`RelativeSummary.lean:1469-1474`). In contrast,
`(RelativeRmm.canonicalLayout shape).blockSize` is always positive.

### 2.3 Actual structural WordRAM route

```text
concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural
  Ready              -> two-level legacy trace
  active non-Ready   -> bounded legacy summary scan
  inactive           -> TraceResult.pure none
  -> crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegments
  -> lcaCloseTraceResultWithRankSeedAllSizeStructural
       zero block -> zeroBlockSameBlockCloseStructuralTraceResult
       same block -> local decoded trace
       cross block -> structural cross-block trace
  -> concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural
  -> WholeQueryInstr.evalGlobalWordTrace (.lcaClose)
  -> WholeQueryProgram.evalGlobalWordTrace
  -> concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
  -> all-size / no-synthetic / flat-payload execution stories
```

Evidence:

- interior dispatcher and public route theorem:
  `ConcreteDirectoryRAM.lean:1119-1172`;
- cross-block composition: `ConcreteDirectoryRAM.lean:2146-2180`;
- LCA zero/same/cross dispatch: `ConcreteDirectoryRAM.lean:2985-3032`;
- final LCA trace: `SuccinctFinalRAM.lean:2377-2398`;
- whole-query evaluator and controller:
  `SuccinctFinalRAM.lean:3226-3258,3754-3762,3985-4010,4054-4067`;
- execution-story packets:
  `SuccinctFinalRAM.lean:4678-4713,4806-5086`.

The fixed controller is still the expected one: select the left close, select
the close for `right - 1`, compute LCA-close, conditionally rank at
`answerClose + 1`, and return the predecessor (`SuccinctFinalRAM.lean:3985-3994`).
The U2 migration changes the close/LCA implementation beneath that controller,
not the half-open RMQ contract.

### 2.4 Actual supplied-store route

```text
concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructuralWithStore
  -> crossBlockCloseTraceResultWithRankSeedAllSizeStructuralAtSegmentsWithStore
  -> lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore
  -> concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore
  -> supplied WholeQuery instruction/program evaluator
  -> concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResultWithStore
  -> footprint agreement / exactness / model-adequacy theorems
```

The supplied interior repeats the Ready/Active/inactive split
(`ConcreteDirectoryRAMStoreParam.lean:3624-3637`), the supplied LCA repeats the
zero/same/cross split (`4926-4943`), and the final supplied wrapper inherits it
(`SuccinctFinalStoreParam.lean:1380-1389,1573-1606,1763-1772,1862-2168`).

### 2.5 Global segmented and flat store

The production segment manifest is:

- `20..23`: legacy summary baseline/min/max/arg;
- `24`: legacy local offsets;
- `25`: legacy global blocks;
- `26..27`: retired finite-small interior names, empty and uncounted;
- `28`: retired finite-small same-block name, empty and uncounted;
- `29`: dead segment.

`concreteBPNativeSuccinctRMQGlobalReadStore` binds `20..25` directly to the
legacy tables (`Segments.lean:49-65,84-150`). The flat payload's close component
is `(concreteBPNativeCloseDirectory shape).payload`, also legacy
(`FlatPayload.lean:68-123`). Its source manifest makes summary components
counted only under `Active`, local/global components counted only under `Ready`,
and `26..28` never counted (`FlatPayload.lean:256-350`). Source offsets, words,
payload slices, and backing theorems all inherit those choices
(`FlatPayload.lean:412-772,774-965,1172-1390`).

### 2.6 List and paper surfaces

```text
SuccinctFinal whole-query global trace/store
  -> SuccinctRMQClassic.queryCosted / queryCostedWithStore
  -> SuccinctRMQClassic flat-payload and full-model profiles
  -> RMQ.Headlines.RMQ aliases
  -> RMQPaper
```

`SuccinctRMQClassic.lean:108-225` constructs and exposes the final payload,
query, store, and trace wrappers; its exactness, cost, flat-store, and main
profile theorems continue through `:237-557`. `RMQ/Headlines/RMQ.lean:28-553`
exports those surfaces, including the route costs and zero-block leaf aliases.
`RMQPaper.lean` imports only `RMQ.Headlines.RMQ`.

## 3. Singleton and Size-Two Address-Capacity Failures

### 3.1 What is already repaired

The original singleton **cell width** mismatch is real but no longer the open
issue. For a singleton, raw relative cells require 5 bits while the input-based
machine word has 2 bits. `FixedWidthNatTable.machineStore` repairs that by
rechunking every logical cell into multiple 2-bit physical words. The composed
query really reads those chunks and reconstructs the value.

### 3.2 What still fails

Rechunking increases the number of physical words. The component's current
word width remains
`SuccinctRank.machineWordBits shape.bpCode.length = log2(bpLength) + 1`, but no
theorem proves the resulting word addresses fit `2^wordWidth`.

After a targeted build of the defining module, direct `#eval` of the actual
`canonicalRelativeRmmInteriorComponentStore` and offset record gave:

```text
# fields:
# (size, bpLen, inputWordBits, capacity, totalComponentWords,
#  baselineWords, minWords, maxWords, argWords, localWords, globalWords,
#  (baseline,min,max,arg,local,global,dead offsets))

(1, 2, 2, 4, 17, 2, 3, 3, 3, 2, 4, (0,2,5,8,11,13,17))
(2, 4, 3, 8, 23, 1, 3, 3, 3, 12, 1, (0,1,4,7,10,22,23))
```

Therefore:

| Shape size | Input word width | Component words | Live address range | Dead address | Capacity | Result |
|---:|---:|---:|---:|---:|---:|---|
| 1 | 2 | 17 | `0..16` | 17 | 4 | live and dead addresses exceed capacity |
| 2 | 3 | 23 | `0..22` | 23 | 8 | live and dead addresses exceed capacity |

Both size-two Cartesian shapes `[7, 3]` and `[3, 7]` gave the same counts. The
empty shape already has three component words and dead address 3 against
one-bit capacity 2. The `#eval` probes were stdin-only and did not add a proof
theorem or source file. The first direct import failed because the fresh
worktree had no RMQ oleans; after the targeted module build, the direct probes
ran successfully.

The defect is not confined to the first two nonempty sizes. Additional direct
samples were:

| `n` | input bits | capacity | component words | largest one component |
|---:|---:|---:|---:|---:|
| 4 | 4 | 16 | 44 | 36 |
| 8 | 5 | 32 | 94 | 80 |
| 16 | 6 | 64 | 145 | 125 |
| 32 | 7 | 128 | 248 | 216 |
| 64 | 8 | 256 | 351 | 294 |
| 128 | 9 | 512 | 548 | 448 |

There is a second immediate failure in the current segmented model:
`WordRAM.Register.AddressFitsInBits` requires both segment and index to be below
capacity (`WordRAM/Register.lean:19-25`), but the close segments are `20..25`.
They cannot fit the 2-bit singleton or 3-bit size-two input word even when a
particular local index happens to fit.

This failure is exactly the completion-gate distinction between:

```text
address < host Array.size
```

and:

```text
address < 2 ^ modeledAddressWordWidth.
```

`canonicalRelativeRmmInteriorRange_successful_read_backed` proves the first,
not the second. The dead address is `componentStore.store.words.size`, so a
capacity theorem must cover `size` itself, not merely successful addresses
below `size`.

## 4. Principled Word-Width Designs

### 4.1 Fixed floor

Example:

```lean
max K (SuccinctRank.machineWordBits shape.bpCode.length)
```

Advantages:

- mechanically preserves the existing input-derived model above a finite
  threshold;
- a sufficiently large `K` can cover a proved finite small regime; and
- monotonicity immediately preserves current returned-word bounds.

Problems:

- `K = 5` happens to cover the two reported component addresses, but already
  fails the sampled `n = 4` component; `K = 8` fails the sampled `n = 64`
  component;
- choosing `K` from an unproved finite search is arbitrary model repair;
- the final counted payload contains `2n + o(n)` bits, so input positions alone
  do not automatically bound one globally flattened word-address space; and
- it obscures why the address word is the right machine domain.

Disposition: acceptable only if accompanied by a theorem proving one explicit
`K` covers the entire finite exceptional domain and if the same width covers
the final counted store and operands. It is not the preferred reviewer story.

### 4.2 Separate input data width and component address width

Example:

```lean
dataWordBits shape := machineWordBits shape.bpCode.length
addressWordBits shape :=
  machineWordBits (canonicalRelativeRmmInteriorComponentStore shape).store.words.size
```

Advantages:

- minimal change to the already-verified data codec;
- capacity follows directly from `self_lt_two_pow_machineWordBits`; and
- accurately diagnoses that stored words and addresses are different
  obligations.

Problems:

- it is a two-width machine unless the final model explicitly permits separate
  data and address registers;
- it does not yet cover addresses in the entire final payload store; and
- a component-local width is not the cleanest headline certificate.

Disposition: useful intermediate theorem layer, but insufficient as the final
single-word-RAM story unless the public model deliberately adopts split widths.

### 4.3 Input plus counted-store/address domain (recommended)

Define one query-independent machine domain from the input and the exact
counted final store (or from an independent bit-length upper bound that avoids
a circular rechunking definition). Schematically:

```lean
finalAddressDomain shape :=
  max 26 (max shape.bpCode.length
    (concreteBPNativeSuccinctRMQFlatWordStore shape).words.size)

finalWordBits shape := machineWordBits (finalAddressDomain shape)
```

If the final word store itself is chunked at `finalWordBits`, avoid a circular
definition by deriving the width from the counted flat **bit** payload length
plus a constant segment/sentinel allowance, then prove the word count is below
that domain.

Advantages:

- the width has a direct semantic meaning: it indexes the input and the counted
  store actually used by the execution;
- singleton, size two, offsets, sentinels, and later flat-store composition are
  covered by one certificate;
- it supports a reviewer-native theorem that every read address and operand
  fits the same fixed width for the whole prepared input; and
- asymptotic `O(log n)` width follows from a linear/eventually-linear bound on
  the counted `2n + o(n)` payload, without a query-dependent maximum.

Required care:

- prove the width is positive and query independent;
- prove it dominates the data width, so all existing returned-word theorems
  transport monotonically;
- prove the exact flat store and every component slice lie in the domain;
- cover segment identifiers if they remain separate operands;
- cover all arithmetic operands used by the controller, not only read indices;
- prove the new physical chunking/padding does not change the counted bit
  payload or the `2n + o(n)` theorem; and
- keep the width theorem separate from Lean `Array` bounds and runtime claims.

Disposition: recommended. It fixes the actual invariant at the final consumer
and produces the clearest paper-level machine-well-formedness certificate.

### 4.4 Trace-local maximum (not sufficient)

`SuccinctFinalRAM.lean:4308-4326` derives a finite bound from a particular
trace's maximum event bits. This is technically valid for that execution, but
it is query dependent and does not define one prepared-input machine domain.
It must not be used as the final U2 addressability theorem.

## 5. Required Migration Declarations and Signatures

Names below are proposed canonical targets. Existing public names may be
preserved by changing their definitions and retaining compatibility aliases,
but each signature-strength obligation must exist before U2 is complete.

### 5.1 Address-domain certificate

```lean
def canonicalRelativeRmmInteriorAddressDomain
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.max 26
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.size

def canonicalRelativeRmmInteriorAddressWordBits
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits
    (canonicalRelativeRmmInteriorAddressDomain shape)

theorem canonicalRelativeRmmInteriorAddressWordBits_pos
    (shape : Cartesian.CartesianShape) :
    0 < canonicalRelativeRmmInteriorAddressWordBits shape

theorem canonicalRelativeRmmInteriorDataWordBits_le_addressWordBits
    (shape : Cartesian.CartesianShape) :
    SuccinctRank.machineWordBits shape.bpCode.length <=
      canonicalRelativeRmmInteriorAddressWordBits shape

theorem canonicalRelativeRmmInteriorComponentStore_size_lt_capacity
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentStore shape).store.words.size <
      2 ^ canonicalRelativeRmmInteriorAddressWordBits shape

theorem canonicalRelativeRmmInteriorDeadAddress_lt_capacity
    (shape : Cartesian.CartesianShape) :
    (canonicalRelativeRmmInteriorComponentOffsets shape).deadAddress <
      2 ^ canonicalRelativeRmmInteriorAddressWordBits shape

theorem canonicalRelativeRmmInteriorRange_address_lt_capacity
    {shape : Cartesian.CartesianShape} {store : Array (List Bool)}
    {startBlock count address : Nat} {word? : Option (List Bool)}
    (hread : (address, word?) ∈
      (canonicalRelativeRmmInteriorRangeMinExecutionWithStore
        shape store startBlock count).reads) :
    address < 2 ^ canonicalRelativeRmmInteriorAddressWordBits shape

theorem canonicalRelativeRmmInteriorRange_operands_lt_capacity ...
```

The address theorem must cover successful, failed, repeated, and sentinel
reads. If the final domain is global rather than component-local, use the final
width in these statements and prove the component offset transport.

### 5.2 Flat-execution to WordRAM trace bridge

The present U2 API stops at `FlatStoreExecution`; it has no globally segmented
`WordRAM.TraceResult` consumer. A real bridge must execute against the supplied
`WordRAM.ReadStore`, not wrap a precomputed `Costed` answer.

```lean
def canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore
    (shape : Cartesian.CartesianShape)
    (store : WordRAM.ReadStore) (segment : Nat)
    (startBlock count : Nat) :
    WordRAM.TraceResult (Option (Nat × Nat))

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore_refines
    ... :
    (...).toCosted =
      canonicalRelativeRmmInteriorRangeMinCostedWithStore
        shape componentArray startBlock count

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore_eq_of_agree
    ... :
    (forall address,
      address ∈ consumedFootprint ->
      storeA.readWord? segment address = storeB.readWord? segment address) ->
    traceA = traceB

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore_trace_forall
    ...

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore_matchesReadStore
    ...

theorem canonicalRelativeRmmInteriorRangeMinTraceResultAtSegmentWithStore_noSynthetic
    ...
```

A single close-interior segment containing the exact composed U2 words is the
cleanest match to the existing physical execution. Keeping six public segments
is also possible, but then the migration must prove an exact address
decomposition/recomposition theorem for every component offset; a semantic
adapter is not enough.

### 5.3 Canonical close directory and zero-free dispatch

Either migrate `ConcreteCompactBPCloseLCADirectory` in place or introduce a new
canonical structure and make the old name a compatibility alias. The final
reviewer structure must have this shape:

```lean
structure CanonicalCompactBPCloseLCADirectory
    (shape : Cartesian.CartesianShape) where
  interior : PayloadLiveBPRelativeRmmInteriorDirectory shape
    (RelativeRmm.canonicalLayout shape).blockSize
    (RelativeRmm.canonicalLayout shape).blockCount
    (canonicalRelativeRmmInteriorDirectoryPayloadLength shape)
    canonicalRelativeRmmInteriorQueryCost
  payload : List Bool
  payload_eq_interior : payload = interior.payload

def canonicalCompactBPCloseLCADirectory
    (shape : Cartesian.CartesianShape) :
    CanonicalCompactBPCloseLCADirectory shape

theorem canonicalCompactBPCloseLCADirectory_interior_eq
    (shape : Cartesian.CartesianShape) :
    (canonicalCompactBPCloseLCADirectory shape).interior =
      canonicalRelativeRmmInteriorDirectory shape
```

The final costed query must dispatch only same-block versus cross-block using
the positive raw block size:

```lean
theorem lcaCloseCostedWithRankSeed_eq_canonical_dispatch
    (directory : CanonicalCompactBPCloseLCADirectory shape)
    (rankCloseCosted : Nat -> Costed Nat)
    (leftClose rightClose : Nat) :
    directory.lcaCloseCostedWithRankSeed rankCloseCosted leftClose rightClose =
      if blockOfClose layout.blockSize leftClose =
          blockOfClose layout.blockSize rightClose then
        localBPSameBlockCloseDecodedCostedWithRankSeed ...
      else
        directory.crossBlockCloseCostedWithRankSeed ...
```

No Ready, Active, CompactReady, or `blockSize = 0` premise or branch may appear.
The existing semantic signatures must then be reproved with raw block
arithmetic, especially:

```lean
theorem crossBlockCloseCostedWithRankSeed_exact_of_query ... :
  (...).erase = some answerClose

theorem lcaCloseCostedWithRankSeed_exact_of_query ... :
  (...).erase = some answerClose

theorem lcaCloseCostedWithRankSeed_cost_le ...

theorem read_words_length_le_machine ...
```

The first two should retain their existing half-open query premises and
leftmost answer conclusion, but replace every legacy block-size occurrence with
`(RelativeRmm.canonicalLayout shape).blockSize`.

### 5.4 Structural and supplied-store close/LCA

Required zero-free structural ladder:

```lean
def canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment ...
theorem ..._refines
theorem ..._trace_forall
theorem ..._matchesReadStore

def crossBlockCloseTraceResultWithRankSeedCanonicalAtSegment ...
theorem ..._refines
theorem ..._trace_forall
theorem ..._matchesReadStore

def lcaCloseTraceResultWithRankSeedCanonical ...
theorem ..._refines
theorem ..._trace_forall
theorem ..._matchesReadStore
theorem ..._no_syntheticCostOnlyPrimitive
```

and supplied-store counterparts:

```lean
def crossBlockCloseTraceResultWithRankSeedCanonicalAtSegmentWithStore ...
theorem ..._eq_of_agree
theorem ..._store_parametric
theorem ..._matchesReadStore

def lcaCloseTraceResultWithRankSeedCanonicalWithStore ...
theorem ..._eq_of_agree
theorem ..._store_parametric
theorem ..._matchesReadStore
theorem ..._no_syntheticCostOnlyPrimitive
```

The global final wrappers must refine the newly migrated costed close query,
not the legacy directory through a CompactReady equality.

### 5.5 Counted global flat-store slice

At minimum, the flat-store layer needs declarations equivalent to:

```lean
theorem concreteBPNativeSuccinctRMQFlatPayloadCanonicalInterior_words
    (shape) :
    canonicalInteriorSourceWords shape =
      (canonicalRelativeRmmInteriorComponentStore shape).store.words

theorem concreteBPNativeSuccinctRMQFlatPayloadCanonicalInterior_payload
    (shape) :
    flattenPayloadWords (canonicalInteriorSourceWords shape).toList =
      (canonicalRelativeRmmInteriorDirectory shape).payload

theorem concreteBPNativeSuccinctRMQFlatPayloadCanonicalInterior_slice
    (shape) :
    flatPayloadSlice ... =
      (canonicalRelativeRmmInteriorDirectory shape).payload

theorem concreteBPNativeSuccinctRMQFlatPayloadCanonicalInterior_counted
    (shape) :
    concreteBPNativeSuccinctRMQFlatPayloadSegmentCountedInFlat
      shape canonicalInteriorSegment

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_canonicalInterior
    (shape) (index) :
    flatStore.readWord? canonicalInteriorSegment index =
      (canonicalRelativeRmmInteriorComponentStore
        shape).store.words[index]?

theorem concreteBPNativeSuccinctRMQFlatPayloadReadStore_successful_counted_read_backed
    ...
```

These theorems must be unconditional. Active/Ready-gated countedness for the
new canonical source would preserve the defect U2 exists to remove.

### 5.6 Whole-query and public capstones

The migrated route must re-establish, under existing stable public names or
new names plus aliases:

- global trace refinement to the costed query;
- supplied-store equality on exact dynamic read agreement;
- successful counted-read backing and flat-slice provenance;
- no-synthetic execution;
- fixed prepared-input address/operand/word bounds;
- exactness to the `List Int` half-open leftmost query;
- payload length `2 * n + o(n)`; and
- a physical-read-derived all-size cost theorem.

The public chain ends only when the migrated declarations are consumed by
`SuccinctRMQClassic`, `RMQ.Headlines.RMQ`, and `RMQPaper`.

## 6. Remaining Ready / Active / Inactive Dependencies

### Runtime and proof dependencies that must leave the reviewer route

- Active-gated legacy geometry:
  `canonicalBPRelativeSummaryBlockSize` and related projections,
  `RelativeSummary.lean:1443-1474`.
- Legacy `concreteBPRelativeRmmInteriorReady`, including its empty obstruction
  and threshold sufficiency; these may remain as compatibility theorems but not
  final dispatch.
- `ConcreteCompactBPCloseLCADirectory.interior` legacy indices and old query
  cost, `ConcreteDirectory.lean:15-24`.
- Ready/Active/inactive interior selection in the costed directory and
  structural trace, `InteriorDirectory.lean:937-1180` and
  `ConcreteDirectoryRAM.lean:1119-1193`.
- Public route theorem
  `concreteBPRelativeRmmInteriorAllSizeStructuralRoute_total`, which certifies
  the obsolete split.
- Ready/Active/inactive branches in the supplied-store replay,
  `ConcreteDirectoryRAMStoreParam.lean:3624-3893`.
- Ready/Active/inactive cost constants and route bounds:
  Ready 118, active non-Ready 568, inactive 88, and their proof branches in
  `SuccinctFinal.lean:27-107` and final RAM/store-param modules.
- Ready-keyed successful-read exclusion and backing lemmas for close segments
  24/25 in `FlatPayload.lean:1313-1390` and their whole-query propagation.
- Validation harness route labels keyed to Ready/Active.

### Dependencies allowed to remain as compatibility history

- `RelativeRmm.canonicalLayout_compactReady_iff_legacyReady` and fieldwise
  agreement theorems;
- `canonicalRelativeRmmInteriorDirectory_agrees_with_legacy_of_compactReady`;
- legacy cost equalities, provided their names and docs explicitly say legacy
  and they are no longer the main paper route; and
- old route implementations in compatibility-only modules outside
  `RMQPaper`'s reviewer closure.

Agreement evidence is useful regression protection. It is not a dispatch
license.

## 7. Remaining Zero-Block Dependencies

The zero-block route is live because the reviewer path still asks the legacy
Active-gated projection for its block size.

Current consumers:

- `ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed`,
  `ConcreteDirectory.lean:122-136`;
- `lcaCloseTraceResultWithRankSeedAllSizeStructural`,
  `ConcreteDirectoryRAM.lean:2985-3000`;
- `lcaCloseTraceResultWithRankSeedAllSizeStructuralWithStore`,
  `ConcreteDirectoryRAMStoreParam.lean:4926-4943`;
- final global and supplied-store LCA wrappers;
- `concreteCompactBPCloseRouteSplitQueryCostWithRankSeed`,
  `ConcreteDirectory.lean:1374-1383`;
- `concreteCompactBPCloseZeroBlockRouteScanCost = 4096`, which drives the clean
  all-size `4144` bound;
- headline aliases around `RMQ/Headlines/RMQ.lean:480-496`;
- route descriptions in `WHAT_IS_PROVED.md`, `PAPER_MODEL_ADEQUACY.md`,
  `TRUST_AUDIT_PACKET.md`, and `WORD_RAM_REVIEW_PACKET.md`; and
- the validation cost harness.

The raw canonical block size is positive for every shape. Full migration should
make the zero branch absent by construction, not merely unreachable after an
extra Ready/Active premise. The old scan may stay checked as compatibility
history, but no `RMQPaper` theorem should need it.

## 8. Public Surfaces Affected

### Cost and constants

- `SuccinctClose.compactBPCloseOverhead` and its little-o proof currently point
  to the legacy envelope (`LocalBPDecoder.lean:30-73`); migration should point
  to the exact canonical overhead or prove an exact suitable domination.
- Close costs in `LocalBPDecoder.lean:75-98`.
- Final Ready/Active/inactive/zero/clean/legacy constants and route theorems in
  `SuccinctFinal.lean:16-107,1593-1922`.
- Global trace cost theorems around `SuccinctFinalRAM.lean:5755-5788`.
- Headline aliases around `RMQ/Headlines/RMQ.lean:282-381`.

The current U2 interior cap is 240 physical reads, not the legacy Ready cost 30.
A conservative old bound may remain true during migration, but `U3` must derive
one explained public numeral from the new physical trace. Preserving 118 by
charging logical cells instead of all physical chunks would be invalid.

### Payload and store

- `concreteBPNativeCloseDirectory` payload and
  `concreteBPNativeSuccinctRMQPayload` accounting;
- `ConcreteBPNativeSuccinctRMQFlatPayloadLayout.closePayload` and padding;
- flat source enumeration, offsets, word arrays, payloads, countedness, slices,
  source manifest, segment backings, and global-store equality in
  `FlatPayload.lean:68-1803`;
- `concreteBPNativeInteriorTraceSegments` and global store definitions in
  `Segments.lean`; and
- exact read-agreement footprints in `SuccinctFinalStoreParam.lean`.

### Execution and adequacy

- final structural/no-synthetic/flat-payload stories in `SuccinctFinalRAM.lean`;
- supplied-store whole-query equality and exactness in
  `SuccinctFinalStoreParam.lean`;
- the packaged records in `SuccinctFinalModelAdequacy.lean`;
- `SuccinctRMQClassic` prepared, flat-store, and main profile theorems; and
- `RMQ.Headlines.RMQ` and `RMQPaper`.

### Axiom inventories

The local U2 entries already appear in `scripts/axiom_check.lean:847-861`.
Migration affects legacy route entries around `:869-895,936,949-979`, WordRAM
entries around `scripts/wordram_axiom_check.lean:84-112,165,178,194,200`, and
headline entries around `scripts/headline_axiom_check.lean:41-77`. New public
capstones must replace or supplement those checks; old compatibility checks may
remain explicitly labeled.

### Theorem and claim maps

At implementation time, synchronize at least:

- `docs/FAMILY_SUMMARY.md`;
- `docs/WHAT_IS_PROVED.md`;
- `docs/PAPER_THEOREM_MAP.md`;
- `docs/PAPER_MAIN_THEOREM.md`;
- `docs/PAPER_CLAIM_CORRESPONDENCE.md`;
- `docs/PAPER_MODEL_ADEQUACY.md`;
- `docs/PUBLICATION_STRATEGY.md`;
- `docs/TRUST_AUDIT_PACKET.md`;
- `docs/WORD_RAM_REVIEW_PACKET.md`;
- `docs/CODE_MAP.md` and import-closure counts if they change;
- `docs/DIGESTION_LOG.md`; and
- `docs/internal/RMQ_FINAL_ROADMAP.md` plus a new accepted design record for the
  address-domain and final-route choice.

This scout did not edit any of those surfaces.

## 9. Technically Correct Routes That Fail U2 in Spirit

Reject any migration that does one of the following:

1. places U2 only behind the Ready branch while retaining Active/inactive
   fallbacks;
2. uses only CompactReady agreement to claim an all-size consumer;
3. changes the structural trace but leaves the public `Costed` query on the
   legacy directory;
4. changes the costed query but leaves supplied-store, global store, or flat
   source words on legacy conditional tables;
5. appends the U2 component store as counted padding while actual reads still
   target the legacy segments;
6. computes the semantic answer first and emits U2-looking reads afterward;
7. wraps `canonicalRelativeRmmInteriorRangeMinCostedWithStore` in an opaque
   `TraceResult.ofCosted`-style boundary instead of exposing its actual reads;
8. keeps legacy block size for fringe/block arithmetic while swapping only the
   middle directory, producing incompatible partitions on inactive shapes;
9. preserves the zero-block scan as a small-input compatibility fallback in the
   reviewer path;
10. proves only `address < Array.size`, ignoring modeled capacity and the dead
    address;
11. uses a query-dependent trace maximum as the prepared-input word width;
12. uses an arbitrary fixed floor with no full finite-domain and final-store
    capacity theorem;
13. flattens components with `offset + index` but omits component-range guards,
    allowing an out-of-range local read to alias the next component;
14. claims the old 118 cost while charging fewer events than the physical U2
    chunks read;
15. leaves summary/local/global countedness conditional on Active/Ready in the
    purportedly uniform flat store;
16. proves source-name correspondence but not literal flat-slice containment;
17. introduces proof-only answers, routing oracles, answer-as-premise cells,
    decorative reads, empty footprints, or synthetic cost events; or
18. retains 4144/196727 and route-split wording as the main paper claim after a
    new uniform all-size theorem exists.

## 10. Migration Order and Stop Gate

Recommended order:

1. choose and prove the final input-plus-counted-store address domain;
2. prove singleton, size-two, threshold-minus-one, threshold, and representative
   same/cross/interior cases against that domain;
3. add the real U2 `FlatStoreExecution` to supplied `WordRAM.TraceResult` bridge;
4. migrate the abstract close directory and raw block arithmetic;
5. migrate cross-block and zero-free `lcaClose` costed exactness;
6. migrate structural and supplied-store close/LCA traces;
7. embed the exact component words as an unconditional counted flat slice;
8. reprove final read backing, dynamic agreement, machine well-formedness, and
   no-synthetic execution;
9. rederive one physical-read all-size cost (`U3`);
10. update list/headline/paper aliases, axiom inventories, theorem maps, claims,
    roadmap, and digestion record; and
11. verify that the paper import closure no longer reaches a live zero-block or
    Ready/Active/inactive dispatch theorem.

U2 may be marked complete only when the canonical directory is consumed by the
reviewer close/LCA path, every final supplied-store read is backed by its counted
flat slice under one principled machine domain, and the zero-block route is no
longer reachable there.

## 11. Proof Digestion

### What the current work means

The repository has built the correct isolated U2 interior navigator. It is not
an oracle wrapper: the six payload tables are physically chunked, the supplied
store returns the chunks, the query reconstructs candidates from those results,
and the same execution creates the footprint and cost. The all-size semantic
theorem no longer depends on Ready or Active.

### What remains conceptually

The final RMQ theorem still asks a different, older navigator to do the work.
Migration is therefore not a local alias change. It is the proof that the new
navigator owns the final block partition, close merge, machine trace, supplied
store, counted flat payload, list query, and paper theorem. The address register
must also be sized for the store actually addressed, not just for positions in
the input.

### Live assumptions and model boundaries

- half-open RMQ queries and leftmost tie semantics remain unchanged;
- `RelativeRmm.canonicalLayout_valid` supplies positive total geometry;
- fixed-width chunk encoding/decoding and one-tick indexed reads are model-level
  assumptions already made explicit in the current component;
- payload bits, physical word count, proof fields, model ticks, machine
  registers, Lean runtime, and measured performance remain distinct; and
- no compiled-runtime bound is claimed by this audit.

### Skeptical graduate-student questions

1. Show one `RMQPaper` theorem whose reduction reaches
   `canonicalRelativeRmmInteriorDirectory` on a singleton or two-node shape.
2. Why do every live, failed, repeated, and sentinel address fit one fixed
   prepared-input machine word?
3. Does every successful final read literally land in the counted U2 flat
   slice, or only in an extensionally similar table?
4. Is the final all-size cost the number of physical reads after rechunking?
5. Has the zero-block path disappeared from the reviewer call graph, rather
   than being hidden behind an additional premise?

At this base, the answer to the first and fifth questions is no, and the second
is concretely false for the current input-only address width.

## 12. Audit Verification

Performed:

- verified the worktree `HEAD` is exactly
  `27a4514152f2ce5680542e712d8c652263a08010`;
- verified the branch is `codex/rmq-u2-final-route-scout`;
- independently searched declarations and consumers across the U2 module,
  costed close directory, structural RAM trace, supplied-store trace, final
  global/flat stores, `SuccinctRMQClassic`, `RMQ.Headlines.RMQ`, `RMQPaper`,
  axiom scripts, roadmap, claims, and design records;
- ran `lake build
  RMQ.Core.SuccinctClose.EndpointFringe.InteriorCandidate.InteriorDirectory`
  successfully (58 targets, 250.2 seconds) to make the exact defining module
  available in the fresh worktree;
- ran stdin-only Lean `#eval` probes of the actual component store for empty,
  singleton, both size-two shapes, and the additional sampled sizes in section
  3; and
- will run `git diff --check` and an allowed-file-only status check before
  commit.

Not performed:

- no full `lake build` was required; the targeted build above was used only to
  validate the concrete address-capacity finding;
- no public headline/root changed, so no axiom inventory script was required;
- no existing design record or public claim document was changed; and
- no `native_decide` or `Lean.ofReduceBool` evidence is used in this report.
