# Succinct RMQ Final Path Spec

This document is now the status, caveat, and hardening tracker for the
payload-accounted BP-native succinct RMQ path. The concrete
`2*n + o(n), O(1)` theorem has landed; the remaining work is no longer the C1
false-close/select witness or the C2 compact close-directory join.

The post-capstone goal is to keep the result honest: payload that the query
actually reads, machine-word-bounded word primitives, compiled
exactness/cost/profile theorems, and clear separation between proof-only fields
and charged payload bits.

## Current Capstone Status

The main capstone is now:

```lean
theorem SuccinctFinal
    .builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile :
    ...
```

It composes the generic sparse-exception false-close/select source
`GenericSelect.sparseExceptionSelectSource shape.bpCode false`, packaged by
`SuccinctFinal.builtGenericSparseExceptionSelectBPCloseAccessFamily_profile`,
with the concrete C2 close directory
`SuccinctClose.concreteCompactBPCloseLCADirectory_profile`. The final
payload is `shape.bpCode ++ aux`, the auxiliary payload is padded to the stated
`o(n)` overhead, the query cost is bounded by a constant, and valid
representative-array windows erase to the exact `scanWindow` RMQ answer.
The relative-split theorem trio remains checked compatibility for the
BP-specialized witness, with its public archive alias in
`RMQ.Archive.BPSpecializedCapstone`. The public generic two-sided wrapper makes
explicit that the profile has no large-regime premise and pairs the upper
structure with the doubled Catalan lower slack.

The false-close/select path now reuses the standalone generic Clark
sparse-exception select implementation over `List Bool`, specialized to the
balanced-parentheses code and target `false`.

The C2-local fidelity hardening has also landed on the final path: endpoint
fringes and positive-block same-block queries route through local BP windows
and rank-false seeds supplied by the final close-rank access path. The
zero-block semantic fallback remains only for all-input totality on
tiny/inactive cases; the large/canonical regime has `_of_size_ge` branch
normalization lemmas showing that the positive-block path is used. The remaining
succinct work is presentation/model polish, especially an even flatter
encoded/payload-only version of the final theorem. The older worker scorecards
and anti-pattern catalog below are retained as historical guardrails. Treat any
later sentence that describes the C1 sparse/dense locator, compact close
directory, local BP decoder, or final join as "remaining" as superseded by this
status section.

The local-decoder hardening plan is pinned in
`docs/internal/LOCAL_BP_DECODER_PATH.md`. Workers should use that theorem chain before
editing the split `RMQ/Core/SuccinctClose/*` modules; the old
`RMQ/Core/SuccinctCloseProposal.lean` root is only a compatibility shim.

## Current Inputs

The current merged surface provides useful partial surface:

- The close/LCA side has a payload-live macro/micro BP close-navigation join.
  Its key capstone is:

  ```lean
  theorem RMQ.SuccinctClose
      .PayloadLiveMacroMicroBPCloseNavigationFamily
      .two_n_plus_o_built_query_profile :
    ...
  ```

  This consumes payload-live rank/select plus a payload-live macro/micro
  LCA-close family. It still leaves the macro side abstract through a
  `macroCosted`/`split_exact` style interface.

- The close/LCA side also has a concrete negative theorem:

  ```lean
  theorem RMQ.SuccinctClose.blockPairMacroDirectory_not_sufficient :
    ...
  ```

  This proves that a macro keyed only by
  `(blockOfClose leftClose, blockOfClose rightClose)` is not exact, already on
  a four-node right spine with `blockSize = 3`.

- The close/LCA side has also checked the obvious endpoint-sensitive dense
  fallback:

  ```lean
  theorem RMQ.SuccinctClose
      .denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile :
    ...

  theorem RMQ.SuccinctClose
      .denseAllCloseBPCloseLCAOverhead_not_littleO :
    ...
  ```

  This fallback is exact, charged, and constant-query, but its all-close
  endpoint table is not `o(n)`. The next concrete macro should therefore be a
  real succinct BP-excess/RMQ macro with charged endpoint-fringe repair, not a
  dense direct-access endpoint table.

- The close/LCA side now also has a guarded concrete macro/micro layer:

  ```lean
  theorem RMQ.SuccinctClose
      .concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_profile :
    ...

  theorem RMQ.SuccinctClose
      .concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile :
    ...
  ```

  The first theorem is real semantic progress: same-block close queries use the
  charged micro-codebook, cross-block close queries use charged endpoint-fringe
  and interior macro reads, and the close/LCA answer is exact with constant
  cost. The sampled theorem is intentionally only conditional scaffolding. Its
  `hmacroBudget` premise still has to cover a dense
  `interiorBlockPairRanges blockCount` payload, so it is not a concrete
  `2*n + o(n)` witness and should not be cited as closing C2.

- The select side proves the current query-shape forcing facts:

  ```lean
  theorem RMQ.SuccinctSelect
      .SelectSampleWordExact.selected_position_in_read_word :
    ...

  theorem RMQ.SuccinctSelect
      .TwoLevelPayloadLiveStoredWordSelectData
      .selected_position_in_read_word_of_sample :
    ...

  theorem RMQ.SuccinctSelect
      .SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word :
    ...

  theorem RMQ.SuccinctSelect
      .TwoLevelPayloadLiveStoredWordSelectData
      .selected_wordIndex_eq_of_sample :
    ...

  theorem RMQ.SuccinctSelect
      .SelectSampleWordExact
      .shared_aligned_read_word_forces_same_wordIndex :
    ...

  theorem RMQ.SuccinctSelect
      .TwoLevelPayloadLiveStoredWordSelectData
      .shared_local_locator_forces_same_selected_wordIndex :
    ...
  ```

  These facts show that a shared local locator sample can only answer
  occurrences whose selected bit lies in the one payload word read by that
  sample. If that read word is an aligned machine chunk, exactness forces its
  word index to be `pos / wordSize` for the selected bit; two successful
  queries sharing that aligned word must therefore have the same selected
  chunk. A final compact select builder needs a charged descriptor that
  computes that word choice, or a changed local dense-block query path.

## Final Theorem Shape

The final theorem should have this semantic shape, with concrete names chosen
to match the module where the join lands:

```lean
theorem final_bpnative_succinct_rmq_profile
    (family : FinalBPNativeSuccinctRMQFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n : Nat,
        EncodingLowerBound.logSlackLower n <= 2 * n + overhead n /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            (family.payload shape hshape).length = 2 * n + overhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall left right,
              (family.queryCosted shape hshape left right).cost <= queryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          (hshape : List.Mem shape (Cartesian.shapesOfSize n)) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (family.queryCosted shape hshape left (left + len)).erase =
                    some (scanWindow shape.representative left len))
```

Do not close this target with a theorem over hypothetical operations unless the
same round also supplies the concrete family instance that those operations read
from.

## Component 1: Compact False-Select Locator

The current `blockIndex` hook is not enough.  The old
`TwoLevelPayloadLiveStoredWordSelectData` query shape is also probably too
narrow for the final construction because it reads one local sample and one
aligned payload word.  The final false-select locator needs branch-specific
explicit reads for sparse cases and a dense local path that may read two
aligned payload words.  Do not force the final proof through the old one-word
shape if doing so reintroduces an uncharged locator.

The final select component should specialize first to
`select false shape.bpCode`, since that is what the BP-native RMQ query actually
consumes. A later general rank/select family can generalize the construction,
but it is not the binding theorem.

The final false-select component should let one local entry cover a bounded run
of payload words by storing a compact descriptor that chooses the payload word
before running `RAM.selectBoolWord`. The existing `selectBoolWord` primitive is
the right in-word operation and should be reused before adding any new RAM
primitive. It does not, by itself, locate the word containing the requested
occurrence.

Target query shape:

```text
coarse select-sample read
compact locator / local descriptor read
charged word-choice from the locator payload
payload word read
RAM.selectBoolWord
```

Do not revive the one-entry/one-aligned-word shortcut. The merged theorem
`SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word` says that
an aligned read word is forced to be the selected position's own chunk. Sharing
is only legitimate if the descriptor includes a charged way to choose the final
payload word. The sharper blocker
`TwoLevelPayloadLiveStoredWordSelectData.shared_local_locator_forces_same_selected_wordIndex`
rules out a shared local locator that reads one aligned payload word while
serving selected bits in different chunks.

Do not say "reuse rank summaries to locate the block" unless the construction
also proves the actual locator. Rank summaries answer prefix counts at a known
position; they are not an uncharged predecessor/select structure from an
occurrence to a payload-word index. Rank summaries may be reused for validation,
local counts, or side conditions, but the word-choice step must be backed by a
payload-live compact locator or by a standard dense/sparse select directory with
charged reads.

The component should expose a surface equivalent to:

```lean
structure PayloadLiveBPSelectCloseData
    (shape : Cartesian.CartesianShape) (overhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRank.machineWordBits shape.bpCode.length

  auxPayload : List Bool
  auxPayload_length : auxPayload.length = overhead

  selectCloseCosted : Nat -> Costed (Option Nat)
  selectCloseCosted_cost_le :
    forall idx, (selectCloseCosted idx).cost <= queryCost
  selectCloseCosted_exact :
    forall idx,
      (selectCloseCosted idx).erase =
        SuccinctSpace.bpCloseOfInorder? shape idx

  payload_word_length_le_machine :
    forall {word : List Bool},
      List.Mem word (payloadWordsReadByQuery idx) ->
        word.length <= SuccinctRank.machineWordBits shape.bpCode.length

  word_choice_exact :
    forall idx pos,
      SuccinctSpace.bpCloseOfInorder? shape idx = some pos ->
        selectedPayloadWordIndex idx = pos / wordSize
```

The final theorem need not use exactly this structure name, but it must prove
these facts for a concrete construction. A structure that merely stores
`selectCloseCosted` as a supplied function is only an interface and does not
retire the select blocker.

Known trap from the previous worker round: a local theorem such as
`twoWordDescriptorTableRead_choice_exact_of_select_in_run` is useful but not
enough. It is only a descriptor kernel unless the same loop consumes it in a
global `selectCloseCosted` construction that:

- chooses the descriptor from `idx`;
- proves the selected position lies in that descriptor's covered run, not just
  conditionally assumes it;
- reads descriptor payload and payload words through counted operations;
- proves exact erasure for all indices, not just for the
  branch where the answer is already known to be in one local run;
- proves the auxiliary descriptor payload is in a `LittleOLinear` budget; and
- carries the machine-word side condition for every charged payload word.

Expected concrete builder theorem shape:

```lean
theorem compactSelectCloseLocatorData_profile
    (shape : Cartesian.CartesianShape)
    (hword : 0 < wordSize)
    (hmachine :
      wordSize <= SuccinctRank.machineWordBits shape.bpCode.length)
    ... :
    let data :=
      compactSelectCloseLocatorData shape hword hmachine ...
    data.auxPayload.length <= compactSelectCloseOverhead shape.size /\
      (forall idx,
        (data.selectCloseCosted idx).cost <= compactSelectCloseQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      data.read_words_length_le_machine /\
      data.word_choice_exact
```

Expected family theorem shape:

```lean
theorem PayloadLiveBPSelectCloseFamily.constant_query_profile
    (family : PayloadLiveBPSelectCloseFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall shape,
        ((family.component shape).auxPayload.length <= overhead shape.size) /\
        (forall idx,
          ((family.component shape).selectCloseCosted idx).cost <=
            queryCost) /\
        (forall idx,
          ((family.component shape).selectCloseCosted idx).erase =
            SuccinctSpace.bpCloseOfInorder? shape idx) /\
        (family.component shape).read_words_length_le_machine
```

The binding implementation strategy is the sparse/dense select inventory in
`docs/internal/SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md`.  At a high level:

- sample every `w^2`-ish false occurrence, where
  `w = machineWordBits shape.bpCode.length`;
- store explicit positions for long super intervals;
- inside short super intervals, sample every
  `w / (log w)^2`-ish false occurrence;
- store explicit positions for local intervals whose span exceeds one machine
  word; and
- answer the remaining dense local case by reading at most two aligned payload
  words and using counted word-rank/select primitives.

The locator may reuse rank-side sample tables for counted local counts, but the
proof must still show how `idx` routes to the selected payload word in constant
charged work. A full general `select target bits occurrence` structure is
acceptable only if the same branch instantiates the false-target BP
close-select theorem and proves the payload budget of the actual built tables.

The earlier sibling sparse/dense close-access socket has been pruned rather
than kept as a parallel adapter layer. The repaired relative-split compact
route is now the retained BP-specialized C1 witness:
`SuccinctSelect.builtRelativeSplitSparseExceptionFalseSelectCloseData_profile`
constructs the super/local, sparse-exception, long-flag-rank, and compact
long-super relative tables from `shape.bpCode`, and
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
consumes it in the BP-native final join. Its executable close-select query uses
the cheap validity guard `idx < shape.size`; the full false-count identity
`rankPrefix false shape.bpCode shape.bpCode.length = shape.size` is proof-only.

The current reconciled C1 socket has two useful but non-final ingredients.
First, `sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded`
shows that the old one-word four-field locator entry cannot carry full
machine-width fields while satisfying the machine-word read bound. Dense-local
absolute-base data must therefore use relative fields, split fields, or another
explicitly budgeted layout. The stronger final invariant is that high-frequency
local descriptors may not carry absolute `0..n` positions, absolute
payload-word indices, or absolute table pointers. Absolute full-width fields are
allowed only in low-frequency super tables, rare explicit payloads, or charged
side tables whose total payload is separately proved `LittleOLinear`. If a
low-frequency super table needs several absolute full-width fields, those
fields must be split across charged word-bounded tables or another explicit
word-bounded layout; the old one-word four-full-field codec remains invalid.

The preferred repaired layout is rectangular local routing:

```text
superSlot        := q / superStride
localSlotInSuper := (q - super.baseOccurrence) / localStride
globalLocalSlot  := superSlot * localSlotsPerSuper + localSlotInSuper
```

Dense local entries should live at this deterministic slot or be reached by a
charged dense-side locator. Sparse-local explicit payload bases should likewise
come from a charged sparse flag/rank side structure, not from an absolute
`loc.pointer` packed into every high-frequency local entry.

Explicit exception payloads should be relative and preferably padded by stride:
long-super blocks reserve `superStride` relative offsets and sparse-local
blocks reserve `localStride` relative offsets. Then the query computes the
explicit entry index by charged exception-block rank plus the local occurrence
offset. A variable-length explicit table is acceptable only with a charged base
directory and a payload proof for that directory. Sparse-local exceptions must
not store absolute `0..n` positions at local-entry frequency unless the same
profile proves the absolute encoding still lies under the named little-o
overhead.

The old four-field sparse/dense false-select locator path has now been
physically pruned from the live proposal module. The useful residue is the
relative-split construction consumed by the current capstone, plus the retained
two-level shared-locator obstruction witnesses. New C1 work should not revive
`SparseDenseFalseSelectCloseData` or the rectangular locator branch; it should
build on the generic select surface and the live relative-split tables.

The latest rectangular-built worker branch clarified this target. A route
through `builtTwoLevelFalseSelectCloseData` / the full-width
`TwoLevelPayloadLiveStoredWordSelectData` table can be exact and constant-time,
but `builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ` shows that
its block payload is linear. That route is a compatibility baseline, not a
valid C1 close.

This C1 target is now closed by the repaired relative-split sparse-exception
profile built from the narrow components. The concrete witness is:

```lean
def builtRelativeSplitSparseExceptionFalseSelectCloseData
    (shape : Cartesian.CartesianShape) :
    RelativeSplitSparseExceptionFalseSelectCloseData shape
      (rankSuperOverhead shape.size)
      (rankBlockOverhead shape.size)

theorem builtRelativeSplitSparseExceptionFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := builtRelativeSplitSparseExceptionFalseSelectCloseData shape
    data.payload.length <=
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead shape.size /\
      SuccinctSpace.LittleOLinear
        canonicalRelativeSplitSparseExceptionFalseSelectOverhead /\
      (forall idx,
        (data.selectCloseCosted idx).cost <=
          sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      data.read_words_length_le_machine
```

The theorem consumes deterministic local-slot routing, charged side locators,
the repaired sparse-exception relative table, compact long-super exceptions,
and the dense two-word payload fallback. It is consumed in
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`,
whose public total two-sided wrapper
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`
feeds the concrete close-access witness into the BP-native final theorem and
packages the sharpened lower side.
A verified adapter around `builtTwoLevelFalseSelectCloseData` remains useful
baseline evidence only, because its own overhead theorem exposes the linear
payload.

## Component 2: Concrete Macro/Micro BP Close-LCA (Historical Guardrails)

The macro side is now concrete in the final path. The notes below are retained
as guardrails against reopening false designs, not as active worker targets.

Do not use a macro directory keyed only by endpoint close-block pair. The merged
theorem `SuccinctClose.blockPairMacroDirectory_not_sufficient` proves
that design false. A viable macro must store enough endpoint-sensitive fringe
information, include local offsets inside endpoint blocks, or use a real
BP-excess/RMQ macro over block summaries whose answer is then repaired by
charged local micro queries.

Do not use the fully dense all-close endpoint fallback as the final space
witness. `SuccinctClose.denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile`
shows it is exact and charged, but
`SuccinctClose.denseAllCloseBPCloseLCAOverhead_not_littleO` proves its
auxiliary payload is not `o(n)`.

Do not treat the guarded endpoint-fringe/interior macro as the final succinct
space witness while it still stores dense block-pair range entries. In
particular, a theorem whose final space step assumes
`hmacroBudget` for a payload containing
`interiorBlockPairRanges blockCount` is an abstract conditional wrapper, not the
needed concrete little-o close directory. The final close component must prove
its own `LittleOLinear closeOverhead` from its actual payload layout.

Target construction:

```lean
structure ConcreteMacroBPCloseLCADirectory
    (shape : Cartesian.CartesianShape)
    (overhead queryCost : Nat) where
  payload : List Bool
  payload_length : payload.length = overhead
  lcaCloseCosted : Nat -> Nat -> Costed (Option Nat)
  lcaCloseCosted_cost_le :
    forall leftClose rightClose,
      (lcaCloseCosted leftClose rightClose).cost <= queryCost
  lcaCloseCosted_exact :
    forall {left len leftClose rightClose answerClose : Nat},
      0 < len ->
      left + len <= shape.size ->
      bpCloseOfInorder? shape left = some leftClose ->
      bpCloseOfInorder? shape (left + len - 1) = some rightClose ->
      bpCloseOfInorder? shape (scanWindow shape.representative left len) =
        some answerClose ->
      (lcaCloseCosted leftClose rightClose).erase = some answerClose
```

Expected family/profile theorem shape:

```lean
theorem concreteMacroMicroBPCloseLCAFamily_profile
    (family : ConcreteMacroMicroBPCloseLCAFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall n shape hshape,
        ((family.directory (n := n) shape hshape).payload.length =
          overhead n) /\
        (forall leftClose rightClose,
          ((family.directory (n := n) shape hshape).lcaCloseCosted
            leftClose rightClose).cost <= queryCost) /\
        ...
```

It is acceptable for the first concrete macro theorem to use a conservative
macro layout if its overhead proof is `LittleOLinear` and every read is charged.
It is not acceptable to charge one word for a proof-side table or to leave
`split_exact` as an unimplemented field in the final family.

Known trap from the previous worker round: a profile for
`PayloadLiveBPRangeMinMaxSummaryTable` or
`concreteBPRangeMinMaxSummaryTable_sampled_profile` is only a block-summary
checkpoint. It is not a C2 stop point unless the same loop consumes those
summaries in a `ConcreteMacroBPCloseLCADirectory` or equivalent directory whose
`lcaCloseCosted_exact` proves the returned close is the answer close for the
RMQ/LCA query. Any fixed-width summary table charged as O(1) must also expose
the relevant machine-word bound, such as
`fieldWidth <= SuccinctRank.machineWordBits shape.bpCode.length` or an
equivalent theorem over the actual stored words. If the proof interprets BP
excess via `Nat` subtraction, the construction must state the balanced-prefix
or nonnegative-excess invariant needed by the answer-close theorem.

## Component 3: Final Join

After Component 1 lands, the coordinator or join worker should combine:

- exact `shape.bpCode` payload length `2*n`;
- payload-live rank-false with bounded machine words;
- compact payload-live select-false/close access;
- the concrete compact macro/micro BP close-LCA directory;
- the close-navigation join, adapted to the false-only access interface if
  useful.

Expected theorem shape:

```lean
theorem descriptorMacroMicroBPCloseNavigationFamily
    .two_n_plus_o_concrete_query_profile
    (family :
      DescriptorMacroMicroBPCloseNavigationFamily
        rankOverhead selectOverhead closeOverhead queryCost) :
    LittleOLinear family.overhead /\
      forall n,
        EncodingLowerBound.logSlackLower n <=
          2 * n + family.overhead n /\
        ...
```

The final theorem should be payload-live and concrete. A theorem over encoded
component functions is useful only when it also proves those encoded functions
agree with the built payloads.

## Non-Negotiable Close Chain

The C2 BP-close side is now theorem-shaped. Workers should not redefine
success as "a useful interface landed" or "a concrete builder remains." The
chain below names the next closure targets. A branch may introduce helper
lemmas, structures, or local profiles only while consuming them toward one of
these targets in the same unattended loop.

1. Relative summary budget, with no hidden dense term:

```lean
theorem concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile
    (shape : Cartesian.CartesianShape) :
    let table := concreteBPRelativeMinMaxArgSummaryTable_canonical shape
    SuccinctSpace.LittleOLinear
      (compactBPCloseSummaryPayloadOverhead
        codeSlots microSlots blockSummarySlots superSummarySlots) /\
      table.payload.length <=
        compactBPCloseSummaryPayloadOverhead
          codeSlots microSlots blockSummarySlots superSummarySlots
          shape.size /\
      (forall block,
        (table.summaryCosted block).cost <= 4 /\
          (table.summaryCosted block).erase =
            some (bpSummaryValue shape block)) /\
      table.read_words_length_le_machine := ...
```

This theorem is not closed if it still has premises analogous to
`hsuperPayload`, `hblockPayload`, or a budget for
`interiorBlockPairRanges blockCount`. It must discharge the canonical sampled
superblock and log-log relative-block budgets from the chosen parameters.

2. Pure candidate merge, not a structure field:

```lean
theorem bpRelativeRmmCandidateMerge_exact
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount leftClose rightClose answerClose : Nat} :
    0 < blockSize ->
      blockOfClose blockSize leftClose < blockCount ->
      blockOfClose blockSize rightClose < blockCount ->
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose ->
      answerClose_prefix_leftmost_min_excess_hypotheses shape
        leftClose rightClose answerClose ->
      bpCandidateMerge3? leftFringeCandidate middleCandidate
        rightFringeCandidate =
          some (bpExcessAt shape (answerClose + 1), answerClose + 1) := ...
```

The exact helper names may differ, but the substance may not: the merge fact
must be proved from BP/RMQ semantics and candidate definitions, not supplied as
`semantic_merge_exact`, `hmerge`, or another proof-only field.

3. Concrete compact rmM interior navigator, not a scan:

```lean
def concreteBPRelativeRmmInteriorDirectory
    (shape : Cartesian.CartesianShape) :
    PayloadLiveBPRelativeRmmInteriorDirectory shape
      canonicalBlockSize canonicalBlockCount
      concreteInteriorOverhead concreteInteriorQueryCost := ...

theorem concreteBPRelativeRmmInteriorDirectory_profile
    (shape : Cartesian.CartesianShape) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    SuccinctSpace.LittleOLinear concreteInteriorOverhead /\
      directory.payload.length <=
        concreteInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= canonicalBlockCount shape ->
          (directory.rangeMinCosted startBlock count).erase =
            some
              (bpRangeMinExcess shape canonicalBlockSize startBlock count,
               bpRangeArgMinPrefixPos shape canonicalBlockSize
                 startBlock count)) /\
      directory.read_words_length_le_machine := ...
```

This is the adopted option-1 design: a compact rmM/min-max-tree-style navigator
over block-minimum candidates. It may use B's relative per-block summaries as
leaf values and small universal/local tables, but it must answer the full-block
middle interval by a constant number of charged reads plus bounded arithmetic.
It must not be a direct scan over all interior blocks, a sparse-table payload
with non-little-o space, a dense all-pairs table, or a recursive final RMQ
claim hidden behind this C2 theorem.
The current concrete construction plan is `docs/internal/INTERIOR_NAVIGATOR_DESIGN.md`:
a two-level sparse-table-style navigator over the shrunk block-minimum sequence,
with local offset tables, a global macroblock table, and charged relative-summary
reads for candidate comparison.

The abstract `PayloadLiveBPRelativeRmmInteriorDirectory.profile` theorem is
only an interface sanity check, not target closure. In particular,
`payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle`
shows that the generic record can be inhabited by an empty-payload semantic
oracle unless the final theorem names a concrete built directory and ties the
answer to charged payload word reads. A construction whose
`payloadWordsRead := fun _ _ => []` while the query computes semantic range
minima directly is a documented anti-pattern, not a compact rmM witness.

The exact structure name may differ, but the theorem obligation may not: this
checkpoint closes only when the built payload gives constant-cost leftmost
range-minimum witnesses over complete blocks and proves its payload overhead is
`LittleOLinear`.

Do not count a selected-block bridge as this checkpoint if its exactness still
assumes that the selector entry already contains the semantic winner, for
example a premise of the form `selectorEntries[slot]? = some
(bpRangeArgMinBlock ...)`. Such a lemma is useful only as an iteration result.
The same loop must build the local/global/top selector entries, prove the query
computes the correct slot by bounded arithmetic and charged reads, prove the
payload and machine-word bounds, and consume the bridge in
`concreteBPRelativeRmmInteriorDirectory_profile`.

4. Concrete relative-rmM macro, backed by charged payload reads:

```lean
def concretePayloadLiveRelativeRmmBPCloseMacro
    (shape : Cartesian.CartesianShape) :
    PayloadLiveRelativeRmmBPCloseMacro shape
      canonicalBlockSize canonicalBlockCount
      concreteRelativeOverhead concreteMiddleQueryCost := ...

theorem concretePayloadLiveRelativeRmmBPCloseMacro_profile
    (shape : Cartesian.CartesianShape) :
    let macro := concretePayloadLiveRelativeRmmBPCloseMacro shape
    macro.payload.length <= concreteRelativeOverhead shape.size /\
      (forall leftClose rightClose,
        (macro.lcaCloseCosted leftClose rightClose).cost <=
          concreteMiddleQueryCost + 4) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
          bpCloseOfInorder? shape (left + len - 1) = some rightClose ->
          bpCloseOfInorder? shape
              (scanWindow shape.representative left len) =
            some answerClose ->
          (macro.lcaCloseCosted leftClose rightClose).erase =
            some answerClose := ...
```

This theorem is not closed if the concrete macro is instantiated by arbitrary
exactness fields or uncharged routing. Its reads must come from the relative
summary payload, the compact interior rmM navigator from step 3,
universal/local codebooks, or bounded arithmetic.

5. Concrete compact close directory:

```lean
theorem concreteCompactBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape) :
    let directory := concreteCompactBPCloseLCADirectory shape
    directory.payload.length <= compactBPCloseOverhead shape.size /\
      SuccinctSpace.LittleOLinear compactBPCloseOverhead /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <=
          closeQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
          bpCloseOfInorder? shape left = some leftClose ->
          bpCloseOfInorder? shape (left + len - 1) = some rightClose ->
          bpCloseOfInorder? shape
              (scanWindow shape.representative left len) =
            some answerClose ->
          (directory.lcaCloseCosted leftClose rightClose).erase =
            some answerClose := ...
```

This is the C2 closure point. Same-block micro results, endpoint-fringe repair,
relative-rmM interior summaries, machine-word bounds, and payload budgets must
all be consumed here. A branch that stops before this theorem must identify
which earlier theorem in this chain it closed and why the next theorem is
outside its assigned ownership.

Current caveat: this C2 closure is allowed to use a bounded-local-BP primitive
surface for same-block and endpoint-fringe repair. The primitive must account
for a constant number of BP payload words and prove exact local BP semantics,
but it need not yet derive the answer by interpreting those words. Strengthening
that local decoder is a later hardening item; the final BP-native RMQ join must
carry the caveat rather than silently claiming bit-level local decoding.

6. Final BP-native RMQ join:

```lean
theorem readBackedBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    (accessFamily :
      ReadBackedBPCloseAccessFamily
        rankSuperOverhead rankBlockOverhead
        selectSuperOverhead selectBlockOverhead
        closeAccessOverhead closeAccessQueryCost) :
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead closeAccessOverhead) /\
      forall n,
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n /\
        (forall {shape},
          shape ∈ Cartesian.shapesOfSize n ->
            (concreteBPNativeSuccinctRMQPayload
              accessFamily.toWeakFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead closeAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily.toWeakFamily shape left right).cost <=
            concreteBPNativeSuccinctRMQQueryCost closeAccessQueryCost) /\
        -- exact built-query RMQ erasure for every valid representative window
        ... := ...
```

This final join consumes the read-backed false-only close-access surface and the
C2 concrete compact close directory. The current theorem is a built-payload
join, not an arbitrary encoded-function wrapper: its payload is
`shape.bpCode ++ aux`, with aux padded to the exact reserved overhead, and its
query erases to the exact representative-array RMQ result. This was the staging
surface that the repaired relative-split compact false-close/select witness now
instantiates; future work should focus on local BP-decoder hardening or an
encoded/payload-only presentation, not on reopening the retired C1 caveat.

## Concrete Close Contract

The retask target for the BP close/LCA side is a concrete payload-live directory
with no dense-budget escape hatch:

```lean
def compactBPCloseOverhead : Nat -> Nat := ...

theorem compactBPCloseOverhead_littleO :
    SuccinctSpace.LittleOLinear compactBPCloseOverhead := ...

theorem concreteCompactBPCloseLCADirectory_profile
    (shape : Cartesian.CartesianShape) :
    let directory := concreteCompactBPCloseLCADirectory shape
    directory.payload.length <= compactBPCloseOverhead shape.size /\
      (forall leftClose rightClose,
        (directory.lcaCloseCosted leftClose rightClose).cost <= closeQueryCost) /\
      forall {left len leftClose rightClose answerClose : Nat},
        0 < len ->
          left + len <= shape.size ->
            bpCloseOfInorder? shape left = some leftClose ->
              bpCloseOfInorder? shape (left + len - 1) = some rightClose ->
                bpCloseOfInorder? shape
                    (scanWindow shape.representative left len) =
                  some answerClose ->
                  (directory.lcaCloseCosted leftClose rightClose).erase =
                    some answerClose := ...
```

The concrete implementation should be based on universal small-block tables plus
the adopted compact rmM/min-max-tree interior navigator over relative block
summaries. It must not rely on:

- a dense all-close table;
- dense all block-pair answer/range entries;
- a sampled-budget premise for `interiorBlockPairRanges blockCount`;
- a direct scan over all interior blocks, even if the scan is exact;
- a sparse-table payload unless its own profile proves little-o space under the
  same machine-word model;
- a recursive final succinct-RMQ theorem used as an unexpanded oracle for the
  C2 interior query;
- proof-only exactness fields that are not backed by charged payload reads.

## Loop Rules For This Target

Workers must run the stop audit from `docs/internal/CODEX_AUTONOMY.md`.

At the start of every C1/C2/C3 loop iteration, write the capstone reflection in
the worker report or scratch notes:

```text
Overall goal:   final concrete BP-native succinct RMQ profile
Current gap:    the selected concrete C1/C2 component or final integration still not consumed
Hard part:      routing queries through charged o(n) payloads without answer/proof-only fields
This iteration: the largest coherent proof/construction step toward it
Not doing:      adjacent helper/docs/blocker work that would leave it untouched
```

If the selected work does not directly reduce the distance to the final
`2*n + o(n), O(1)` theorem, choose a harder target before editing. The loop is
allowed to build helper lemmas, but only while immediately consuming them in
the compact false-select locator, BP macro/close component, close-access
witness, or final join.

For this target, local wins are iteration checkpoints. A descriptor kernel,
sample table, range-min/max summary table, local codebook, endpoint lemma, or
adapter theorem should be followed in the same unattended loop by the next
attempt to consume it in the concrete C1 profile, close-access witness, or final
join. Do not stop merely because the local layer is useful and verified.

The loop-stop audit is a gate, not a confession box. If the audit concludes the
stop is invalid, the worker is not allowed to produce a final completion report;
it must immediately continue with the next obvious theorem in the same owned
file surface. A report that admits "this is not a valid stop" without continuing
is a loop protocol failure.

The next rounds are positive-construction rounds. The existing no-go theorems
already rule out the tempting false shortcuts. A worker should not stop after
another blocker unless it attempted the named C1/C2 construction and proved
that the requested target statement itself is ill-specified. Failed
construction attempts, even serious ones, should normally be treated as
iteration notes and used to choose the next repaired positive construction.

Invalid stop points for this final path:

- adding only a field such as `blockIndex`, `macroCosted`, `codeOfBlock`, or an
  abstract `selectCosted`/`selectCloseCosted`;
- adding only an adapter theorem while the concrete builder remains in the same
  owned file surface;
- updating docs to say "concrete builder remains" and then stopping;
- proving a profile over a hypothetical family with no concrete instance.
- re-proving or restating the conditional
  `concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile`
  without producing the concrete false-only close-access witness that it consumes.
- proving a `PayloadLiveBPCloseAccessFamily` inhabitant whose costed functions
  first compute `bpCloseOfInorder?`, `rankPrefix`, `scanWindow`, or another
  semantic reference answer and then charge an unrelated/dummy payload read.
- proving a compact-select/close-access component surface whose exactness still
  comes from proof fields such as `descriptor_some_exact`,
  `descriptor_none_exact`, `descriptor_word_choice_exact`, or a free
  `descriptorIndex`, while the compact payload builder remains missing.
- reviving the pruned `SparseDenseFalseSelectCloseData.profile` route or a
  sibling sparse/dense close-access adapter as a final checkpoint while the
  super/local/exception tables are not constructed from `shape.bpCode` and the
  branch-exactness fields are still supplied as assumptions.
- proving `builtTwoLevelFalseSelectCloseData_profile`,
  `builtTwoLevelFalseSelectBPCloseAccessDirectory_profile`, or an equivalent
  adapter over the full-width two-level select block table as a final C1
  checkpoint. That path is exact and useful as a baseline, but its
  `builtTwoLevelFalseSelectBlockOverhead_ge_bpCode_length_succ` theorem makes
  the payload linear.
- repairing the dense/local route by storing one full-width row per
  high-frequency local interval, unless the same theorem proves that the row
  count and field widths fit the named little-o C1 overhead. Splitting an
  absolute pointer into charged full-width fields is not a succinct repair by
  itself.
- storing sparse-local explicit answers as absolute BP positions at
  local-entry frequency without a LittleOLinear payload proof. The intended
  compact path stores relative offsets in padded exception blocks, or supplies
  a charged variable-length base directory with its own budget proof.
- leaving `descriptorIndex` or an analogous routing function as an uncharged
  arbitrary function that could hide search, predecessor, or oracle work.
- producing a technically substantial theorem cluster that does not feed the
  current compact false-select, close-access, BP macro/close, or final-join
  target.
- proving only a local descriptor-choice theorem, local range-min/max summary
  table, block codebook, or partial charged read profile while the C1/C2
  concrete component profile remains the next obvious step.
- proving `twoWordDescriptor...` facts without a global descriptor-backed
  `selectCloseCosted_exact` theorem over all close indices.
- proving a global packed descriptor-backed `selectCloseCosted_exact` while the
  only descriptor-space theorem is an exact full per-occurrence local-delta-slot
  payload length, with no `LittleOLinear` compact-budget theorem under the
  machine-word model.
- proving a rank-summary exactness theorem and then claiming it locates select
  queries without a charged occurrence-to-word locator.
- proving `PayloadLiveBPRangeMinMaxSummaryTable...` facts without a concrete
  close-LCA answer theorem that consumes the summaries plus charged endpoint
  repair.
- proving a position-bearing BP range-witness or block-pair macro-candidate
  profile, or an `_exact_of_prefix_pos` theorem, without a global close-LCA
  answer theorem that consumes the witness via charged endpoint-fringe repair
  and the leftmost-minimum-excess BP semantics.
- proving a charged endpoint-fringe macro/profile whose strongest exactness
  theorem is still conditional on a supplied merged-candidate hypothesis such
  as `hmerge`, rather than proving that merge fact from the built payload
  entries and BP/RMQ semantics.
- proving a selected-block or selector-cell bridge whose exactness assumes the
  selector cell already stores `bpRangeArgMinBlock` or another semantic answer,
  without building and routing the concrete local/global/top selector tables in
  the same loop.
- repairing the machine-word side condition or balanced-prefix invariant for
  the BP range-min/max summary layer and then stopping before the next concrete
  answer-close attempt.
- omitting the machine-word side condition for a newly charged fixed-width
  table or payload-word read.
- leaving a misleading theorem name that claims more than its statement proves,
  such as an `...select...` theorem that does not mention `select`.
- stopping after hard proof failures, new local blockers, or a partial
  obstruction dossier while the next positive construction remains obvious.
- sending a completion report whose own loop-stop audit says the stop is
  invalid, instead of continuing immediately to the next iteration.

Valid stop points:

- the owned concrete component profile lands, not merely a helper profile, and
  the next step truly crosses into another worker's owned branch;
- a concrete construction attempt proves the target statement is impossible as
  stated, with a minimal obstruction theorem and a precise replacement target;
- at least fifty serious attempts at the named positive construction hit the
  same design-level brick wall, with enough evidence for the coordinator to
  choose a new invariant, representation, or target statement;
- the final theorem above typechecks and the full gate passes.
