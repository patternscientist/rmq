# Succinct RMQ Final Path Spec

This is the worker-visible spec for the remaining path to a genuine
`2*n + o(n), O(1)` BP-native succinct RMQ theorem.

The goal is not another conditional wrapper. The final path must be witnessed by
payload that the query actually reads, machine-word-bounded word primitives, and
compiled exactness/cost/profile theorems.

## Current Inputs

The current merged surface provides useful partial surface:

- The close/LCA side has a payload-live macro/micro BP close-navigation join.
  Its key capstone is:

  ```lean
  theorem RMQ.SuccinctCloseProposal
      .PayloadLiveMacroMicroBPCloseNavigationFamily
      .two_n_plus_o_built_query_profile :
    ...
  ```

  This consumes payload-live rank/select plus a payload-live macro/micro
  LCA-close family. It still leaves the macro side abstract through a
  `macroCosted`/`split_exact` style interface.

- The close/LCA side also has a concrete negative theorem:

  ```lean
  theorem RMQ.SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient :
    ...
  ```

  This proves that a macro keyed only by
  `(blockOfClose leftClose, blockOfClose rightClose)` is not exact, already on
  a four-node right spine with `blockSize = 3`.

- The close/LCA side has also checked the obvious endpoint-sensitive dense
  fallback:

  ```lean
  theorem RMQ.SuccinctCloseProposal
      .denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile :
    ...

  theorem RMQ.SuccinctCloseProposal
      .denseAllCloseBPCloseLCAOverhead_not_littleO :
    ...
  ```

  This fallback is exact, charged, and constant-query, but its all-close
  endpoint table is not `o(n)`. The next concrete macro should therefore be a
  real succinct BP-excess/RMQ macro with charged endpoint-fringe repair, not a
  dense direct-access endpoint table.

- The select side proves the current query-shape forcing facts:

  ```lean
  theorem RMQ.SuccinctSelectProposal
      .SelectSampleWordExact.selected_position_in_read_word :
    ...

  theorem RMQ.SuccinctSelectProposal
      .TwoLevelPayloadLiveStoredWordSelectData
      .selected_position_in_read_word_of_sample :
    ...

  theorem RMQ.SuccinctSelectProposal
      .SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word :
    ...

  theorem RMQ.SuccinctSelectProposal
      .TwoLevelPayloadLiveStoredWordSelectData
      .selected_wordIndex_eq_of_sample :
    ...

  theorem RMQ.SuccinctSelectProposal
      .SelectSampleWordExact
      .shared_aligned_read_word_forces_same_wordIndex :
    ...

  theorem RMQ.SuccinctSelectProposal
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

## Component 1: Descriptor-Based Select

The current `blockIndex` hook is not enough. The final select component should
let one local entry cover a bounded run of payload words by storing a small
descriptor that chooses the payload word before running `wordSelect`.

Target query shape:

```text
coarse locator read
local descriptor read
bounded word-choice primitive over descriptor payload
payload word read
wordSelect
```

Do not revive the one-entry/one-aligned-word shortcut. The merged theorem
`SelectSampleWordExact.selected_wordIndex_eq_of_aligned_read_word` says that
an aligned read word is forced to be the selected position's own chunk. Sharing
is only legitimate if the descriptor includes a charged way to choose the final
payload word. The sharper blocker
`TwoLevelPayloadLiveStoredWordSelectData.shared_local_locator_forces_same_selected_wordIndex`
rules out a shared local locator that reads one aligned payload word while
serving selected bits in different chunks.

The component should expose a surface equivalent to:

```lean
structure DescriptorPayloadLiveStoredWordSelectData
    (bits : List Bool) (overhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits bits.length

  auxPayload : List Bool
  auxPayload_length : auxPayload.length = overhead

  selectCosted : Bool -> Nat -> Costed (Option Nat)
  selectCosted_cost_le :
    forall target occurrence,
      (selectCosted target occurrence).cost <= queryCost
  selectCosted_exact :
    forall target occurrence,
      (selectCosted target occurrence).erase =
        Succinct.select target bits occurrence

  payload_word_length_le_machine :
    forall {word : List Bool},
      List.Mem word (payloadWordsReadByQuery target occurrence) ->
        word.length <= SuccinctRankProposal.machineWordBits bits.length

  word_choice_exact :
    forall target occurrence pos,
      Succinct.select target bits occurrence = some pos ->
        selectedPayloadWordIndex target occurrence = pos / wordSize
```

The final theorem need not use exactly this structure name, but it must prove
these facts for a concrete construction. A structure that merely stores
`selectCosted` as a supplied function is only an interface and does not retire
the select blocker.

Expected concrete builder theorem shape:

```lean
theorem descriptorSelectDataOfChunks_profile
    {bits : List Bool}
    (hword : 0 < wordSize)
    (hmachine :
      wordSize <= SuccinctRankProposal.machineWordBits bits.length)
    ... :
    let data :=
      descriptorSelectDataOfChunks bits hword hmachine ...
    data.auxPayload.length <= descriptorSelectOverhead bits.length /\
      (forall target occurrence,
        (data.selectCosted target occurrence).cost <= descriptorSelectQueryCost) /\
      (forall target occurrence,
        (data.selectCosted target occurrence).erase =
          Succinct.select target bits occurrence) /\
      ...
```

Expected family theorem shape:

```lean
theorem DescriptorPayloadLiveStoredWordSelectFamily
    .constant_query_profile
    (family : DescriptorPayloadLiveStoredWordSelectFamily overhead queryCost) :
    LittleOLinear overhead /\
      forall bits,
        ((family.component bits).auxPayload.length = overhead bits.length) /\
        (forall target occurrence,
          ((family.component bits).selectCosted target occurrence).cost <=
            queryCost) /\
        (forall target occurrence,
          ((family.component bits).selectCosted target occurrence).erase =
            Succinct.select target bits occurrence)
```

## Component 2: Concrete Macro/Micro BP Close-LCA

The merged close-navigation join is valuable, but the macro side must become
concrete. The next BP worker should not add another family wrapper around
`macroCosted`.

Do not use a macro directory keyed only by endpoint close-block pair. The merged
theorem `SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient` proves
that design false. A viable macro must store enough endpoint-sensitive fringe
information, include local offsets inside endpoint blocks, or use a real
BP-excess/RMQ macro over block summaries whose answer is then repaired by
charged local micro queries.

Do not use the fully dense all-close endpoint fallback as the final space
witness. `SuccinctCloseProposal.denseFallbackPayloadLiveMacroMicroBPCloseLCADirectory_profile`
shows it is exact and charged, but
`SuccinctCloseProposal.denseAllCloseBPCloseLCAOverhead_not_littleO` proves its
auxiliary payload is not `o(n)`.

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

## Component 3: Final Join

After Components 1 and 2 land, the coordinator or join worker should combine:

- exact `shape.bpCode` payload length `2*n`;
- payload-live rank with bounded machine words;
- descriptor-based payload-live select;
- concrete macro/micro BP close-LCA;
- the Worker A close-navigation join, adapted if necessary.

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

## Loop Rules For This Target

Workers must run the stop audit from `docs/CODEX_AUTONOMY.md`.

At the start of every C1/C2/C3 loop iteration, write the capstone reflection in
the worker report or scratch notes:

```text
Overall goal:   final concrete BP-native succinct RMQ profile
Current gap:    the missing descriptor select, macro/close component, or join
Hard part:      the concrete payload-live construction most tempting to defer
This iteration: the largest coherent proof/construction step toward it
Not doing:      adjacent helper/docs/blocker work that would leave it untouched
```

If the selected work does not directly reduce the distance to the final
`2*n + o(n), O(1)` theorem, choose a harder target before editing. The loop is
allowed to build helper lemmas, but only while immediately consuming them in
the descriptor builder, BP macro/close component, or final join.

For this target, local wins are iteration checkpoints. A descriptor kernel,
sample table, range-min/max summary table, local codebook, endpoint lemma, or
adapter theorem should be followed in the same unattended loop by the next
attempt to consume it in the concrete C1/C2 profile. Do not stop merely because
the local layer is useful and verified.

The next rounds are positive-construction rounds. The existing no-go theorems
already rule out the tempting false shortcuts. A worker should not stop after
another blocker unless it attempted the named C1/C2 construction and proved
that the requested target statement itself is ill-specified.

Invalid stop points for this final path:

- adding only a field such as `blockIndex`, `macroCosted`, `codeOfBlock`, or an
  abstract `selectCosted`;
- adding only an adapter theorem while the concrete builder remains in the same
  owned file surface;
- updating docs to say "concrete builder remains" and then stopping;
- proving a profile over a hypothetical family with no concrete instance.
- producing a technically substantial theorem cluster that does not feed the
  current descriptor-select, BP macro/close, or final-join target.
- proving only a local descriptor-choice theorem, local range-min/max summary
  table, block codebook, or partial charged read profile while the C1/C2
  concrete component profile remains the next obvious step.
- stopping after one or two hard proof failures without a brick-wall dossier
  explaining why the target requires a fundamental redesign.

Valid stop points:

- the owned concrete component profile lands, not merely a helper profile, and
  the next step truly crosses into another worker's owned branch;
- a concrete construction attempt proves the target statement is impossible as
  stated, with a minimal obstruction theorem and a precise replacement target;
- at least three serious attempts at the named positive construction hit the
  same design-level brick wall, with enough evidence for the coordinator to
  choose a new invariant, representation, or target statement;
- the final theorem above typechecks and the full gate passes.
