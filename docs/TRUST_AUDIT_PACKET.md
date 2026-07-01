# Trust Audit Packet

Snapshot: 2026-07-01. This is the compact packet to hand to a skeptical
Lean/formalization reviewer before asking for a broader library-readiness
review. It focuses on the public succinct RMQ headline theorem, its alias
chain, its cost/space model, and the main anti-oracle checks.

## Quick Reproduction

From the repository root:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
lake env lean scripts\headline_axiom_check.lean
```

The full gate builds the public roots, checks hygiene, runs curated axiom
scripts, runs succinct cost/space lints, runs compatibility-shim lints, and
finishes with `git diff --check`.

For the focused first-order Word-RAM anti-oracle boundary used by the
interpreted RMQ and rank/select capstones, also see
`docs/WORD_RAM_REVIEW_PACKET.md` and run:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\review_wordram.ps1
```

## Public Headline Alias

The main public RMQ name lives in `RMQ/Headlines.lean`:

```lean
abbrev succinctRMQTwoNPlusOConstantQuery :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
```

Alias chain:

```text
RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
  = RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
    -> builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_n_plus_o_constant_query_profile
    -> builtGenericSparseExceptionBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
    -> concreteBPNativeSuccinctRMQFamily_two_n_plus_o_constant_query_profile
         builtGenericSparseExceptionSelectBPCloseAccessFamily
```

The additive interpreted public alias is:

```lean
abbrev succinctRMQTwoNPlusOConstantQueryInterpreted :=
  RMQ.SuccinctFinal.builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_whole_query_interpreted_profile
```

It has the same payload/lower-bound/cost/exactness theorem shape as the main
capstone, but the query clause uses
`SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryInterpretedCosted`: a
closed first-order whole-query controller whose leaves are interpreted
close-select, compact close/LCA, and register-backed answer-rank operations.

## Theorem Statement

The construction-heavy theorem name is intentionally verbose because it exposes
the model and construction path:

```lean
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile :
    let accessFamily :=
      builtGenericSparseExceptionSelectBPCloseAccessFamily
    SuccinctSpace.LittleOLinear
        (concreteBPNativeSuccinctRMQOverhead
          genericSparseExceptionBPCloseAccessOverhead) /\
      forall n : Nat,
        EncodingLowerBound.doubledLogSlackLower n <=
          2 *
            (2 * n +
              concreteBPNativeSuccinctRMQOverhead
                genericSparseExceptionBPCloseAccessOverhead n) /\
        EncodingLowerBound.logSlackLower n <=
          2 * n +
            concreteBPNativeSuccinctRMQOverhead
              genericSparseExceptionBPCloseAccessOverhead n /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (accessFamily.directory shape).payload.length <=
              genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            (concreteBPNativeSuccinctRMQPayload
              accessFamily shape).length =
              2 * n +
                concreteBPNativeSuccinctRMQOverhead
                  genericSparseExceptionBPCloseAccessOverhead n) /\
        (forall shape left right,
          (concreteBPNativeSuccinctRMQQueryCosted
            accessFamily shape left right).cost <=
              concreteBPNativeSuccinctRMQQueryCost
                SuccinctSelect.sparseDenseFalseSelectQueryCost) /\
        (forall {shape : Cartesian.CartesianShape},
          List.Mem shape (Cartesian.shapesOfSize n) ->
            forall {left len : Nat},
              0 < len ->
                left + len <= n ->
                  (concreteBPNativeSuccinctRMQQueryCosted
                    accessFamily shape left (left + len)).erase =
                    some (scanWindow shape.representative left len))
```

Read literally, this says:

- the auxiliary overhead is `o(n)`;
- the upper bound has `2*n + overhead n` payload bits;
- the lower-bound side is present in both ordinary and doubled Catalan-slack
  forms;
- the close-access payload is itself bounded by the advertised overhead;
- every query has a fixed modeled cost bound; and
- every valid half-open query over every Cartesian shape of size `n` erases to
  the reference leftmost RMQ answer `scanWindow shape.representative left len`.

## Axiom Excerpt

Run:

```powershell
lake env lean scripts\headline_axiom_check.lean
```

Current excerpt for the public headline path:

```text
'RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectWordBoundedNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightFamilyProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.rankSelectCompressedFIDFixedWeightInterpretedFamilyProfile' depends on axioms:
  [propext, Classical.choice, Quot.sound]
'RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery' depends on axioms:
  [propext, Classical.choice, Quot.sound]
```

The gate rejects `sorryAx` and `Lean.ofReduceBool`. It also scans checked
source for `sorry`, `admit`, custom `axiom`, `unsafe`, `opaque`,
`implemented_by`, `partial`, `extern`, `noncomputable`, `native_decide`, and
`import Mathlib`.

## Dependency Sketch

The final query is:

```lean
concreteBPNativeSuccinctRMQQueryCosted accessFamily shape left right
```

Its shape is:

1. Select the close position of the left endpoint using
   `accessFamily.directory shape.selectCloseCosted`.
2. Select the close position of the right endpoint the same way.
3. Run the compact BP close/LCA directory:
   `SuccinctClose.concreteBPNativeCloseDirectory`.
4. Rank the answer close position back to an inorder index using
   `accessFamily.directory shape.rankCloseCosted`.
5. Return the resulting representative-array index.

The abstract composition surface is named `BPCloseAccessDirectory`. The file
explicitly calls it a weak compatibility surface because its costed methods are
fields. The public headline does not stop at an arbitrary inhabitant of that
surface: its concrete access family is

```lean
builtGenericSparseExceptionSelectBPCloseAccessFamily
```

and its directory is defined by:

```lean
payload :=
  (builtRelativeSplitBPCloseRankData shape).auxPayload ++
    (GenericSelect.sparseExceptionSelectSource shape.bpCode false).payload

selectCloseCosted := fun idx =>
  (GenericSelect.sparseExceptionSelectSource
    shape.bpCode false).selectPositionCosted idx

rankCloseCosted := fun pos =>
  (builtRelativeSplitBPCloseRankData shape).rankCosted false pos
```

The exactness and cost facts for those operations come from:

- `GenericSelect.sparseExceptionSelectSource_profile shape.bpCode false`,
  which proves select payload length, `LittleOLinear` overhead, cost bound,
  exact select semantics, and machine-word-bounded read words;
- `builtRelativeSplitBPCloseRankData`, which is a concrete two-level
  payload-live rank structure over `shape.bpCode`;
- `SuccinctSpace.select_false_bpCode_eq_bpCloseOfInorder?`, which identifies
  false-select in the BP code with the Cartesian inorder close lookup;
- the compact close/LCA profile for
  `SuccinctClose.concreteBPNativeCloseDirectory`; and
- `concreteBPNativeSuccinctRMQQueryCosted_exact`, which composes select-close,
  LCA-close, rank-close, and the RMQ reference semantics.

So the theorem still uses a generic composition interface, but the headline
inhabitant supplies concrete payload and query definitions from rank/select and
close-navigation components rather than leaving correctness hidden in external
callbacks.

## Model Glossary

- `Costed a`: a value of type `a` plus a natural-number model cost. `erase`
  forgets the cost.
- `RAM.Exec`: a shallow primitive-trace model used for small array/word/read
  executions. It records model steps and converts to `Costed`.
- Payload bits: the modeled stored bits counted by space theorems. These are
  separate from proof fields carried by Lean structures.
- Proof-only fields: certificates and invariants used to prove exactness or
  bounds. They are not charged as stored payload bits.
- Unit-cost indexed read: the standard word-RAM modeling assumption that a
  bounded table/word read costs one primitive step. This is not a claim about
  Lean `List` runtime.
- Machine-word bound: theorems such as read-word-length bounds show that the
  queried words fit under the repository's `machineWordBits` function.

## Non-Claims

This packet does not claim:

- the algorithmic result is new data-structure theory;
- Lean's native execution of lists or structures has the modeled runtime;
- the final theorem is a production-ready serialized packed implementation;
- all BP tree-navigation operations are already available;
- the compressed/FID rank/select replay is a single closed machine-code
  program rather than a bridge-backed word-RAM model theorem; or
- the repo is CSLib-ready as-is.

The claim is narrower and stronger in the formalization sense: the repo gives
a machine-checked Lean stack connecting exact RMQ semantics, Cartesian-shape
counting lower bounds, payload-accounted BP/rank/select upper-bound machinery,
and a constant-query word-RAM-style succinct RMQ profile.

## Minimal Imports

Headline aliases:

```lean
import RMQ.Headlines

#check RMQ.Headlines.succinctRMQTwoNPlusOConstantQuery
#check RMQ.Headlines.exactRMQLowerBoundDoubledCatalanSlack
```

Standalone spokes:

```lean
import RMQRankSelect
import RMQBPNavigation
import RMQUnionFind
```

Checked downstream examples:

```powershell
lake build RMQExamples
```

Focused spoke checks:

```powershell
lake build RMQRankSelect
lake env lean scripts\rank_select_axiom_check.lean

lake build RMQBPNavigation
lake env lean scripts\bp_navigation_axiom_check.lean

lake build RMQUnionFind
lake env lean scripts\union_find_axiom_check.lean
```

## Reviewer Reading Order

1. `RMQ/Headlines.lean`
2. `docs/WHAT_IS_PROVED.md`
3. `docs/TRUST_BASE.md`
4. this packet
5. `scripts/headline_axiom_check.lean`
6. `RMQ/Core/SuccinctFinal.lean`, starting at
   `builtGenericSparseExceptionSelectBPCloseAccessDirectory` and
   `builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile`
