# Succinct RMQ Research And Capstone Plan

Date: 2026-06-20.

This note records the current research-backed path to a genuine
`2*n + o(n)`-bit, `O(1)`-query BP-native succinct RMQ theorem. It complements
the worker contract in `docs/SUCCINCT_FINAL_PATH.md`.

## Current Audit

The latest proof rounds did not close the capstone, but they did prune several
cheap false closes:

- `SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient`: a BP
  close/LCA macro keyed only by endpoint close-block pair is not exact.
- `SuccinctCloseProposal.denseAllCloseBPCloseLCAOverhead_not_littleO`: the
  direct all-close endpoint table is exact and charged, but not `o(n)`.
- `SuccinctSelectProposal.SelectSampleWordExact.shared_aligned_read_word_forces_same_wordIndex`
  and the two-level `shared_local_locator...` lemmas: a select locator that
  reads one aligned payload word can only serve successful selects in that same
  payload chunk.

These are useful anti-vacuity facts, but they should not define the next round.
Since then, the relative summary component has landed:
`concreteBPRelativeMinMaxArgSummaryTable_canonical_compact_payload_profile`
provides a concrete, payload-live, machine-word-bounded, unconditional
`LittleOLinear` summary table for BP block min/max/arg data. That closes the
old "summary envelope is only abstract" gap.

The remaining close-side wall is therefore narrower and sharper: build the
option-1 compact rmM/min-max-tree-style interior navigator over complete-block
minimum candidates. The next positive component theorem is
`concreteBPRelativeRmmInteriorDirectory_profile`, not another scan, dense table,
or blocker catalog entry.

## Remaining Components

The capstone splits into three concrete components.

1. C1 descriptor-based select.
   Replace the disproven shared aligned-word locator with a charged descriptor
   that chooses the payload word, then runs in-word select.

2. C2 concrete macro/micro BP close-LCA.
   Replace abstract `macroCosted` with a real BP-excess/RMQ macro over block
   summaries plus charged endpoint-fringe repair. The adopted subtarget is the
   concrete interior rmM/min-max-tree navigator
   `concreteBPRelativeRmmInteriorDirectory_profile`, consumed immediately by
   `concretePayloadLiveRelativeRmmBPCloseMacro_profile`.

3. C3 final join.
   Combine exact `shape.bpCode` payload length `2*n`, payload-live rank, C1,
   C2, and the close-navigation join into a concrete family theorem with
   `LittleOLinear overhead`, exact query erasure, bounded query cost, and the
   lower-bound tie `EncodingLowerBound.logSlackLower n <= 2*n + overhead n`.

## Canonical Constructions

The project does not need a new data-structure invention. The likely winning
path is to formalize known structures in the existing payload-live model.

### C1: Select Descriptor

Use a Clark/Vigna-style two-level select directory:

```text
coarse locator read
local descriptor read
charged word-choice inside the local descriptor
payload word read
wordSelect
```

The exact constants can be loose. The important facts are:

- every payload word used by `wordSelect` is machine-word bounded;
- the descriptor computes the actual word containing the selected position;
- the auxiliary descriptor payload is `o(n)`;
- `selectCosted` erases to `Succinct.select`.

### C2: BP-Excess Macro

Use the Navarro-Sadakane range min-max tree idea over BP excess:

- split the BP bitstring into blocks;
- store block excess summaries, especially minimum/maximum information;
- answer the macro portion over summaries;
- repair endpoint fringes using charged local micro queries.

This is the canonical way to avoid both false designs already ruled out in the
repo: endpoint-block-pair-only tables are not exact, and fully dense endpoint
tables are not `o(n)`.

The current option-1 specialization is deliberately modest: prove only the
interior full-block range-minimum operation needed by the close/LCA macro. The
directory should expose a costed `rangeMinCosted startBlock count` whose erasure
is

```lean
some
  (bpRangeMinExcess shape canonicalBlockSize startBlock count,
   bpRangeArgMinPrefixPos shape canonicalBlockSize startBlock count)
```

under the usual nonempty in-bounds hypotheses, with a constant query bound and
`LittleOLinear` payload. Directly scanning the relative per-block summaries is a
valid obstruction/diagnostic theorem but not a component close, because its
charged cost grows with the number of interior blocks.

### C2 Micro Layer

Use a Four-Russians plus-minus-one RMQ table for local blocks. This repo already
has the right precedent in the Fischer-Heun/microtable development: finite block
shape/signature universes, exact table lookup, and counted payload accounting.
The BP local block can follow the same pattern rather than inventing a new
universe from scratch.

### C3 Final Join

The final theorem should be a concrete family theorem, not a profile over
hypothetical operations. It should expose the upper bound and the existing lower
bound in the same statement family:

```lean
LittleOLinear overhead /\
payload.length = 2 * n + overhead n /\
queryCosted.cost <= queryCost /\
queryCosted.erase = some (scanWindow shape.representative left len) /\
EncodingLowerBound.logSlackLower n <= 2 * n + overhead n
```

## Formalization Frontier

The likely novelty remains strong:

- existing Coq succinct work covers rank/select and LOUDS-style trees, but not
  a BP-excess RMQ/LCA structure with this RMQ lower-bound connection;
- CSLib does not yet have this family;
- this repo already has a formal Catalan-style lower bound for exact RMQ;
- a payload-live, machine-word-bounded `2*n + o(n)`, `O(1)` RMQ theorem would
  pair a succinct upper construction with a matching lower-bound story in one
  Lean development.

## Recommended Order

1. C2 interior first: land
   `concreteBPRelativeRmmInteriorDirectory_profile` for the option-1 compact
   rmM/min-max-tree-style navigator over complete-block minimum candidates.
2. Consume that in `concretePayloadLiveRelativeRmmBPCloseMacro_profile`, then
   `concreteCompactBPCloseLCADirectory_profile`.
3. C3 final join, including the lower-bound tie.
4. C1 descriptor/select work should continue only if the final BP-native join
   still needs a select-side gap closed; it should not displace the current C2
   interior target.

For the next worker round, a useful branch must land a concrete component
profile or a concrete construction consumed by such a profile. More negative
theorems are acceptable only if they arise from a serious attempt at that
specific construction and make the original target provably ill-specified.

## References

- M. J. Jacobson. Space-efficient static trees and graphs. FOCS 1989.
- D. Clark. Compact Pat Trees. PhD thesis, University of Waterloo, 1996.
- M. A. Bender and M. Farach-Colton. The LCA Problem Revisited. LATIN 2000.
  https://www.dcc.fc.up.pt/~pribeiro/aulas/taa1920/lca_rmq.pdf
- S. Vigna. Broadword Implementation of Rank/Select Queries. WEA 2008.
  https://vigna.di.unimi.it/ftp/papers/Broadword.pdf
- J. Fischer and V. Heun. Space-Efficient Preprocessing Schemes for Range
  Minimum Queries on Static Arrays. SIAM J. Comput. 40(2):465-492, 2011.
  https://arxiv.org/abs/0812.2775
- G. Navarro and K. Sadakane. Fully Functional Static and Dynamic Succinct
  Trees. ACM Trans. Algorithms 10(3), 2014.
  https://arxiv.org/abs/0905.0768
- R. Affeldt, J. Garrigue, and K. Tanaka. Proving Tree Algorithms for Succinct
  Data Structures. ITP 2019.
  https://arxiv.org/abs/1904.02809
  Code: https://github.com/affeldt-aist/succinct
- G. Navarro. Compact Data Structures: A Practical Approach. Cambridge
  University Press, 2016.
