# Succinct RMQ Research And Capstone Plan

Date: 2026-06-20.

This note records the current research-backed path to a genuine
`2*n + o(n)`-bit, `O(1)`-query BP-native succinct RMQ theorem. It complements
the worker contract in `docs/SUCCINCT_FINAL_PATH.md`.

## Current Audit

This note began as the research plan for the succinct capstone. The capstone
has since landed; the items below are retained as design provenance and
anti-vacuity guardrails. Earlier proof rounds pruned several cheap false
closes:

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

Since that note was written, the concrete compact close/LCA directory, the
relative-split false-close/select witness, and the BP-native join have landed.
The public total capstone is
`SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_n_plus_o_constant_query_profile`.
The old full
`SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily` remains
useful scaffold, but the final capstone consumes the concrete false-only BP
close-access witness:

```lean
selectCloseCosted idx  -- exact for bpCloseOfInorder? shape idx
rankCloseCosted pos    -- exact for rankPrefix false shape.bpCode pos
```

This was not a new semantic burden. `bpCloseOfInorder?` was already proved to
be `select false` over `shape.bpCode`; the real burden was the compact
payload-live locator for that select operation.

## Remaining Components

Historically, the capstone split into three concrete components, with C1 as the
binding constraint. All three have now been consumed by the final theorem.

1. C1 compact false-select / close-access.
   Replace the disproven shared aligned-word locator with a charged compact
   locator that chooses the payload word for `select false shape.bpCode idx`,
   then runs the existing in-word `RAM.selectBoolWord`.

2. C2 concrete macro/micro BP close-LCA.
   This is currently the strongest landed side of the construction: the compact
   interior navigator and concrete compact close/LCA profile are available as
   the close-side consumer. Further local-decoder hardening is allowed later,
   but it is not the current capstone blocker.

3. C3 final join.
   Combine exact `shape.bpCode` payload length `2*n`, payload-live rank-false,
   C1 false-select/close access, C2 close/LCA, and the close-navigation join
   into a concrete family theorem with `LittleOLinear overhead`, exact query
   erasure, bounded query cost, and the lower-bound tie
   `EncodingLowerBound.logSlackLower n <= 2*n + overhead n`.

## Canonical Constructions

The project does not need a new data-structure invention. The likely winning
path is to formalize known structures in the existing payload-live model.

### C1: Compact False-Select Locator

Use a Clark/RRR/Vigna-style select directory specialized first to close
parentheses:

```text
coarse select-sample read
compact locator / local descriptor read
charged word-choice from the locator payload
payload word read
RAM.selectBoolWord
```

The exact constants can be loose. The important facts are:

- every payload word used by `RAM.selectBoolWord` is machine-word bounded;
- the compact locator computes the actual word containing the selected close;
- the auxiliary locator payload is `o(n)`;
- `selectCloseCosted` erases to `bpCloseOfInorder? shape idx`.

The existing `RAM.selectBoolWord` primitive should be reused before adding any
new RAM primitive. It handles the final in-word select once the word is known.
It does not solve the global locator problem by itself, and rank summaries alone
do not invert an occurrence into a word index in constant time. Rank summaries
can be reused for counted local counts or verification, but the route from
`idx` to the selected payload word must be a real payload-live compact locator
or dense/sparse select directory.

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

1. C1 compact false-select first: land a concrete payload-live close-select
   locator profile whose query uses charged sample/descriptor reads, reads a
   bounded BP payload word, calls `RAM.selectBoolWord`, proves
   `bpCloseOfInorder?` exactness, and proves `LittleOLinear` auxiliary payload.
2. Package rank-false plus close-select as the concrete `BPCloseAccessDirectory`
   or equivalent false-only access witness. A generic conditional join is fine
   as helper glue, but it is not a stop point without this witness.
3. C3 final join, including the lower-bound tie. Consume the concrete access
   witness and the existing concrete compact close/LCA directory to produce the
   unconditional `2*n + o(n), O(1)` BP-native RMQ theorem.
4. After the capstone, optionally generalize the false-only close-select witness
   back to a full two-target rank/select family and harden the local BP decoder.

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
