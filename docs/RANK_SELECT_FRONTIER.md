# Rank/Select Frontier

Snapshot: 2026-06-23. This note separates the reusable rank/select data
structure track from the RMQ capstone while keeping both tracks in the same Lean
repository for now.

## Research Target

For plain bitvectors, the rank/select analogue of the RMQ `2n + o(n), O(1)`
headline is:

- store the `n` input bits plus `o(n)` auxiliary bits;
- support `access i`, `rank b i`, and `select b k`;
- charge a uniform constant number of modeled word-RAM/indexed-access steps per
  query;
- keep the reference semantics exactly `bits[i]?`,
  `Succinct.rankPrefix b bits i`, and `Succinct.select b bits k`.

For compressed/FID-style bitvectors, the sharper target changes the leading
term from `n` to an entropy-sensitive budget.  The natural long-term theorem is
`log2 (Nat.choose U m) + o(U)` or `log2 (Nat.choose U m) + o(m)` depending on
whether the model promises fast operations over the whole universe length `U`
or over a sparse set with occurrence count `m`.  This repo does not yet have a
binomial/entropy lower-bound layer, so the first compressed milestone should be
a carefully scoped predecessor: define the finite family, state which parameter
the lower-order term is measured against, and only then connect it to
rank/select queries.

## What Is Already Here

- `RMQ/Core/Succinct.lean` defines the reference operations
  `Succinct.rankPrefix`, `Succinct.select`, exact bounds/monotonicity lemmas,
  and the RAM primitive bridges `rankBoolWordPrefix_toCosted_run` and
  `selectBoolWord_toCosted_run`.
- `RMQ/Core/SuccinctSpace.lean` already has the payload-live interface pieces:
  `PayloadLiveStoredWordRankData`, `PayloadLiveStoredWordSelectData`,
  `RankSelectDirectory`, `PayloadLiveStoredWordRankSelectFamily`, and the
  combined profile theorem
  `PayloadLiveStoredWordRankSelectFamily.constant_query_profile`.
- `RMQ/Core/SuccinctRankProposal.lean` contains the Jacobson-side construction
  surface: canonical super/block samples, chunk payload-word bridges, canonical
  overhead functions, and sampled-family theorem targets.
- `RMQ/Core/SuccinctSelectProposal.lean` contains the Clark-side construction
  surface: super/block select samples, locator exactness lemmas, two-level
  rank/select joins, and the later sparse/dense false-select work needed by the
  BP RMQ capstone.
- `RMQ/Core/RankSelectSpec.lean` is the new extraction point.  It wraps the
  existing rank/select directory with explicit stored-bit `access` and exposes
  the public plain-bitvector theorem shape
  `RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile`.

## Extract First

The first extraction should be a public spec layer, not a file move:

1. Keep `Succinct.rankPrefix` and `Succinct.select` as the reference semantics.
2. Use `RankSelectSpec.BitVectorRankSelectDirectory` as the plain bitvector
   surface: payload equals `bits ++ aux`, access reads the stored bits, and
   rank/select reuse `SuccinctSpace.RankSelectDirectory`.
3. Feed the new surface from existing payload-live data with
   `RankSelectSpec.BitVectorRankSelectDirectory.ofPayloadLiveRankSelectData`.
4. Keep `SuccinctRankProposal` and `SuccinctSelectProposal` as construction
   modules until their builders are strong enough to instantiate the public
   family theorem directly.

This keeps RMQ imports stable: `RMQ.lean` imports `RankSelectSpec` after
`SuccinctSpace` and before the proposal modules, while the existing
`SuccinctFinal` path remains downstream of the proposal modules.

## Target Theorem Surfaces

Plain public family target:

```lean
RMQ.RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
```

This is the reusable headline statement: for every `bits : List Bool`, counted
payload length is `bits.length + overhead bits.length`, `overhead` is
`SuccinctSpace.LittleOLinear`, and `access`, `rank`, and `select` queries are
exact with modeled cost bounded by `queryCost`.

Landed Jacobson rank targets:

```lean
RMQ.SuccinctRankProposal.jacobsonRankData_profile
RMQ.SuccinctRankProposal.jacobsonRankFamily_constant_query_profile
```

This builds concrete two-level rank data using Jacobson-style parameters
chosen from `bits.length`, proves the stored payload words flatten back to
`bits`, proves machine-word bounds, and proves exact rank via the canonical
stored-word path.  The family theorem packages concrete super/miniblock payload
length bounds, additive machine-word tails for the sentinel tables, and the
resulting `LittleOLinear` overhead.

Landed Clark select local/obstruction targets:

```lean
RMQ.SuccinctSelectProposal.clarkSelectChunkBaseSample_exact_of_one_word
RMQ.SuccinctSelectProposal.clarkSelectChunkBaseSample_cross_word_obstruction
RMQ.SuccinctSelectProposal.clarkSelectTwoWordDescriptorIndexTable_profile
RMQ.SuccinctSelectProposal.clarkSelectTwoWordIdentityDescriptorRoute_profile
RMQ.SuccinctSelectProposal.clarkSelectTwoWordChunk_table_backed_sample_exact
RMQ.SuccinctSelectProposal.clarkSelectTwoWordDescriptorIndexIdentityOverhead_not_littleO
RMQ.SuccinctSelectProposal.ChargedSelectPositionSource
  .descriptorIndexCosted_profile
RMQ.SuccinctSelectProposal.ChargedSelectPositionSource
  .descriptorIndexCosted_table_backed_sample_exact
RMQ.SuccinctSelectProposal.chargedSelectPositionSource_allows_empty_select_oracle
RMQ.SuccinctSelectProposal.RelativeSplitSparseExceptionFalseSelectCloseData
  .toChargedSelectPositionSource_descriptorIndexCosted_profile
RMQ.SuccinctSelectProposal.RelativeSplitSparseExceptionFalseSelectCloseData
  .relativeSplitDescriptorIndexCosted_table_backed_sample_exact
RMQ.SuccinctSelectProposal.RelativeSplitSparseExceptionFalseSelectCloseData
  .relativeSplitDescriptorIndexCosted_profile
RMQ.SuccinctSelectProposal.builtTwoLevelFalseSelect_current_finite_block_tables_not_littleO
```

These isolate the first Clark occurrence-count chunk boundary: one sampled
locator is exact when the queried occurrence stays in the same payload word as
the chunk base, it is formally insufficient for a cross-word chunk, and a
charged identity-indexed descriptor route can drive the two-word descriptor
sample exactly.  The identity descriptor route and current finite block-table
route are both formally blocked as compact witnesses, so the next Clark step is
a real sparse/dense descriptor-index producer with `o(n)` payload.  The
relative-split BP-specialized theorem is the first charged compact descriptor
producer: it maps the existing compact false-select/close read to a two-word
descriptor index and proves the resulting `ClarkSelectTwoWordChunkCovers`
fact, but it is still BP/false-select specialized rather than a generic Clark
bitvector component.  The generic `ChargedSelectPositionSource` lift is now
explicitly contract-only: `chargedSelectPositionSource_allows_empty_select_oracle`
formalizes that the source abstraction can otherwise hide a zero-payload
semantic-select oracle.

Proposed Clark select family target names:

```lean
RMQ.SuccinctSelectProposal.clarkSelectData_profile
RMQ.SuccinctSelectProposal.clarkSelectFamily_constant_query_profile
```

These names do not exist yet. Intended signature shape: build a
`SuccinctSpace.PayloadLiveStoredWordSelectData bits
  (selectOverhead bits.length)` from occurrence-count chunks, sparse/dense
locators, and final Four Russians word-select tables, prove the locator payload
is `o(n)`, prove word-size bounded reads, and discharge exact select through
`RAM.selectBoolWord`.

Current abstract two-level adapter:

```lean
RMQ.SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
  .n_plus_o_constant_query_profile
RMQ.SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordRankSelectFamily
  .word_bounded_n_plus_o_constant_query_profile
```

This is the strongest public bridge currently in code: it turns any supplied
two-level rank/select family into `RankSelectSpec.BitVectorRankSelectFamily`,
adds the stored-bit `access` leg, proves payload length `n + overhead n`, and
preserves exact rank/select plus the modeled query-cost bound. The
word-bounded version also records that both rank and select payload word stores
erase to `bits` and fit `machineWordBits bits.length`.

Landed concrete combined target:

```lean
RMQ.GenericSelect.jacobsonClarkRankSelectDirectory_profile
RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory_profile
RMQ.GenericSelect.sparseExceptionSelectSource_rankSelectSpec_adapter_profile
RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
```

The adapter instantiates `RankSelectSpec.BitVectorRankSelectFamily` by combining
`SuccinctRankProposal.jacobsonRankData` with two
`GenericSelect.sparseExceptionSelectSource` values, one for `false` and one for
`true`.  Because `RankSelectSpec` publishes exact auxiliary-payload lengths
while the sparse-exception source proves an upper bound, the adapter pads the
unused auxiliary suffix to the clean overhead expression.  The query methods
still call the concrete Jacobson rank data and the concrete sparse/dense Clark
sources, and the public theorem proves stored-bit access, exact rank, exact
select, `n + o(n)` counted payload bits, and one fixed modeled query bound.

## Import Stability

Do not move `SuccinctSpace`, `SuccinctRankProposal`, `SuccinctSelectProposal`,
or `SuccinctFinal` yet.  The stable direction is:

```text
Succinct -> SuccinctSpace -> RankSelectSpec
Succinct -> SuccinctSpace -> SuccinctRankProposal -> SuccinctSelectProposal
  -> GenericSelectBuilder -> SuccinctFinal
```

RMQ-facing modules can continue to consume `SuccinctSpace` and the proposal
modules.  New standalone rank/select claims should be stated in
`RankSelectSpec` or be adapters into that namespace.  Construction modules may
depend on `RankSelectSpec` only at adapter boundaries; `RankSelectSpec` itself
must stay upstream of the proposal/generic-select implementations, so a later
split into a verified data-structures repo can lift one clean spoke instead of
untangling the BP/RMQ capstone.

## Non-oracular Clark select source (2026-06-24)

The `ChargedSelectPositionSource` oracle escape
(`chargedSelectPositionSource_allows_empty_select_oracle`) is now closed on the
constructive path by a builder that backs the source with the genuine two-level
`selectCosted` query rather than `Costed.pure (Succinct.select ...)`:

```lean
RMQ.SuccinctSelectProposal.ChargedSelectPositionSource.ofTwoLevelSelectData
RMQ.SuccinctSelectProposal.ChargedSelectPositionSource.ofTwoLevelSelectData_profile
RMQ.SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectFamily
  .toChargedSelectPositionSource
RMQ.SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectFamily
  .toChargedSelectPositionSource_profile
```

`ofTwoLevelSelectData` sets `selectPositionCosted := data.selectCosted target`
(charged super-sample read + block-delta read + indexed payload-word read +
`RAM.selectBoolWord`), `payload := data.auxPayload` (the real super/block sample
tables), and `readWords := data.bitWords.store.words.toList` (the real stored
payload words).  `ofTwoLevelSelectData_profile` records that the source's
`selectPositionCosted` is *definitionally* the two-level query and its payload is
the real sample-table payload, plus exact select, constant cost, and
machine-word bounded reads.

`toChargedSelectPositionSource` lifts this to the family level.  Because a
`TwoLevelPayloadLiveStoredWordSelectFamily` carries genuine
`super_littleO`/`block_littleO`, the source overhead `twoLevelSelectOverhead
super block` is genuinely `LittleOLinear` -- not the constant-function escape
available at a single `domainSize`.  So this is a real non-oracular `o(n)`-payload
two-level Clark select source, **reduced to** supplying one input: a two-level
select family with `o(n)` super and block budgets.

### The remaining wall: a compact (dense/sparse) block table

The reduction's single missing input is a concrete
`TwoLevelPayloadLiveStoredWordSelectFamily` with `block_littleO`.  The only
concrete two-level select data in code (`canonicalTwoLevelSelectData`) uses
`blockIndex := fun _ occurrence => occurrence` and stores one block-delta slot
per occurrence, which is provably **not** `o(n)`:

```lean
RMQ.SuccinctSelectProposal.canonicalSelectBlockTablesFinite_identity_payload_not_littleO
```

witnessed by `List.replicate n false` (block payload `>= n + 1`).  This is not a
missing optimization but a structural limit of the current data type: the
`select_some_exact` contract decodes the answer from a *single* payload-word read
(`addSelectSample super delta`'s `wordIndex`, then `boolSelectInWord`).  For that
one read to land on the queried occurrence's word in the **sparse** regime, the
block samples must be dense enough to reach every occurrence's word -- i.e.
~one entry per occurrence, hence linear.  A genuinely `o(n)` exact select needs a
richer structure: the dense/sparse occurrence-chunk dichotomy (Clark/Munro),
i.e. the generic analog of the BP capstone's
`RelativeSplitSparseExceptionFalseSelectCloseData` sparse-exception split.

That generic refactor now lives in `RMQ.Core.GenericSelectParams`,
`RMQ.Core.GenericSelectPrimitives`, and `RMQ.Core.GenericSelectBuilder`.  The
current landed layer is additive and target-threaded over `(bits : List Bool)`
and `(target : Bool)`: Clark parameter/overhead leaves, dense two-word exactness
from charged payload reads, span-counting lemmas, dense-local entry tables,
generic flag-rank data, sparse-exception directories, and relative-offset
tables.  The strongest new compact space/exactness leaves are:

```lean
RMQ.GenericSelect.denseTwoWordSelectCosted_exact_of_payload_routing_facts
RMQ.GenericSelect.longSuperRelativeTable_payload_le_overhead
RMQ.GenericSelect.sparseExceptionRelativeTable_payload_le_overhead
RMQ.GenericSelect.SparseExceptionDirectory.profile
RMQ.GenericSelect.sparseExceptionDirectory_readCosted_lookup_exact
RMQ.GenericSelect.SparseExceptionSelectData.profile
RMQ.GenericSelect.sparseExceptionSelectData_profile
RMQ.GenericSelect.sparseExceptionSelectSource_profile
```

so the generic sparse-exception select source is now concrete: its long,
local-missing, sparse-compact, and dense branches are filled from built tables,
its auxiliary payload is charged to explicit `o(n)` budgets, and its query cost
is modeled constant.  The concrete source is also consumed by the public
plain-bitvector family surface:

```lean
RMQ.GenericSelect.jacobsonClarkRankSelectDirectory_profile
RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory_profile
RMQ.GenericSelect.sparseExceptionSelectSource_rankSelectSpec_adapter_profile
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
```

If the project still wants the older two-level-family route, the remaining
target is a *new* concrete compact two-level select family,
e.g.

```lean
RMQ.SuccinctSelectProposal.compactTwoLevelSelectFamily        -- does not exist yet
RMQ.SuccinctSelectProposal.compactTwoLevelSelectFamily_block_littleO
```

whose block table samples occurrence-chunks with a dense/sparse split (explicit
positions for sparse long chunks, relative deltas for dense short chunks) so the
block payload is `o(n)` while a constant number of charged word reads still
decode the exact occurrence.  Feeding such a family into
`toChargedSelectPositionSource` (and, for the public spec, into the
`RankSelectSpec` select leg) closes the generic `o(n)` Clark select goal.
