# Rank/Select Spoke

Snapshot: 2026-06-25. This note records the first extracted succinct
data-structure spoke in the RMQ repository: plain bitvector access/rank/select.

## Import

Use the standalone import root:

```lean
import RMQRankSelect
```

`RMQRankSelect` exposes the public bitvector spec plus the concrete
Jacobson/Clark construction. It does not import RMQ windows, Cartesian trees,
LCA, Fischer-Heun, or the final succinct RMQ capstone modules.

Verification:

```powershell
lake build RMQRankSelect
lake env lean scripts/rank_select_axiom_check.lean
```

## Public Headline

For plain bitvectors, the rank/select analogue of the RMQ `2n + o(n), O(1)`
headline is:

- store the `n` input bits plus `o(n)` auxiliary bits;
- support `access i`, `rank b i`, and `select b k`;
- charge a uniform constant number of modeled word-RAM/indexed-access steps per
  query;
- use exact reference semantics `bits[i]?`,
  `Succinct.rankPrefix b bits i`, and `Succinct.select b bits k`.

The reusable theorem shape is:

```lean
RMQ.RankSelectSpec.BitVectorRankSelectFamily.n_plus_o_constant_query_profile
```

This is not an existence theorem by itself: it packages the theorem once a
family is supplied.

The concrete landed Jacobson/Clark family theorem is exposed publicly as:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
```

It proves `LittleOLinear` auxiliary overhead and, for every
`bits : List Bool`, counted payload length
`bits.length + jacobsonClarkRankSelectOverhead bits.length`, exact stored-bit
access, exact rank, exact select, and one fixed modeled query-cost bound.

## Module Boundary

The reusable public spec is:

- `RMQ/Core/RankSelectSpec.lean`
- `RMQ/Core/RankSelectPublic.lean`

The concrete construction currently lives in:

- `RMQ/Core/SuccinctRankProposal.lean`
- `RMQ/Core/SuccinctSelectProposal.lean`
- `RMQ/Core/GenericSelectParams.lean`
- `RMQ/Core/GenericSelectPrimitives.lean`
- `RMQ/Core/GenericSelectBuilder.lean`

The intended direction is:

```text
Succinct -> SuccinctSpace -> RankSelectSpec
Succinct -> SuccinctSpace -> SuccinctRankProposal -> SuccinctSelectProposal
  -> GenericSelectBuilder -> SuccinctFinal
```

`RankSelectSpec` should stay small and upstream. Construction modules may adapt
into it, but it should not import the proposal/generic builders.
`RankSelectPublic` is the downstream facade that is allowed to import the
concrete Jacobson/Clark construction and expose short names.

## What Landed

The rank side uses:

```lean
RMQ.SuccinctRankProposal.jacobsonRankData_profile
RMQ.SuccinctRankProposal.jacobsonRankFamily_constant_query_profile
```

The select side uses the generic sparse-exception Clark-style source:

```lean
RMQ.GenericSelect.sparseExceptionSelectSource_profile
RMQ.GenericSelect.SparseExceptionSelectData.profile
RMQ.GenericSelect.SparseExceptionDirectory.profile
```

The public adapter combines one Jacobson rank directory with two select
sources, one for `false` and one for `true`:

```lean
RMQ.RankSelect.jacobsonClarkNPlusOConstantQuery
RMQ.GenericSelect.jacobsonClarkRankSelectDirectory_profile
RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory_profile
RMQ.GenericSelect.sparseExceptionSelectSource_rankSelectSpec_adapter_profile
RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
```

The auxiliary payload is padded only to publish a clean exact overhead
expression. Query methods still call the concrete Jacobson rank data and the
concrete sparse/dense Clark select sources.

## Scope Notes

The public theorem is model-scoped. Constant query time means the repository's
modeled RAM/indexed-access cost: stored-bit access, table reads, and word
rank/select primitives are charged as constant-cost operations. It is not a
claim about Lean `List` runtime.

`ChargedSelectPositionSource` remains a contract boundary, not by itself a
non-oracular builder. The theorem
`RMQ.SuccinctSelectProposal.chargedSelectPositionSource_allows_empty_select_oracle`
records the pitfall. The concrete public family avoids that escape by routing
through the built `GenericSelect.sparseExceptionSelectSource` construction.

Some implementation names still reveal their BP/RMQ ancestry, especially
`falseSelect*` helpers and a few bridge lemmas used while extracting the generic
select source. The public facade keeps downstream users on neutral
`RMQ.RankSelect.*` names; the remaining internal names are polish debt, not a
correctness gap.

## Remaining Frontier

The plain-bitvector `n + o(n), O(1)` milestone is landed. The next research
targets are:

1. compressed/FID-style payload budgets such as
   `log2 (Nat.choose U m) + o(U)`, after adding a binomial/entropy counting
   layer;
2. a more explicit word-bounded public theorem for the concrete Jacobson/Clark
   family, exposing the machine-word read bounds already present in component
   profiles;
3. balanced-parentheses navigation as its own spoke over the same public
   rank/select surface;
4. neutral naming/facade polish if this module is later moved into a broader
   verified data-structures repository.
