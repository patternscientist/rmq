# Generic Select Refactor Scope

Status: landed for the plain-bitvector rank/select milestone.

This note records the scope of the generic Clark sparse-exception select
refactor. It supersedes the earlier BP-shaped checklist that generalized
`RelativeSplitSparseExceptionFalseSelectCloseData` from
`(shape : CartesianShape, target = false)` to `(bits : List Bool, target :
Bool)`.

## Goal

Extract a generic, non-oracular, `o(n)`-payload, constant-query, exact select
source over `List Bool`, then consume it through the standalone
`RankSelectSpec` public surface.

The target semantics remain:

- access: `bits[i]?`;
- rank: `Succinct.rankPrefix target bits pos`;
- select: `Succinct.select target bits occurrence`.

The model distinction is important:

- stored input bits count in the public `n + overhead n` payload;
- auxiliary directory payload is charged separately;
- proof-only fields do not count as payload;
- query costs are modeled ticks/charged reads, not Lean runtime.

## Landed Modules

The generic select layer lives in:

- `RMQ/Core/GenericSelectParams.lean`
- `RMQ/Core/GenericSelectPrimitives.lean`
- `RMQ/Core/GenericSelectBuilder.lean`

The public bitvector extraction layer lives in:

- `RMQ/Core/RankSelectSpec.lean`

`RMQ.lean` imports `RankSelectSpec` before the proposal/generic builder modules,
and imports the generic select modules before `SuccinctFinal`.

## Landed Generic Select Theorems

The parameter and primitive layers expose target-threaded Clark arithmetic,
dense two-word select exactness, and payload-routed local entry reads. The
builder layer now closes the generic sparse-exception source:

```lean
RMQ.GenericSelect.SparseExceptionDirectory.profile
RMQ.GenericSelect.sparseExceptionDirectory_readCosted_lookup_exact
RMQ.GenericSelect.SparseExceptionSelectData.profile
RMQ.GenericSelect.sparseExceptionSelectData_profile
RMQ.GenericSelect.sparseExceptionSelectSource_profile
```

The source is non-oracular in the intended sense: `selectPositionCosted` is the
built sparse/dense query, `payload` is the built auxiliary payload, and
`readWords` are the charged payload-word reads used by the query.

## Landed Public Rank/Select Theorems

The public Jacobson/Clark plain-bitvector family is now:

```lean
RMQ.GenericSelect.jacobsonClarkRankSelectDirectory_profile
RMQ.GenericSelect.jacobsonClarkBitVectorRankSelectDirectory_profile
RMQ.GenericSelect.sparseExceptionSelectSource_rankSelectSpec_adapter_profile
RMQ.GenericSelect.jacobsonClarkRankSelectOverhead_littleO
RMQ.GenericSelect.jacobsonClarkRankSelectFamily_n_plus_o_constant_query_profile
```

This combines:

- `SuccinctRankProposal.jacobsonRankData` for rank;
- `GenericSelect.sparseExceptionSelectSource bits false` for `select false`;
- `GenericSelect.sparseExceptionSelectSource bits true` for `select true`;
- stored-bit access from `RankSelectSpec`.

The auxiliary payload is padded only to publish the clean overhead expression.
Queries still call the concrete Jacobson rank data and concrete sparse/dense
Clark select sources.

## Import Boundary

Keep the direction:

```text
Succinct -> SuccinctSpace -> RankSelectSpec
Succinct -> SuccinctSpace -> SuccinctRankProposal -> SuccinctSelectProposal
  -> GenericSelectBuilder -> SuccinctFinal
```

`RankSelectSpec` should stay a small public spec module. Construction modules
may adapt into it, but it should not import the proposal/generic builders.

## Remaining Frontier

The plain-bitvector `n + o(n), O(1)` milestone is closed enough to clean the
worktree. The next research frontier is not another adapter into
`RankSelectSpec`; it is one of:

1. compressed/FID-style payload budgets such as
   `log2 (Nat.choose U m) + o(U)` or a scoped predecessor;
2. a word-bounded/read-backed presentation theorem for the public
   Jacobson/Clark family;
3. balanced-parentheses navigation spokes over the same public rank/select
   surface.

## Verification Recipe

After edits touching these surfaces, run:

```powershell
lake build
lake env lean scripts\axiom_check.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ
git diff --check
```
