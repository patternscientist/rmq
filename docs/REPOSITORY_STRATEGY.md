# Repository Strategy

This repository is the RMQ proof-of-concept spoke for a broader verified
advanced-data-structures program. The long-term goal is a hub-and-spoke library:
shared proof infrastructure in a reusable hub, with independently meaningful
data-structure spokes such as RMQ, rank/select, union-find, heaps, balanced
trees, and hashing structures.

## Recommendation

Do not rename this repository yet.

Keep `patternscientist/rmq` as the stable, citable RMQ artifact while the new
rank/select, balanced-parentheses, and union-find spokes stabilize. The repo
already has public theorem names, RMQ-specific docs, a large branch history,
and a clean public story. Renaming it now would create churn without making
reuse materially easier.

Instead, use this staged plan:

1. Keep the current repo as the RMQ spoke and in-tree extraction testbed.
2. Continue hardening `RMQ.Core.ModelHub` / `RMQHub` as the reusable boundary.
3. Use `VerifiedDS` as a thin neutral facade over the active public roots,
   without moving namespaces or changing citable theorem names.
4. Use standalone rank/select as the first extraction spoke. This now has an
   in-tree import root, `RMQRankSelect`, and a public plain-bitvector
   `n + o(n)` payload profile with constant modeled `access`, `rank`, and
   `select`. The construction can initially live beside the RMQ succinct
   modules until the API stabilizes.
5. Use `RMQUnionFind` as the first non-succinct spoke. It now has a
   parent-pointer forest refinement, union-by-rank/root-mass/rank-power
   checkpoints, full-compression find refinement, log-rank and rank-bucket
   amortized checkpoints, and first Tarjan-level potential scaffolding, but
   not Tarjan's inverse-Ackermann theorem.
6. Keep the current `VerifiedDS` facade thin until at least two spokes consume
   the same hub APIs in a way that clearly justifies a package boundary.
7. Create a new umbrella repo or promote the hub into a first-class package
   only when that boundary is demanded by concrete reuse rather than naming
   ambition.

This avoids a premature namespace migration while still making the current
repository legible as an emerging verified data-structures library.

## Target Shape

A future umbrella or split package should look conceptually like:

```text
VerifiedDS/
  Hub/
    Cost.lean
    RAM.lean
    Refine.lean
    TableModel.lean
    LowerBound.lean
    PayloadLowerBound.lean
  Succinct/
    RankSelect.lean
    BalancedParens.lean
    PackedWords.lean
  RMQ/
    Core/
    Impl/
  UnionFind/
    Core/
    Impl/
    Amortized/
  Amortized/
    Potential.lean
    Accounting.lean
```

The exact namespace should be chosen when the spoke APIs settle. Until then,
the in-tree `VerifiedDS` facade and `RMQHub` target are the compatibility tests.

## Why Not Rename Now?

Renaming the current repo to a broad data-structures repo would preserve Git
history and make one monorepo, but it would also force a repository identity
change before the second spoke proves which hub APIs are actually stable. The
current module names are RMQ-shaped, the docs are RMQ-shaped, and the theorem
inventory is a useful standalone artifact.

A new umbrella repo is cleaner once there are multiple stable spokes, but
starting it too early risks creating empty architecture. The better trigger is
concrete reuse: when a second data-structure formalization imports or needs at
least two hub modules from `RMQ.Core.ModelHub`, promote those modules.

## Next Spoke Criteria

The next data structure should force a new reusable hub capability rather than
only adding another isolated proof. Good candidates:

- standalone succinct rank/select and balanced-parentheses navigation, to
  extract the bit-level machinery already built for RMQ;
- union-find, to add amortized analysis and mutable/refinement invariants;
- splay trees or Fibonacci heaps, to stress-test potential functions and
  structural invariants;
- cuckoo hashing or filters later, once the project is ready for probability
  and hash-family assumptions.

The strongest immediate path is: push `RMQRankSelect` toward the concrete
compressed/FID constructor and balanced-parentheses navigation, then deepen
`RMQUnionFind` from the current Tarjan-level scaffolding toward the true
inverse-Ackermann amortized theorem. Rank/select and union-find should not be
treated as RMQ theorem add-ons: they now have their own spec surfaces, theorem
inventories, public headlines, and import/check boundaries.
