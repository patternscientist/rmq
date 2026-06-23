# Repository Strategy

This repository is the RMQ proof-of-concept spoke for a broader verified
advanced-data-structures program. The long-term goal is a hub-and-spoke library:
shared proof infrastructure in a reusable hub, with independently meaningful
data-structure spokes such as RMQ, rank/select, union-find, heaps, balanced
trees, and hashing structures.

## Recommendation

Do not rename this repository yet.

Keep `patternscientist/rmq` as the stable, citable RMQ artifact while the next
spoke starts. The repo already has public theorem names, RMQ-specific docs, a
large branch history, and a clean demo story. Renaming it now would create churn
without making reuse materially easier.

Instead, use this staged plan:

1. Keep the current repo as the RMQ spoke and in-tree extraction test.
2. Continue hardening `RMQ.Core.ModelHub` / `RMQHub` as the reusable boundary.
3. When the next spoke begins, create a new umbrella repo only if it needs to
   share code immediately. Otherwise, start the next spoke in its own repo and
   copy only the stable hub modules it consumes.
4. Once two spokes consume the same hub modules, split or promote the hub into
   a first-class package and let spokes depend on it.

This avoids a premature namespace migration while still keeping the path to a
larger library open.

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

The exact namespace should be chosen when the second spoke lands. Until then,
the in-tree `RMQHub` target is the compatibility test.

## Why Not Rename Now?

Renaming the current repo to a broad data-structures repo would preserve Git
history and make one monorepo, but it would also force a repository identity
change before the second spoke proves which hub APIs are actually stable. The
current module names are RMQ-shaped, the docs are RMQ-shaped, and the theorem
inventory is a useful standalone artifact.

A new umbrella repo is cleaner once there are multiple spokes, but starting it
too early risks creating empty architecture. The better trigger is concrete:
when a second data-structure formalization imports or needs at least two hub
modules from `RMQ.Core.ModelHub`, promote those modules.

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

The strongest immediate path is: extract the succinct bitvector/BP layer, then
start union-find as the first non-succinct spoke.
