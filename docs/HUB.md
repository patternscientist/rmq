# RMQ Hub Layer

`RMQ.Core.ModelHub` is the in-tree reusable import surface for the hub modules
extracted during the RMQ proof of concept. `RMQHub` is the standalone Lake
library target that imports the same surface.

## Import

```lean
import RMQHub
```

or, inside the existing `RMQ` library:

```lean
import RMQ.Core.ModelHub
```

These import only:

- `RMQ.Core.Cost`
- `RMQ.Core.RAM`
- `RMQ.Core.Refine`
- `RMQ.Core.TableModel`
- `RMQ.Core.LowerBound`
- `RMQ.Core.PayloadLowerBound`

These modules do not import RMQ-specific range specs, Cartesian shapes, Euler
tours, or backend implementations.

## Interfaces

- `Costed` is the lightweight value-plus-cost carrier.
- `RAM.Exec` is the hardened shallow primitive-trace substrate. Clients build
  traces through typed primitives such as `readArray?`, `writeArray?`,
  `pushArray`, `branch`, and comparisons.
- `Refine.StoredSeq` and `Refine.StoredMatrix` connect executable `Array`
  representations to List-level reference semantics.
- `TableModel` names unit-cost indexed reads and payload-bit accounting views.
- `LowerBound` provides fixed-length bitstring universes, lossless finite-domain
  encodings, capacity counting, and logarithmic-slack arithmetic.
- `PayloadLowerBound` connects payload-accounted states to fixed-length
  lossless encodings, with separate lemmas for pointwise and uniform charged
  payload-budget lower bounds. `PayloadSpaceBounds` packages the reusable
  two-sided form: a finite-domain count lower bound plus a concrete
  fixed-length payload upper witness.

## Checks

Build only the hub:

```powershell
lake build RMQHub
```

Check the hub trust base:

```powershell
lake env lean scripts/hub_axiom_check.lean
```

## Scope

The hub is still physically inside this repository. This target is the first
standalone extraction test: it validates dependency direction before any file
move, package split, or CSLib-facing reorganization.

For now, keep this repository as the RMQ spoke and use `RMQHub` as the in-tree
hub boundary. Promote the hub into a separate package only after another spoke
actually imports the same interfaces. See `docs/REPOSITORY_STRATEGY.md`.

The first planned spoke to stress this boundary is standalone succinct
rank/select: a plain-bitvector `n + o(n)` payload profile with constant modeled
`access`, `rank`, and `select` queries.
