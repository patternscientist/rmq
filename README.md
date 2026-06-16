# RMQ

A standalone Lean 4 formalization project for reusable range-minimum query
correctness results.

This repository started as a small extraction from a VeriBench-oriented RMQ
development. The code here is intentionally library-shaped rather than
benchmark-shaped: the goal is to factor reusable specifications, backend
contracts, and correctness lemmas that can support multiple RMQ algorithms.

## Current Status

The project currently builds without Mathlib, using only Lean/Std plus `omega`.
It proves a common half-open, leftmost-argmin contract for:

- a direct linear scan backend,
- a sparse table backend,
- a hybrid block backend with boundary scans and sparse middle summaries, and
- a self-recursive hybrid backend with aligned boundary scans and recursive
  middle summaries.

The hybrid proof is already factored through a generic three-piece combinator:
an exact nonempty left boundary, an optional middle interval, and an optional
right interval combine into one exact leftmost argmin witness.

## Layout

- `RMQ/Core/Spec.lean`: query validity, `LeftmostArgMin`, index combination,
  and reusable exactness combinators.
- `RMQ/Core/Window.lean`: direct scan/window lemmas.
- `RMQ/Core/Backend.lean`: explicit backend interface with soundness,
  completeness, invalid-query rejection, and generic built-backend equality.
- `RMQ/Core/LCA.lean`: proof-friendly rose-tree Euler node/depth traces, the
  plus/minus-one depth invariant, first-occurrence windows, direct root-path
  LCA semantics, the `TracePathAgreement` bridge statement, a derived
  `TracePathExactOnLabels` semantic exactness theorem, a trace-side
  leftmost-minimum reference candidate, generated path-annotated Euler traces,
  a finite generated-label agreement certificate, structural
  `LabelsUnique -> TracePathAgreement` proof via generated Euler-window
  invariants, and the RMQ-backed tree-level LCA theorem for certified traces.
- `RMQ/Core/Reduction.lean`: contract-level RMQ/LCA reduction interfaces:
  label-unique generated Euler traces turn RMQ backends into LCA backends,
  with trace/path-agreement and finite-check wrappers still available, and
  certified interval-to-LCA encodings turn LCA backends into RMQ backends.
- `RMQ/Core/Cartesian.lean`: proof-friendly Cartesian tree construction over
  list indices, root/range-minimum lemmas, and the `RangeLCASpec ->
  RMQToLCAReduction` bridge for the reverse direction.
- `RMQ/Core/Recursion.lean`: Mathlib-free well-founded recursion over strictly
  shorter summary lists, concrete full-block minimum summaries, and lifting
  lemmas from summary candidates back to original-list candidates, including
  a generic recursive-middle hybrid combinator.
- `RMQ/Core/Schedule.lean`: stable block-boundary scheduling helpers shared by
  hybrid variants.
- `RMQ/Impl/LinearScan.lean`: simplest exact backend.
- `RMQ/Impl/SparseTable.lean`: sparse table cells, materialized table lookup,
  and backend proof.
- `RMQ/Impl/HybridBlock.lean`: block summaries, sparse middle query, public
  hybrid query, and backend proof.
- `RMQ/Impl/RecursiveHybrid.lean`: aligned query schedule and public
  self-recursive hybrid backend built with `recurseOnSummary`.
- `RMQ/Impl/Equivalence.lean`: contract-level equality instantiations for all
  public backend pairs.

## Build

The project is pinned to Lean `leanprover/lean4:v4.22.0`.

```powershell
lake build
```

Useful proof-hygiene check:

```powershell
rg -n "sorry|admit|axiom|unsafe|opaque|implemented_by" RMQ lakefile.toml
```

## Next Direction

The forward LCA side is now structural: a label-unique generated Euler trace
plus any exact RMQ backend over its depths induces an exact LCA backend. The
reverse side has a concrete Cartesian tree and certificate bridge; the remaining
proof target is `Cartesian.BuiltRangeLCASpec`, the theorem that endpoint LCAs in
the built Cartesian tree are exactly leftmost RMQ witnesses.
