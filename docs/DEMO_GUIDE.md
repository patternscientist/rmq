# RMQ Demo Guide

## One-Minute Answer

This is a Lean 4 formalization of range-minimum query as a whole algorithmic
family. It starts with a simple semantic contract: for a half-open range
`[left, right)`, return the leftmost index whose value is minimal. From that
contract, the repo verifies linear scan, sparse table, hybrid, recursive
hybrid, Fischer-Heun, RMQ/LCA reductions, Cartesian-shape lower bounds, and a
BP-native succinct RMQ profile.

The punchline is not just that one implementation is correct. The punchline is
that the project connects the usual RMQ story end to end:

- exact query behavior for many implementations under one contract;
- RMQ and LCA reductions in both directions;
- an information-theoretic `2*n - O(log n)` lower bound for exact RMQ shape
  encodings; and
- a payload-accounted `2*n + o(n), O(1)` succinct upper-bound profile under an
  explicit RAM/indexed-access model.

That combination is the demo claim. It is deliberately stronger than a toy
correctness proof and deliberately narrower than a claim about Lean's runtime
performance.

## What To Show

1. The shared spec:
   - `RMQ.Core.Spec.LeftmostArgMin`
   - `RMQ.Core.Backend.RMQBackend`

2. The ordinary algorithm family:
   - `RMQ.Impl.LinearScan`
   - `RMQ.Impl.SparseTable`
   - `RMQ.Impl.HybridBlock`
   - `RMQ.Impl.RecursiveHybrid`
   - `RMQ.Impl.FischerHeun`

3. The reduction story:
   - `RMQ.Core.LCA`
   - `RMQ.Core.Reduction`
   - `RMQ.Core.Cartesian.certifiedReduction`

4. The lower bound:
   - `RMQ.EncodingLowerBound.shapeCount_quadratic_lower`
   - `RMQ.EncodingLowerBound.two_mul_sub_log_slack_le_bits_of_exactRMQShapeEncoding`
   - `RMQ.EncodingLowerBound.exactRMQ_tight_fixed_length_payload_space_bound`

5. The succinct upper bound:
   - `RMQ.SuccinctFinal.builtRelativeSplitSparseExceptionBPNativeSuccinctRMQFamily_total_two_n_plus_o_constant_query_profile`
   - `RMQ.SuccinctFinal.builtRelativeSplitSparseExceptionFalseSelectBPCloseAccessFamily_profile`
   - `RMQ.SuccinctCloseProposal.concreteBPRelativeRmmInteriorDirectory_profile`
     (large-regime interior component)
   - `RMQ.SuccinctCloseProposal.ConcreteCompactBPCloseLCADirectory.lcaCloseCostedWithRankSeed_exact_of_query`

6. The trust-base and hygiene story:
   - `scripts/axiom_check.lean`
   - `scripts/gate.ps1`
   - the hygiene scan for `sorry`, `axiom`, `unsafe`, `noncomputable`, and
     `import Mathlib`

## Headline Statement

A good short version:

> This project verifies RMQ as a connected data-structure family in Lean:
> correctness for standard backends, RMQ/LCA reductions, a formal `2*n -
> O(log n)` information-theoretic lower bound, and a matching payload-accounted
> `2*n + o(n), O(1)` succinct RMQ profile under an explicit RAM model.

A slightly more technical version:

> The final succinct theorem stores a Cartesian shape as its balanced-parentheses
> code of exact length `2*n`, adds only `o(n)` charged auxiliary payload bits,
> and answers RMQ queries by composing payload-live false-close/select access
> with a compact BP close/LCA navigator. Erasure returns the same leftmost RMQ
> answer as the reference semantics.

## What It Does Not Claim

- It does not claim Lean's executable `List` representation has constant-time
  random access.
- It does not claim wall-clock performance for extracted code.
- It does not hide proof-only fields inside the charged payload: the final
  payload theorem separates payload bits from certificates.
- It does not rely on Mathlib, custom axioms, `sorry`, `admit`, `unsafe`, or
  `native_decide` on headline proofs.
- It does not require saying "no other project has this." The defensible claim
  is that this repo combines correctness, reductions, cost modeling, lower
  bounds, and a succinct upper-bound profile in one audited RMQ development.

## Suggested Demo Flow

1. Run `powershell -ExecutionPolicy Bypass -File scripts/demo_check.ps1`.
2. For the full acceptance gate, run
   `powershell -ExecutionPolicy Bypass -File scripts/gate.ps1`.
3. Show the spec in `RMQ/Core/Spec.lean`.
4. Show one ordinary backend theorem, such as Fischer-Heun.
5. Show the lower-bound theorem in `RMQ/Core/EncodingLowerBound.lean`.
6. Show the final upper-bound theorem in `RMQ/Core/SuccinctFinal.lean`.
7. End on the model notes in `docs/FAMILY_SUMMARY.md`: the claims are strong
   because they are scoped.
