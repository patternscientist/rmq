# RMQ Codex Guidance

## Repository Expectations

- Treat this repository as a Mathlib-free Lean 4 project pinned by
  `lean-toolchain`; preserve the Lean/Std plus `omega` footprint unless the
  user explicitly decides otherwise.
- Use the existing half-open RMQ contract, leftmost tie policy, and value-level
  `List Int` semantics as the reference layer. Add representation refinements
  as adapters/refinements instead of rewriting the reference theory.
- Keep proof changes scoped. Prefer strengthening existing modules and theorem
  interfaces over creating parallel APIs.
- When changing public theorem surfaces or headline claims, update
  `docs/FAMILY_SUMMARY.md` and, when relevant, `README.md`.
- Preserve the distinction between payload bits, proof-only fields, model-level
  cost ticks, and executable Lean runtime behavior.

## Verification

- After proof or implementation edits, run `lake build`.
- Run this hygiene scan before finalizing:

  ```powershell
  rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
  ```

- For changes touching old smoke examples or proof trust-base claims, also run:

  ```powershell
  rg -n "native_decide|Lean\.ofReduceBool" RMQ
  ```

- Use `git diff --check` before finalizing file edits.

## Current Research Direction

- Highest-value parity gap: a real succinct upper-bound story, eventually
  approaching `2n + o(n)` payload bits with constant-time query under an
  explicit RAM/indexed-access model.
- Highest-value novelty: pair the existing `2n - O(log n)` lower-bound
  framework with a payload-accounted upper-bound construction.
- Near-term proof strategy: add explicit table/access/space model layers first,
  then refine concrete storage such as sparse tables, microtables, and
  rank/select directories behind those interfaces.

## Subagent Policy

- Use subagents only when the user explicitly asks for parallel agents,
  delegation, or subagent work.
- Prefer read-only subagents for independent proof audits, theorem inventory
  checks, literature/source comparisons, and risk reviews.
- Use worker subagents only for disjoint write scopes, and tell them not to
  revert or overwrite changes made by the main thread or other agents.
