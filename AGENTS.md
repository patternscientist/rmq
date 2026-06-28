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

- For substantial proof/development work, default to a quick parallelization
  check before editing: identify the join theorem or concrete target, the
  independent leaves that feed it, and the work the lead thread will do while
  agents run.
- Use subagents when they materially shorten the path to the current target.
  Avoid ceremonial parallelism: if there is no independent leaf with a clear
  consumer, proceed single-threaded and say why.
- Prefer read-only subagents for independent proof audits, theorem inventory
  checks, literature/source comparisons, and risk reviews.
- Use worker subagents for disjoint write scopes with pinned theorem
  signatures or construction contracts. Tell them they are not alone in the
  codebase, must not revert or overwrite other changes, and should continue
  through their loop until the assigned target closes or a real stop condition
  is met.
- Every worker completion report must include a short proof-digestion section:
  what changed conceptually, what the work just done now means in plain
  English, what assumptions are live, and what a skeptical grad student would
  ask next.
- The lead thread remains responsible for periodic check-ins, steering agents
  away from premature loop breaks or side quests, integrating accepted work, and
  running the final gate. For public-facing milestones, it should also fold
  the worker's digestion note into `docs/DIGESTION_LOG.md` or a focused digest.
