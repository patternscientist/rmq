---
name: rmq-proof-sprint
description: Use for Lean RMQ formalization work in this repository, especially proof planning, theorem implementation, cost/space modeling, lower-bound work, Fischer-Heun, succinct RMQ, plus-minus-one RMQ, LCA reductions, or family-summary maintenance.
---

# RMQ Proof Sprint

Use this workflow for nontrivial work in the RMQ Lean repository.

## Orient

1. Read the nearest relevant module plus `docs/FAMILY_SUMMARY.md` sections for
   the structure being changed.
2. Identify whether the task is one of:
   - correctness theorem,
   - cost theorem,
   - space/lower-bound theorem,
   - representation refinement,
   - documentation/inventory maintenance.
3. Preserve existing public contracts where possible: `RMQBackend`,
   `LeftmostArgMin`, `ExactRMQStateEncoding`, and the LCA/RMQ bridge types.

## Proof Style

- Stay Mathlib-free unless the user explicitly changes that policy.
- Prefer existing helper lemmas and local patterns before introducing a new
  abstraction.
- Keep value-level `List` semantics as reference behavior unless the task is
  specifically about representation refinement.
- When adding Array or packed-table layers, prove equivalence to the existing
  reference query rather than replacing the reference theory.
- Keep cost and space claims model-scoped: distinguish unit-cost indexed reads,
  payload bits, proof-only fields, and executable Lean runtime.

## Orchestration

- Do not spawn subagents unless the user explicitly asks for parallel agents,
  delegation, or subagent work.
- Good read-only subagent splits:
  - theorem inventory and trust-base audit,
  - proof-gap scan for a target milestone,
  - literature/parity comparison,
  - cost/space model consistency review.
- Good worker splits require disjoint write ownership, such as one module per
  worker. Tell workers not to revert other changes.

## Unattended Loops

When the user asks for an unattended loop, restart/continue the loop, or says to
raise loop-end criteria, treat it as a multi-iteration proof sprint rather than
a single milestone.

Loop behavior:

1. Pick the next substantial roadmap milestone from local context.
2. Write a short goal reflection:
   - Overall goal: the capstone theorem or concrete component profile.
   - Current gap: what still prevents that theorem from typechecking.
   - Hard part: the construction or proof obligation easiest to postpone.
   - This iteration: the most ambitious concrete step toward that gap.
   - Not doing: technically useful side work to avoid this round.
3. Implement and verify it.
4. Reassess the roadmap immediately after verification.
5. Continue into the next substantial milestone when there is no real design
   decision, user input need, merge conflict, tool/approval blocker, or proven
   target-misspecification.

If the reflection shows that "This iteration" does not attack the hard live
gap, revise the target before editing. Do not fill an unattended loop with
substantial but adjacent outputs that leave the named hard construction exactly
where it was.

Minimum bar before stopping an unattended loop:

- Complete at least two substantial milestones, or
- complete one large milestone and make verified progress on the next adjacent
  milestone, or
- hit a genuine stop condition below.

Do not count tiny substeps as separate milestones. A substantial milestone must
land at least one of:

- a public theorem surface or exactness/cost/space capstone,
- a concrete structure or representation layer consumed by later proofs,
- a retired tracked debt item,
- a reusable lemma cluster that is immediately consumed by a concrete
  construction/profile.

For the current succinct RMQ finish line, "substantial" means shortening the
path to the concrete `2*n + o(n), O(1)` theorem: a descriptor select builder, a
payload-live BP macro/close component, their join, or a retired false shortcut.
Helper lemmas, proposal docs, adapters, and blocker variants count only when
they are immediately consumed by one of those targets or prove the target
signature itself must change.

Valid stop conditions:

- the requested roadmap slice is genuinely complete;
- the next step requires a non-obvious design choice from the user;
- a concrete construction attempt proves the target statement is
  mis-specified or impossible as stated, with a minimal theorem documenting the
  obstruction;
- required tooling, network, approvals, or local branch conflicts block further
  progress;
- the user interrupts or redirects.

Invalid stop reasons:

- one module built cleanly but the next target is obvious;
- only docs or axiom inventory were updated after code landed;
- proof work remains and the only issue is that more work is ahead.
- the branch only added an API hook, parameter, constructor field, or bridge
  theorem while the concrete instance/witness named by the target is still
  missing;
- the docs or final report say that a "concrete builder", "compact instance",
  "payload-live witness", or analogous construction remains to be supplied for
  the same target.
- the round produced technically substantial side work while explicitly
  deferring the hard part named in the goal reflection.

Before stopping, run this loop-stop audit:

1. Did this round prove the named target theorem, concrete component profile,
   or final construction promised at loop start?
2. Is the next theorem or construction from the diff obvious and still inside
   the worker's owned file surface?
3. Did this round leave a canonical identity witness, abstract family
   parameter, or proof-only placeholder where the target asked for a compact or
   payload-live construction?

If the answer to 1 is "no" and 2 or 3 is "yes", continue the loop. For the
succinct RMQ finish line specifically, a round that only creates hooks for
select locators, BP block code classifiers, macro directories, or close/LCA
navigation does not stop until it also supplies the concrete witness/profile.
A new blocker only justifies stopping if it comes from a serious attempt at the
named positive construction and shows the target signature itself must change.

For unattended loops, keep interim updates concise and periodic, but reserve the
final response for a valid stop condition. If stopping for target
misspecification, report the concrete construction attempted, the minimal
obstruction theorem, and the exact signature/design decision now required.

## Edit And Verify

1. Announce intended edits before changing files.
2. Use `apply_patch` for manual edits.
3. Update `docs/FAMILY_SUMMARY.md` when public theorem inventories, dependency
   status, or scope notes change.
4. Run:

   ```powershell
   lake build
   rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml
   git diff --check
   ```

5. If trust-base examples or finite computations changed, also run:

   ```powershell
   rg -n "native_decide|Lean\.ofReduceBool" RMQ
   ```

## Final Report

Summarize:

- the goal reflection: overall goal, current gap, hard part, and how the branch
  reduced the distance to the capstone,
- changed modules and theorem names,
- verification commands and outcomes,
- any remaining model caveats,
- the next crisp theorem target.
