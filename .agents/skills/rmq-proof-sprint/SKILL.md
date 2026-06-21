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
raise loop-end criteria, treat it as a target-closing proof sprint, not a
single milestone and not a single "good progress" checkpoint. The loop target
is the ambitious owned goal named in the prompt or roadmap. Individual
iterations may land substantial intermediate lemmas or component layers, but
those are reasons to reassess and keep going, not reasons to stop.

Loop behavior:

1. Pick the ambitious owned target from local context, such as the concrete
   component profile or capstone theorem the worker is meant to close.
2. Write a short goal reflection:
   - Overall goal: the capstone theorem or concrete component profile.
   - Current gap: what still prevents that theorem from typechecking.
   - Hard part: the construction or proof obligation easiest to postpone.
   - This iteration: the most ambitious concrete step toward that gap.
   - Not doing: technically useful side work to avoid this round.
3. Implement and verify it.
4. Reassess the same target immediately after verification.
5. Continue into the next iteration when there is no real design decision, user
   input need, merge conflict, tool/approval blocker, or proven
   target-misspecification.

If the reflection shows that "This iteration" does not attack the hard live
gap, revise the target before editing. Do not fill an unattended loop with
substantial but adjacent outputs that leave the named hard construction exactly
where it was.

Strict break criteria for unattended loops:

- Stop normally only when the owned target is closed: the named theorem,
  concrete component profile, or capstone construction typechecks and the
  relevant gate passes.
- Stop for design rethink only when a formal theorem shows the owned target
  itself is impossible or mis-specified. Failed construction attempts are loop
  scratchpad evidence, not a stop condition, unless the worker has recorded an
  extreme exhaustion dossier of at least fifty distinct serious attempts at the
  named positive construction and a common design-level obstruction.
- Stop for external blockers only when tooling, approvals, branch conflicts, or
  unavailable dependencies prevent further local progress.

"Good progress" is not a strict break criterion. A verified helper layer,
partial profile, local kernel, or first successful construction step is an
iteration result. After reporting it in the scratch notes, continue toward the
owned target unless one of the strict break criteria above applies.

Closing the latest audit caveat is also not a loop endpoint unless the prompt's
owned target was exactly "patch these audit caveats." If the loop target is a
C1/C2/C3 component or the final succinct theorem, a caveat repair on a helper
layer is one iteration result; immediately attempt to consume the repaired
layer in the owned concrete profile or capstone theorem.

For this policy, failed construction attempts do not justify a normal loop
break. They should inform the next repaired statement or construction. Only a
formal impossibility theorem for the target statement itself, or an explicitly
documented fifty-attempt exhaustion dossier, can replace a positive
construction/profile as a stop reason.

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

For C1 descriptor-select work, a component/profile surface whose exactness is
still supplied by proof fields is not target closure. Fields such as
`descriptor_some_exact`, `descriptor_none_exact`,
`descriptor_word_choice_exact`, or a free `descriptorIndex` state the remaining
obligations; the same loop should continue to instantiate them from concrete
payload tables. Any routing or index function used by a constant-time query must
be simple bounded arithmetic or derived through charged payload reads. It cannot
hide an uncharged search, predecessor, or oracle.

A concrete packed descriptor profile is also not C1 closure unless it proves the
descriptor auxiliary payload is in the intended `LittleOLinear` budget under the
machine-word side conditions. An exact global `selectCosted` theorem plus a
payload-length formula that still stores one full local-delta slot per
occurrence is a strong iteration result, but the same loop should continue to
the compact dense/sparse descriptor builder or a formal obstruction theorem.

For C2 BP-close work, a position-bearing range witness or macro candidate is
not target closure if exactness is still conditional on a supplied prefix
position such as `answerClose + 1`. The loop should continue until that witness
is consumed by charged endpoint-fringe repair plus the BP semantic theorem that
identifies the leftmost minimum-excess prefix/close with the representative RMQ
answer close.

Charged endpoint-fringe repair is also not target closure by itself. If the
strongest exactness theorem is still an `_exact_of_merged_candidate` theorem or
has a hypothesis such as `hmerge` asserting that the merged payload candidates
already equal `(bpExcessAt shape (answerClose + 1), answerClose + 1)`, the loop
must continue to prove that merge fact from the concrete built entries and the
BP/RMQ semantics.

For C1/C2 specifically, do not stop after the previous known traps:

- a two-word descriptor/local-run theorem without a global descriptor-backed
  `selectCosted_exact`;
- a descriptor-select profile surface whose exactness still rests on proof
  fields and has no compact payload builder instantiating those fields;
- a packed descriptor-select profile whose exactness is global but whose
  descriptor payload is only given by a full per-occurrence local-delta length,
  with no `LittleOLinear` compact-budget theorem under the machine-word model;
- an uncharged descriptor/routing index that could hide search, predecessor, or
  oracle work;
- a BP range-min/max summary table without an answer-close theorem consuming it;
- a BP range-witness or macro-candidate profile, or an `_exact_of_prefix_pos`
  theorem, without the charged endpoint-fringe repair and BP semantic theorem
  that turn it into a global answer-close theorem;
- a charged endpoint-fringe macro/profile whose exactness still assumes a
  supplied merged-candidate fact such as `hmerge`;
- a repaired machine-word bound or invariant for that summary table without the
  next answer-close theorem attempt that consumes the repaired table;
- a BP close sampled profile whose space theorem still assumes a budget for
  dense `interiorBlockPairRanges blockCount` entries or an equivalent all-pairs
  interior payload;
- a newly charged fixed-width table without an explicit machine-word bound; or
- a theorem name that suggests stronger semantics than the statement proves.

Valid stop conditions:

- the requested roadmap slice is genuinely complete;
- the next step requires a non-obvious design choice from the user;
- a concrete construction attempt proves the target statement is
  mis-specified or impossible as stated, with a minimal theorem documenting the
  obstruction;
- an extreme exhaustion dossier records at least fifty distinct serious
  attempts at the named positive construction, all failing for the same
  design-level reason, and explains why the next move is a fundamental design
  choice rather than more local proof work;
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
- one substantial intermediate theorem or component layer landed, but the
  owned target still has an obvious next construction/proof step.
- the worker hit hard proof errors, no matter how annoying, without continuing
  through the natural repaired statements or nearby construction variants.

Before stopping, run this loop-stop audit:

1. Did this round prove the named target theorem, concrete component profile,
   or final construction promised at loop start?
2. Is the next theorem or construction from the diff obvious and still inside
   the worker's owned file surface?
3. Did this round leave a canonical identity witness, abstract family
   parameter, or proof-only placeholder where the target asked for a compact or
   payload-live construction?
4. If stopping short of the target, is there one formal impossibility theorem
   for the target statement, or an extreme fifty-attempt exhaustion dossier
   showing a common design-level reason local proof work cannot proceed?

If the answer to 1 is "no" and 2 or 3 is "yes", continue the loop. If the
answer to 1 is "no" and 4 is "no", continue the loop. For the succinct RMQ
finish line specifically, a round that only creates hooks for select locators,
BP block code classifiers, macro directories, range-min/max summaries, local
descriptor kernels, or close/LCA navigation does not stop until it also supplies
the concrete witness/profile. A new blocker only justifies stopping if it comes
from serious attempts at the named positive construction and shows the target
signature itself must change.

The loop-stop audit is a control-flow guard, not a disclosure checklist. If the
audit says the stop is invalid, the worker must not send a final completion
report. It must immediately begin the next loop iteration in the same turn,
using the "next theorem/construction" named by the audit as the new iteration
target. A final response that says "this should not be considered a valid stop"
is itself a protocol failure unless it is followed by more implementation and
verification before the final response.

For unattended loops, keep interim updates concise and periodic, but reserve the
final response for a valid stop condition. If stopping for target
misspecification, report the concrete construction attempted, the minimal
obstruction theorem, and the exact signature/design decision now required.

## Edit And Verify

1. Announce intended edits before changing files.
2. Use `apply_patch` for manual edits.
3. Update `docs/FAMILY_SUMMARY.md` when public theorem inventories, dependency
   status, or scope notes change.
4. If the branch adds or documents a new public exactness, cost, space, or
   obstruction theorem as part of the milestone, add a corresponding
   `#print axioms` line to `scripts/axiom_check.lean`, unless the report
   explicitly explains why the theorem is only a local helper and not a curated
   headline/checkpoint surface.
5. Run:

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
