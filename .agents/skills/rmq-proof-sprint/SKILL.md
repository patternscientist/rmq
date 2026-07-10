---
name: rmq-proof-sprint
description: Use for Lean RMQ proof and implementation work that must close a theorem-shaped target while preserving payload, cost-model, trust, and public-surface fidelity.
---

# RMQ Proof Sprint

Use this skill for Lean proof, construction, cost/space, executable-validation,
and theorem-surface work in this repository.

## 1. Establish The Contract

Before editing:

1. Read `AGENTS.md`.
2. Read the assigned node in `docs/internal/RMQ_FINAL_ROADMAP.md`.
3. Read the target modules and their direct public consumers.
4. Read only relevant entries in `docs/internal/DESIGN_DECISIONS.md`.
5. Read `references/KNOWN_FAILURE_MODES.md` only when the target touches one of
   those historical traps.
6. Confirm the assigned base, branch, worktree, write scope, target theorem, and
   checks.

Restate the named target, downstream consumer, hard obligation, forbidden
shortcuts, and exact stop conditions. Do not edit the coordinator checkout or
revert unrelated work.

## 2. Check Parallelism

Identify the join theorem and independent leaves before editing. Use parallel
workers only when leaves have disjoint ownership and a concrete consumer.
Keep one owner for shared records, canonical definitions, and public theorem
signatures.

Read-only theorem inventory, dependency analysis, counterexample search, and
validation can run beside a proof worker. Causally ordered interface and
implementation changes should not.

## 3. Preserve Proof Fidelity

Keep these categories explicit:

- counted payload bits;
- proof-only invariants;
- charged model operations and trace events;
- machine state and supplied stores;
- Lean runtime and measured compiled performance.

Requirements:

- derive cost from charged primitives or checked trace length;
- back every successful payload read by the counted store;
- prove address, operand, and word-width bounds;
- compute answers and routing from payload/machine operations, not proof fields
  or semantic oracles;
- preserve the half-open interval contract, leftmost tie policy, and `List Int`
  reference semantics;
- preserve the Mathlib-free trust boundary.

A helper, wrapper, record field, or conditional exactness theorem is complete
only when the assigned downstream target consumes it.

## 4. Work To The Named Target

Use the smallest local theorem that unblocks the target, then consume it in the
same sprint when ownership permits. Prefer strengthening an existing interface
over creating a parallel API. Preserve stable public names with aliases when a
better internal name is introduced.

Do not replace a failed target with a weaker deliverable. A revised endpoint is
valid only after a precise theorem, counterexample, or architecture conflict
shows the original target is mis-specified.

If repeated variants fail for one structural reason, produce the obstruction
dossier specified in `references/KNOWN_FAILURE_MODES.md`. There is no numeric
attempt quota.

## 5. Log Real Decisions

Update `docs/internal/DESIGN_DECISIONS.md` when the branch chooses or changes a
proof model, abstraction, representation, theorem surface, module boundary,
naming policy, cost model, or artifact architecture.

Update `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` only when the branch changes
ADD process. Do not add a ledger entry for routine proof details.

Entries must record context, alternatives, rationale, consequences, evidence,
and follow-up clearly enough to support future paper exposition.

## 6. Verify

Choose the narrowest relevant build first, then the public gates required by
the prompt. Typical commands are:

```powershell
lake build <touched target>
lake build
lake build RMQPaper
lake env lean scripts/headline_axiom_check.lean
rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ RMQExamples lakefile.toml
rg -n "native_decide|Lean\.ofReduceBool" RMQ RMQExamples
git diff --check
powershell -ExecutionPolicy Bypass -File scripts\design_decision_check.ps1
powershell -ExecutionPolicy Bypass -File scripts\claim_drift_scan.ps1
```

Run the native-decision scan when computation/trust examples changed and the
claim-drift scan when public prose changed. Update curated axiom checks when a
new public checkpoint theorem lands. When public theorem inventory, dependency
status, or scope changes, update `docs/FAMILY_SUMMARY.md` and, when relevant,
`README.md`.

## 7. Finish The Branch

Stage only intended files. Commit unless the prompt explicitly says read-only
or no-commit. Report:

- worker handle, requested title, branch, worktree, base, and commit;
- changed files and exact theorem/definition names;
- conceptual meaning, plain-English meaning, and live assumptions;
- the downstream consumer now closed;
- skeptical-reviewer questions;
- design decisions logged, or why none were needed;
- exact verification outcomes;
- remaining blockers and the next crisp target.

A worker may stop only when the target closes, a formal obstruction forces a
coordinator decision, required external state blocks progress, or the user
redirects. A green build alone is not target closure.
