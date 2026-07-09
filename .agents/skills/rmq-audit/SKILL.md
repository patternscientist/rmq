---
name: rmq-audit
description: Use for read-only or adversarial RMQ audits of branches, worker reports, theorem surfaces, public claims, artifact docs, import roots, trust-base wording, and ADD workflow evidence. Use when Codex should falsify or clear a target against checked source, commands, and explicit evidence tiers rather than coordinate or implement proof work.
---

# RMQ Audit

Use this skill for falsification-oriented RMQ review.

## Ground Rules

Read `docs/internal/AUDIT_PROTOCOL.md` before serious audits. If claim wording is
in scope, also read `docs/internal/CLAIM_DRIFT_POLICY.md`.

An audit does not add trust by itself. It cites checked theorem statements,
source diffs, command outputs, artifact docs, or process evidence and then
recommends the next action.

If the user asks for a read-only audit, do not edit files.

## Evidence Tiers

Classify positive claims by the strongest supporting tier:

- kernel theorem;
- model theorem;
- executable validation;
- artifact evidence;
- process evidence.

Do not use process evidence as proof of a mathematical or executable claim.
Keep payload bits, proof-only fields, model-cost ticks, Lean runtime, and
compiled-code behavior separate.

## Audit Modes

- Branch audit: compare branch, base, owned files, diff, and gates.
- Theorem-surface audit: trace public aliases to concrete theorem statements.
- Claim-drift audit: compare public prose with checked theorem truth and the
  claim-drift policy.
- Worker-stop audit: decide whether a worker stopped at a real obstruction or
  at an honest partial checkpoint with obvious local work remaining.
- Literature/parity audit: compare against external precedent and separate
  novelty, reviewer-pattern, and theorem gaps.

## Useful Commands

```powershell
git status --short --branch
git log --oneline --decorate -20
git diff --stat BASE..HEAD
git diff --check
scripts/claim_drift_scan.ps1
scripts/design_decision_check.ps1
```

For proof branches, use the target-specific Lake commands requested by the
coordinator prompt. For public RMQ surfaces, `lake build RMQPaper` and
`lake env lean scripts/headline_axiom_check.lean` are common minimum checks.

## Report Shape

Lead with findings for review-style requests:

1. Scope: branch, commit, base, files, theorem surfaces, and prompt.
2. Verdict: merge-ready, merge-ready with follow-up, blocked, or needs another
   worker pass.
3. Findings: ordered by severity, each with evidence and an actionable target.
4. Stale or rejected objections.
5. Verification commands run, skipped, and why.
6. Best next theorem, docs, artifact, or workflow prompt.

Severity:

- P0: proof/trust invalidity or artifact corruption.
- P1: public overclaim, failing required gate, or misleading theorem surface.
- P2: reviewer-friction, maintainability, import-surface, or documentation risk.
- P3: polish.
