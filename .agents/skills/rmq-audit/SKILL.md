---
name: rmq-audit
description: Use to engineer external-auditor prompts and audit packets for RMQ, filling docs/internal/templates/AUDIT_PROMPT.md from current repository context, theorem surfaces, claim docs, and explicit evidence tiers. Do not use for the coordinator's normal audit-integrate-next-prompt cycle.
---

# RMQ External Audit Prompt

Use this skill when the coordinator needs a high-quality prompt or evidence
packet for an external auditor. The coordinator remains responsible for
integrating worker branches and turning audit findings into theorem, docs,
artifact, or workflow targets.

## Ground Rules

Read `docs/internal/AUDIT_PROTOCOL.md` before serious audits. If claim wording is
in scope, also read `docs/internal/CLAIM_DRIFT_POLICY.md`.

An external audit does not add trust by itself. It should be engineered so the
auditor can cite checked theorem statements, source diffs, command outputs,
artifact docs, or process evidence and then recommend the next action.
Keep auditor/model/mode recommendations as coordinator-facing launch metadata
for the user, not as text inside the external-auditor prompt. The prompt itself
should identify the auditor handle, branch/commit/base, scope, evidence tiers,
checks, and report shape.

If the user asks for a read-only local audit rather than an external-auditor
prompt, use `rmq-coordinator` for completed-worker integration audits or a
plain review workflow for one-off local review.

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

## Prompt Modes

- Branch audit prompt: compare branch, base, owned files, diff, and gates.
- Theorem-surface audit prompt: trace public aliases to concrete theorem
  statements.
- Claim-drift audit prompt: compare public prose with checked theorem truth and the
  claim-drift policy.
- Worker-stop audit prompt: decide whether a worker stopped at a real obstruction
  or at an honest partial checkpoint with obvious local work remaining.
- Literature/parity audit prompt: compare against external precedent and separate
  novelty, reviewer-pattern, and theorem gaps.

## Useful Prompt Inputs

```powershell
git status --short --branch
git log --oneline --decorate -20
git diff --stat BASE..HEAD
git diff --check
scripts/claim_drift_scan.ps1
scripts/design_decision_check.ps1
```

For proof branches, include the target-specific Lake commands requested by the
coordinator prompt. For public RMQ surfaces, `lake build RMQPaper` and
`lake env lean scripts/headline_axiom_check.lean` are common minimum checks.

## Report Shape

Ask the external auditor to lead with findings:

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
