---
name: rmq-audit
description: Use to engineer independent external-auditor prompts and evidence packets for RMQ. Select fresh-blind, continuation, longitudinal, or whole-frontier mode and fill the repo audit template from exact commits and source evidence.
---

# RMQ External Audit Prompt

Use this skill to prepare an external audit. The coordinator still audits the
report, integrates branches, updates the roadmap, and engineers worker prompts.

## 1. Choose Independence Mode

Read `docs/internal/AUDIT_PROTOCOL.md` and choose:

- **fresh blind delta** for an independent milestone/merge gate;
- **continuation** for one correction loop on that auditor's findings;
- **longitudinal architecture** for periodic milestone comparison;
- **whole frontier** for release or trust-boundary review.

Default to low history and high evidence. Do not give a fresh auditor prior
verdicts or full transcripts. A commit alone is not enough: name base, target,
scope, design intent, acceptance criteria, load-bearing surfaces, and checks.

Keep model/mode recommendations outside the pasted prompt as coordinator launch
metadata.

## 2. Build The Packet

Use `docs/internal/templates/AUDIT_PROMPT.md` and, when useful,
`scripts/make_audit_packet.ps1`. Include:

- auditor handle and audit mode;
- exact base/target commits and branch;
- active roadmap node and intended change;
- relevant theorem aliases, source theorems, trust/claim docs, and decision
  entries;
- required commands and platform caveats;
- explicit non-goals and rejection conditions;
- durable report path under `docs/internal/audit_reports/`.

For claim wording, also read
`docs/internal/CLAIM_DRIFT_POLICY.md`.

## 3. Demand Adversarial Evidence

Require the auditor to test literal truth and the spirit of the roadmap target.
Specifically look for technically correct wrappers, renamed caveats, decorative
reads, proof-only answers, uncounted storage, synthetic events, or valuable work
that advances a different goal.

Also ask the auditor to reconstruct the requirement-to-evidence matrix from
frozen IDs and exact requirements. In fresh-blind mode, withhold the worker
verdict and narrative. Require checked theorem types and expanded object
arguments; a declaration-name inventory is not evidence. Treat a completion
report's own "remaining risk", "reviewer should ask", or "next consumer must
prove" language as presumptive evidence of incomplete closure.

For combined public claims, require an explicit identity chain showing that
space, execution, provenance, and machine facts concern the same construction.
For whole-machine claims, inventory every segment in the physical embedding and
check that one query-independent width/capacity is related to input size. Audit
claim-drift policies and allowlists rather than treating green output as ground
truth. For machine-backed work, also require backward value dependency and
actual address-capacity checks, including tiny and dead/sentinel cases.

Positive evidence tiers are kernel theorem, model theorem, executable
validation, artifact evidence, then process evidence. Process reports do not
prove mathematical or executable claims.

## 4. Require A Useful Report

Ask for findings first, P0 through P3, with exact source/theorem/command
evidence, stale objections, verification outcomes, roadmap alignment, and the
best next target. Report-only auditors may write exactly the assigned report
file; proof/source files remain read-only.

Afterward the coordinator verifies the report, records dispositions, updates
the worker lifecycle/roadmap, and engineers the next prompt set.
