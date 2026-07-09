# Workflow Design Decisions

This ledger records design decisions about the ADD workflow itself: how work is
delegated, audited, evidenced, automated, and handed back to the proof/code
roadmap.

Use `DESIGN_DECISIONS.md` for proof-model, theorem-surface, code architecture,
and artifact-claim decisions. Use this file when the decision changes the
research process, worker protocol, audit protocol, model-routing policy, or
automation shape.

Workflow design decisions are still design decisions. They affect the quality
and trustworthiness of the project, but they are process/provenance evidence,
not proof evidence.

## WDD-20260708-001: Log ADD Improvements As Workflow Design Decisions

Status: Accepted
Date: 2026-07-08
Scope: ADD process governance.

Decision:

Nontrivial ADD workflow improvements must be logged as workflow design
decisions, either in this file or in a successor workflow ledger.

Context:

The project now treats ADD as a deliberate research workflow rather than an
informal habit. Changes to worker prompts, audit definitions, evidence tiers,
automation, model routing, or transcript/provenance policy can materially affect
the quality of the formalization effort.

Options considered:

- Leave workflow choices scattered across worker prompts and chat history.
- Put all workflow choices into the same ledger as proof/code decisions.
- Keep a separate workflow ledger while cross-linking major decisions from the
  general design log when they touch proof or artifact claims.

Rationale:

A separate workflow ledger keeps process decisions visible without mixing them
with theorem and source-architecture decisions. Cross-links avoid splitting the
history when a choice affects both process and proof surface.

Consequences:

Workers making nontrivial changes to ADD infrastructure should update this file
or explicitly report why no workflow-design update was needed.

Evidence:

- `docs/internal/AUDIT_PROTOCOL.md`
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`
- `docs/internal/DESIGN_DECISIONS.md`

Follow-up:

Update worker/audit prompt templates to include a workflow-design-decision check
once those templates are created.

Supersedes:

None.

## WDD-20260708-002: Add Repo-Native ADD Tooling Before Model-Specific Automation

Status: Accepted
Date: 2026-07-08
Scope: ADD tooling sequence.

Decision:

Prioritize repo-native templates, audit packets, claim-drift scans,
design-decision reminders, and CI artifacts before building model-specific
orchestration.

Context:

Codex, Claude, and other models can all participate in ADD, but the workflow
should be reliable because evidence is standardized. A model-specific
orchestrator would be premature before prompts, scans, logs, and acceptance
criteria are stable.

Options considered:

- Build a Codex SDK/MCP orchestrator immediately.
- Ask external auditors to infer context from raw chat exports.
- Standardize worker/audit packets and evidence checks first.

Rationale:

Repo-native process tools are inspectable, versioned, and model-agnostic. They
reduce coordination errors without expanding the proof trust base.

Consequences:

The next ADD tooling worker should implement prompt templates and advisory
scripts before experimenting with a full automation harness.

Evidence:

- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`
- `docs/internal/AUDIT_PROTOCOL.md`

Follow-up:

After two or more real uses, revisit whether to create dedicated `rmq-audit` and
`rmq-worker` skills or a non-interactive orchestration command.

Supersedes:

None.
