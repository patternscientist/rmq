# Internal Engineering Notes

This directory keeps proof-sprint history, orchestration policy, and
component-design audits out of the public artifact-docs path while preserving
the reasoning trail.

For public artifact status, start with:

- [`../WHAT_IS_PROVED.md`](../WHAT_IS_PROVED.md)
- [`../TRUST_BASE.md`](../TRUST_BASE.md)
- [`../FAMILY_SUMMARY.md`](../FAMILY_SUMMARY.md)
- [`../ROADMAP.md`](../ROADMAP.md)

Useful internal entry points:

- [`AUDIT_PROTOCOL.md`](AUDIT_PROTOCOL.md): repo-local definition of audit
  modes, severity, evidence, and report shape for coordinator and external
  reviews.
- [`CLAIM_DRIFT_POLICY.md`](CLAIM_DRIFT_POLICY.md): policy for sensitive public
  claim wording and how scans should evolve when claims are superseded.
- [`DESIGN_DECISIONS.md`](DESIGN_DECISIONS.md): architecture and proof-model
  decision ledger for choices that future workers should preserve or
  explicitly supersede.
- [`WORKFLOW_DESIGN_DECISIONS.md`](WORKFLOW_DESIGN_DECISIONS.md): ADD/process
  decision ledger for audit, delegation, automation, and evidence-policy
  choices.
- [`RMQ_FINAL_ROADMAP.md`](RMQ_FINAL_ROADMAP.md): delegation-ready ladder for
  the final RMQ paper-hardening sequence.
- [`ADD_WORKFLOW_TOOLING_PLAN.md`](ADD_WORKFLOW_TOOLING_PLAN.md): repo-native
  tooling plan for making audit-driven development repeatable before roadmap
  work begins.
- [`templates/`](templates/): reusable worker, audit, coordinator re-entry, and
  coordinator handoff prompts.
- [`CODEX_AUTONOMY.md`](CODEX_AUTONOMY.md) and
  [`WORKER_INTEGRATION_CHECKLIST.md`](WORKER_INTEGRATION_CHECKLIST.md):
  proof-sprint and worker-loop discipline.
- [`SUCCINCT_FINAL_PATH.md`](SUCCINCT_FINAL_PATH.md) and
  [`SUCCINCT_RESEARCH_AND_PLAN.md`](SUCCINCT_RESEARCH_AND_PLAN.md):
  historical path to the succinct RMQ capstone.
- [`LOCAL_BP_DECODER_PATH.md`](LOCAL_BP_DECODER_PATH.md),
  [`INTERIOR_NAVIGATOR_DESIGN.md`](INTERIOR_NAVIGATOR_DESIGN.md), and
  [`SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md`](SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md):
  component-specific design notes.
- `AUDIT_*.md` and `*_AUDIT.md`: adversarial audit records and design
  postmortems.
