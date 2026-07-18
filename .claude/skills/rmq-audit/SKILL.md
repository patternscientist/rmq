---
name: rmq-audit
description: Use for preparing external audit prompts and evidence packets, and for running fresh blind exact-commit audits of RMQ candidates against frozen contracts.
---

# RMQ Audit (Claude runtime wrapper)

This is the Claude-runtime surface for the canonical skill. Read and follow
`.agents/skills/rmq-audit/SKILL.md` in this repository — that file is the
single source of truth; do not duplicate its content here. Also follow
`docs/internal/AUDIT_PROTOCOL.md`.

Claude-runtime adaptations (user-authorized 2026-07-17):

- Fresh blind auditors receive exact commits and an audit packet, never the
  worker verdict, live worktree, or chat transcript — unchanged from the
  canonical protocol; on this runtime, launch them as fresh sessions or
  background Agents with detached checkouts of the exact commit.
- For genuine independence, prefer a different model family for the blind
  audit than the one that authored the candidate.
- Log each audit round to the round log in
  `docs/internal/AUDIT_AND_A_DESIGN.md` (standing default) and, for A-series
  blind audits, to `docs/internal/audit_reports/`.
