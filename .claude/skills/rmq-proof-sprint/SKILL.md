---
name: rmq-proof-sprint
description: Use for narrow RMQ Lean proof, construction, representation, store/trace/cost-model, validation, or theorem-surface work. Enforces the completion gate — frozen acceptance matrices, anti-vacuity evidence, and honest candidate reporting.
---

# RMQ Proof Sprint (Claude runtime wrapper)

This is the Claude-runtime surface for the canonical skill. Read and follow
`.agents/skills/rmq-proof-sprint/SKILL.md` and everything under
`.agents/skills/rmq-proof-sprint/references/` (especially
`COMPLETION_GATE.md` and `KNOWN_FAILURE_MODES.md`) in this repository —
those files are the single source of truth; do not duplicate their content
here.

Claude-runtime adaptations (user-authorized 2026-07-17):

- Freeze the acceptance matrix in its own commit BEFORE implementation edits
  so the freeze is git-verifiable (process lesson from the E1-01R3 audit).
- Maintain a committed worklog checkpoint at each milestone so a successor
  session can resume from commits alone.
- Acquire `Global\RMQHeavyVerification` before any command expected to exceed
  five minutes; release in finally.
- Workers report only CANDIDATE_COMPLETE / INCOMPLETE / OBSTRUCTED / BLOCKED;
  the coordinator records ACCEPTED after independent reconstruction and any
  mandatory blind exact-commit audit.
