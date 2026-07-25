---
name: rmq-coordinator
description: Use for high-context RMQ coordination — re-entry/frontier reconstruction, completed-worker audit, branch integration, roadmap planning, worker delegation, design-decision logging, and coordinator handoffs. Use when coordinating RMQ work rather than implementing a narrow Lean proof.
---

# RMQ Coordinator (Claude runtime wrapper)

This is the Claude-runtime surface for the canonical skill. Read and follow
`.agents/skills/rmq-coordinator/SKILL.md` in this repository — that file is
the single source of truth; do not duplicate its content here.

Claude-runtime adaptations (WDD-pending; user-authorized 2026-07-17):

- The `scripts/project_skill_preflight.ps1` runtime-catalog check is satisfied
  by this wrapper's presence in the session skill catalog PLUS a git check
  that `.agents/skills/` at the governance ref matches the working tree
  (`git diff <governance-ref> -- .agents/skills` must be empty). Report the
  governance ref, HEAD, and that comparison in place of the Codex catalog
  string.
- Where the canonical skill says "Codex task" / "Codex worktree task", read
  "dedicated worker session or background Agent with its own git worktree".
- Heavy verification (>5 min) still coordinates via the Windows mutex
  `Global\RMQHeavyVerification`, including from wrapper scripts around
  background gates/builds.
- Model routing guidance lives in `docs/internal/RMQ_FINAL_ROADMAP.md` and
  the coordinator memory; recommend exact model + reasoning tier per task in
  launch metadata, as the canonical skill requires.
