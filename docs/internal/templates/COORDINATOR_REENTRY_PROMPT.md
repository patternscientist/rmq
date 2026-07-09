# Coordinator Re-Entry Prompt Template

Use this when starting a fresh coordinator chat or when the current coordinator
state may be stale.

```text
You are the main RMQ coordinator. Do a read-only re-entry/frontier
reconstruction pass before proposing workers or edits.

Repo: [PATH]
Expected base/frontier, if any: [BRANCH/COMMIT or "unknown"]

Tasks:
1. Inspect git state:
   - current branch and HEAD;
   - dirty files;
   - recent commits and tags;
   - relevant worker branches/worktrees;
   - whether [KNOWN_BRANCH_OR_COMMIT] has merged or been replaced.
2. Read the coordination/trust surface:
   - docs/internal/RMQ_FINAL_ROADMAP.md
   - docs/internal/AUDIT_PROTOCOL.md
   - docs/internal/DESIGN_DECISIONS.md
   - docs/internal/WORKFLOW_DESIGN_DECISIONS.md
   - docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md
   - docs/internal/CLAIM_DRIFT_POLICY.md
   - RMQPaper.lean
   - RMQ/Headlines/RMQ.lean
   - docs/PAPER_CLAIM_CORRESPONDENCE.md
   - docs/WHAT_IS_PROVED.md
   - artifact/CLAIMS.md
3. Reconstruct:
   - final RMQ theorem frontier;
   - public claim/artifact frontier;
   - ADD/process/tooling frontier;
   - open proof blockers and open docs/artifact blockers.
4. Audit for stale claims or stale process:
   - claim drift;
   - unlogged design/workflow decisions;
   - context-handoff need;
   - overclaiming around model cost, Lean runtime, executable evidence,
     novelty, or artifact readiness.
5. Produce:
   - current frontier report;
   - what is closed;
   - what remains;
   - what should not be worked on next;
   - top 3 next prompts, ranked;
   - recommended model/mode for each worker prompt and why.

Do not edit files in this pass unless explicitly asked.
```
