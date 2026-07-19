# Coordinator Handoff Packet Template

Use this before moving RMQ coordination to a fresh chat.

```text
RMQ Coordinator Handoff

Repo:
- Path:
- Current branch:
- HEAD:
- Base:
- Dirty files:
- Workflow-governance ref:
- Canonical RMQ skills at that ref:
- Required coordinator skill: rmq-coordinator
- Runtime RMQ skill catalog observed in the new task:
- Skill-preflight command/result:

Startup hard stop:
- Before substantive work, the new task must run the project skill preflight
  against the workflow-governance ref. If the preflight script is absent, any
  canonical skill is absent/stale in the checkout, or any explicitly required
  role skill is absent from the runtime catalog, stop and report the mismatch.
  Unrelated role skills need not be runtime-injected. Do not substitute another
  skill.
- A failed preflight requires a governance-containing checkout and task restart
  unless the user explicitly authorizes a disclosed fallback. A fallback may
  not ACCEPT, integrate, or close a roadmap node.

Merged since last handoff:
- [branch/commit -> meaning]

Unmerged worker branches:
- [branch/worktree/commit -> status, owner, risk]

Current theorem frontier:
- Closed:
- Open:
- Next theorem-shaped target:

Current docs/artifact frontier:
- Closed:
- Open:
- Claim-drift risks:

Current ADD/workflow frontier:
- Closed:
- Open:
- Workflow decisions logged:

Design decisions since last handoff:
- Code/proof/artifact:
- Workflow/process:

Verification evidence:
- Commands run:
- Commands skipped and why:
- Last known failures:

Top next prompts:
1. [highest priority]
2. [second]
3. [third]

Do not work on next:
- [non-goals]

Coordinator warning signs:
- [context risks, stale assumptions, branch hazards]
```
