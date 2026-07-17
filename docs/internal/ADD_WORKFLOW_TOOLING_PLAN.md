# ADD Workflow Tooling Plan

ADD is a model-agnostic research workflow. It improves search, review, and
provenance; it is not part of the proof trust base.

## Landed Foundation

The repository has worker/audit/coordinator templates, coordinator/proof/audit
skills, audit-packet and policy scans, decision ledgers, CI advisory evidence,
issue/PR templates, and durable audit-report storage.

## Immediate Hardening

### Pin Skill Discovery To The Workflow Frontier

Every RMQ task must separate its workflow-governance ref from any older source
commit being inspected. Before substantive work, compare the canonical
`.agents/skills` inventory at that governance ref with both the checkout and the
runtime project-skill catalog. A missing preflight, stale checkout skill,
missing runtime skill, or unavailable explicitly named skill is a startup
blocker: report it, do not substitute, and restart from a governance-containing
project checkout. Repository scripts cannot refresh an already initialized
Codex task catalog.

Keep the repo-local skill packages authoritative. Do not solve stale-checkout
discovery by maintaining unversioned user-global duplicates; that trades a
visible missing-skill failure for silent policy-version drift.

### Keep Skills Thin

The roadmap, audit protocol, and decision ledgers are sources of truth. Skills
route work and enforce the loop; historical failure modes live in on-demand
references. Do not copy large planning documents into every worker context.

### Track The Full Worker Lifecycle

Use `WORKER_LIFECYCLE.md`. Integration is not completion until the branch and
worktree are archived/retired. Add a machine-readable active-task ledger only
when concurrent volume justifies it.

### Standardize Evidence Manifests

Extend audit packets with JSON fields for handle/task type, base/target commits,
command/exit/timestamp/platform, evidence tier/log path, roadmap node, and
acceptance criteria. Keep Markdown reports for humans.

### Strengthen CI With Familiar Lean Tools

Adopt in order:

1. `leanprover/lean-action` for pinned setup while retaining the repo gate;
2. advisory/nightly `nanoda` checking, distinct from the kernel gate;
3. `leanprover-community/import-graph` in a separate tooling environment.

Do not add Mathlib or broaden the project Lake dependency graph for tooling.

### Automate Read-Only Work First, Then Audited Worker Chains

Good initial Codex automation targets:

- scheduled claim-drift/import-closure reports;
- `codex exec --json --output-schema` for structured read-only audits;
- session re-entry, pre-compaction, and advisory completion hooks;
- automatic audit-packet generation on pull requests.

Do not autonomously merge, delete worktrees, choose proof architecture, or run
unreviewed proof-writing loops. After prompt/evidence gates have survived real
cycles, an explicit user opt-in may authorize a reviewed worker chain: create a
fresh governed Codex task from a preflighted `READY_TO_SEND` prompt, monitor it
without steering, audit its exact completion independently, complete reusable
failure-mode feedback, and launch only the next preflighted successor. Keep one
monitor per worker, suppress duplicate handle/base/branch launches, and stop at
unresolved integration, skill-runtime, dependency, concurrency, or architecture
boundaries.

Default nontrivial Lean and public-theorem work to the strongest ordinary
reasoning setting needed by its contract, normally `gpt-5.6-sol` at `max`.
Reserve `ultra` for an explicitly recorded exceptional need. The automated
chain does not expand merge, push, publication, or destructive-cleanup
authority.

### Measure Model Routing

After 5 to 10 comparable tasks, record missed blockers, false positives, time to
accepted branch, coordinator cleanup, token/cost use, and verification strength.
Use strongest available models for coordination, architecture, nontrivial
proof, and final public-claim audits. Pilot cheaper models where outputs are
mechanically checkable.

## External Audit Policy

Use low history and high evidence: fresh blind sessions for independent gates,
the same session for one correction loop, a persistent longitudinal auditor
every two to four milestones, and a fresh session for final acceptance.

A commit alone is not an audit packet. Include base, target, scope, design
intent, load-bearing surfaces, and checks. Prefer source-grounded digests to
full transcripts.

## Later Experiments

- Pilot deterministic optimization only after the cost harness has stable,
  verified objectives.
- Evaluate Shepherd/Shep-style branch tooling only in a sandbox; lifecycle
  visibility must not replace project policy.
- Build SDK/MCP orchestration after evidence schemas and lifecycle rules survive
  several real cycles.

## Trust Boundary

Checked theorems, explicit model theorems, reproducible executables, and CI logs
support claims. Agent reports, model comparisons, and ADD logs are process
evidence only.
