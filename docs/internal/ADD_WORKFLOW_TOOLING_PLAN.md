# ADD Workflow Tooling Plan

This document records the obvious process/tooling additions to make
audit-driven development repeatable before the final RMQ roadmap is executed.
ADD remains a workflow discipline. It is not part of the proof trust base.

## Research-Synthesis Position

The strongest near-term ADD improvements are repo-native and model-agnostic:

- make worker prompts uniform and theorem-shaped;
- make audit packets reproducible;
- make claim-drift scans cheap;
- make design decisions mandatory at the point of architectural change;
- treat nontrivial ADD/process changes as workflow design decisions;
- archive CI logs, timings, and artifact outputs where reviewers can inspect
  them;
- use Codex, Claude, and other agents through the same evidence standard rather
  than by reputation.

Tool-specific automation should come after those pieces exist. Otherwise the
automation only accelerates an underspecified process.

## What To Add First

### 1. Worker Prompt Template

Path:

- `docs/internal/templates/WORKER_PROMPT.md`

Purpose:

- force every worker task to name the branch base, write scope, target theorem or
  document, forbidden shortcuts, verification commands, and completion report;
- prevent "clean partial checkpoint" reports when the next formal step is
  available;
- make proof-digestion output standard.

Required sections:

- Base branch and worktree assumptions.
- Goal in one sentence.
- Concrete target theorem/file names.
- Non-goals and forbidden shortcuts.
- Verification commands.
- Completion report format:
  - theorem names or changed docs;
  - conceptual meaning;
  - live assumptions;
  - skeptical-reviewer questions;
  - exact command outcomes.

Status:

- Implemented as `docs/internal/templates/WORKER_PROMPT.md`.

### 2. Audit Prompt Template

Path:

- `docs/internal/templates/AUDIT_PROMPT.md`

Purpose:

- make audits evidence-classed rather than vibe-based;
- distinguish correctness bugs, claim drift, architecture friction, artifact
  weakness, and style/elegance concerns;
- require source locations and command evidence for each finding.

Required sections:

- Audit scope.
- Read-only or write permission.
- Current claim surface to inspect.
- Evidence tiers to use.
- Required commands.
- Report shape:
  - blockers first;
  - theorem evidence;
  - docs/artifact drift;
  - recommended next theorem-shaped targets.

Status:

- Implemented as `docs/internal/templates/AUDIT_PROMPT.md`.

### 2a. Coordinator Re-Entry And Handoff Templates

Paths:

- `docs/internal/templates/COORDINATOR_REENTRY_PROMPT.md`
- `docs/internal/templates/COORDINATOR_HANDOFF_PACKET.md`

Purpose:

- make high-context coordination refreshable from source;
- make context-health and fresh-coordinator handoff normal workflow events;
- preserve enough frontier/design context for the next coordinator to continue
  without inheriting stale chat assumptions.

Status:

- Implemented.

### 3. Audit Packet Generator

Path:

- `scripts/make_audit_packet.ps1`

Purpose:

- collect the exact context an external auditor needs without dumping raw
  transcripts or unrelated scratch files.

Suggested output:

- `git status --short --branch`
- `git log --oneline --decorate -20`
- `git tag --list`
- `git diff --stat origin/main...HEAD`
- relevant theorem roots and docs:
  - `RMQPaper.lean`
  - `RMQ/Headlines/RMQ.lean`
  - `docs/PAPER_CLAIM_CORRESPONDENCE.md`
  - `docs/WHAT_IS_PROVED.md`
  - `artifact/CLAIMS.md`
  - `docs/internal/DESIGN_DECISIONS.md`
  - `docs/internal/AUDIT_PROTOCOL.md`
- recent verification command outputs if present.

The script should avoid private chat exports by default.

Status:

- Implemented as `scripts/make_audit_packet.ps1`.

### 4. Claim-Drift Scan Script

Path:

- `scripts/claim_drift_scan.ps1`

Purpose:

- make stale public language cheap to catch before audits.

Initial scan terms:

- `first mechanized`
- `first-ever`
- `apparently not previously`
- `cannot be forged`
- `forged`
- `artifact ready`
- `AE-ready`
- `Lean runtime`
- `2^128`
- `196727`
- `118`
- `no extraction gap`

The script should print matched file/line pairs and exit nonzero only in a
strict mode, so exploratory branches can use it without fighting intentional
mentions.

Status:

- Implemented as `scripts/claim_drift_scan.ps1` with policy in
  `docs/internal/CLAIM_DRIFT_POLICY.md` and
  `docs/internal/CLAIM_DRIFT_POLICY.json`.

### 5. Design-Decision Check

Path:

- `scripts/design_decision_check.ps1`

Purpose:

- make architectural changes update `docs/internal/DESIGN_DECISIONS.md`.

Suggested behavior:

- if changed files include `RMQPaper.lean`, `RMQ/Headlines/RMQ.lean`,
  `RMQ/Core/SuccinctRMQClassic.lean`, `RMQ/Core/WordRAM*`, artifact docs, or
  paper theorem-map docs, print a reminder to inspect the design log;
- strict mode may require that the design log changed on branches touching a
  configured set of architecture-sensitive paths.

This should be advisory at first. Mandatory enforcement can come after the team
has used the log for a few branches.

The check should cover both `docs/internal/DESIGN_DECISIONS.md` and
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md`: proof/code architecture changes go
in the former, while ADD process, audit, automation, and model-routing changes
go in the latter.

Status:

- Implemented as `scripts/design_decision_check.ps1`.

### 6. CI Artifact Outputs

Existing GitHub Actions should be extended only after the scripts above exist.

Purpose:

- archive audit packets, artifact reproduction logs, and timings;
- make reviewer-visible CI evidence easy to download;
- reduce dependence on local terminal transcripts.

Candidate additions:

- upload `artifact-repro` logs as workflow artifacts;
- record command timings;
- run `scripts/claim_drift_scan.ps1` in advisory mode;
- run `scripts/design_decision_check.ps1` in advisory mode on pull requests.

Status:

- CI now runs the advisory claim-drift and design-decision scans.
- Artifact reproduction now uploads an audit packet.

### 7. Issue Or PR Templates

Paths:

- `.github/ISSUE_TEMPLATE/audit.yml`
- `.github/ISSUE_TEMPLATE/worker.yml`
- `.github/pull_request_template.md`

Purpose:

- make every proof branch declare its target theorem and verification evidence;
- make every docs/process branch declare which public claims were touched;
- make every audit distinguish blockers from optional cleanup.

These are useful after the roadmap branch merges, but they are lower priority
than the prompt templates and scripts.

Status:

- Implemented initial issue and pull-request templates.

## What To Defer

Do not begin with:

- a full Codex SDK orchestrator;
- automatic external-auditor launches;
- a custom MCP dashboard;
- mandatory pre-commit install;
- ingesting raw chat transcripts as repository evidence;
- model-routing experiments as a substitute for evidence-classed audits.

These can all become useful. They should sit on top of stable templates,
scripts, and CI outputs.

## Model Routing Policy

ADD should route by task risk, not by model prestige.

Initial policy:

- coordinator and architecture synthesis: strongest available model;
- proof workers on ambitious theorem targets: strongest available model until
  success patterns are established;
- read-only claim-drift scans: cheaper models are acceptable when backed by
  exact grep/build evidence;
- independent validation and example generation: cheaper models are acceptable
  if outputs are checked by Lean/CI;
- final public-claim audits: at least one strong external model plus local
  coordinator audit.

Future experiment:

- create `docs/internal/MODEL_ROUTING_MATRIX.md` after 5 to 10 comparable tasks;
- compare false-positive rate, missed-blocker rate, time to usable branch, and
  coordinator cleanup cost;
- do not judge models by how confident their reports sound.

## Skill And Agent Additions

Likely useful after templates stabilize:

- an `rmq-audit` skill that reads `AUDIT_PROTOCOL.md`, theorem-map docs, and the
  audit prompt template;
- an `rmq-worker` skill that reads the worker prompt template, design-decision
  policy, and verification gates;
- a non-interactive audit command that runs the audit packet generator and
  claim-drift scan.

Do not create these skills until the templates have been used on at least two
real branches. Premature skills freeze accidental wording.

Current exception:

- The coordinator and audit skills were created now because the workflow itself
  needs a stable coordinator handoff and audit entry point before practicing the
  final roadmap. Keep them concise and revise after real use.

## Trust Boundary

ADD evidence is process evidence:

- it can explain why branches were explored;
- it can surface skeptical questions;
- it can preserve design reasoning;
- it can improve audit coverage.

It is not proof evidence. The public proof artifact rests on Lean kernel-checked
theorems, checked executable validation where claimed, and reproducible CI or
artifact logs.

## Research Basis

- Codex documentation:
  <https://developers.openai.com/codex/>
- Introducing Codex:
  <https://openai.com/index/introducing-codex/>
- GitHub Actions documentation:
  <https://docs.github.com/en/actions>
- GitHub workflow artifacts:
  <https://docs.github.com/en/actions/tutorials/store-and-share-data>
- pre-commit:
  <https://pre-commit.com/>
- ACM artifact review and badging:
  <https://www.acm.org/publications/policies/artifact-review-and-badging-current>
