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

## WDD-20260708-003: Add Coordinator And Audit Skills Before Roadmap Practice

Status: Accepted
Date: 2026-07-08
Scope: ADD skill routing.

Decision:

Create repo-local `rmq-coordinator` and `rmq-audit` skills, and reroute
`rmq-proof-sprint` toward proof-worker implementation rather than broad
coordination or read-only audit work.

Context:

The proof-sprint skill had accumulated both proof-worker rules and coordinator
habits. That made it too heavy for high-context coordination and too broad for
read-only audits.

Options considered:

- Keep adding coordinator and audit rules to `rmq-proof-sprint`.
- Create separate skills for coordinator, audit, and proof-worker roles.
- Delay skills until after more roadmap practice.

Rationale:

Separate skills make role boundaries explicit: coordinator reconstructs and
delegates, audit falsifies against evidence, and proof sprint implements narrow
Lean targets. The skills point back to versioned repo docs rather than
inventing parallel policy.

Consequences:

Future coordinator re-entry should use `rmq-coordinator`; branch and claim
audits were initially assigned to `rmq-audit`; narrow theorem work should use
`rmq-proof-sprint`. WDD-20260708-008 later refines the audit split: the
coordinator owns completed-worker audit/integration, while `rmq-audit`
engineers external-auditor prompts and packets.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`
- `.agents/skills/rmq-audit/SKILL.md`
- `.agents/skills/rmq-proof-sprint/SKILL.md`

Follow-up:

Revise the skills after two or more real roadmap uses; move any bulky historical
trap inventories into references if they keep crowding the proof skill.

Supersedes:

None.

## WDD-20260708-008: Let Coordinator Own Integration Audits And Repurpose Audit Skill

Status: Accepted
Date: 2026-07-08
Scope: ADD skill routing and worker integration.

Decision:

`rmq-coordinator` owns the recurring coordinator cycle: audit completed worker
branches, integrate accepted work, synchronize public/docs/design surfaces, then
consult the current roadmap and produce the next ambitious prompt set with
maximum effective parallelization. `rmq-audit` is repurposed as the skill for
engineering external-auditor prompts and audit packets from current repository
context, using `docs/internal/templates/AUDIT_PROMPT.md` and the audit protocol.

Context:

In practice, a coordinator audit almost never stops at falsification. The useful
workflow is audit plus integration plus next-step planning. External auditors,
especially non-Codex auditors, do not use a Codex skill; they need a filled
prompt and evidence packet. Keeping a separate local `rmq-audit` skill for
ordinary branch audits duplicated coordinator responsibility and made the skill
boundary fuzzy.

Options considered:

- Keep `rmq-audit` as a local read-only branch-audit skill.
- Delete the audit skill and leave external-auditor prompts ad hoc.
- Move completed-worker audits into `rmq-coordinator` and repurpose `rmq-audit`
  for external audit prompt engineering.

Rationale:

The new split matches actual workflow roles. The coordinator remains accountable
for source-grounded integration and roadmap continuation. The audit skill
becomes a prompt-engineering tool for auditors outside the coordinator loop,
which is where a specialized audit template is genuinely useful.

Consequences:

Coordinator reports after worker audits should include merge/integration status
and the next prompt set, not just a verdict. External audit requests should
produce a filled audit prompt with scope, evidence tiers, required checks, and
recommended auditor/model/mode. Future references to `rmq-audit` should not
imply that normal worker integration is delegated away from the coordinator.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`
- `.agents/skills/rmq-audit/SKILL.md`
- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `docs/internal/templates/AUDIT_PROMPT.md`

Follow-up:

After the next external audit request, evaluate whether `rmq-audit` should be
renamed to `rmq-external-audit-prompt` or whether the revised description is
clear enough.

Supersedes:

WDD-20260708-003 for the branch/claim audit routing portion.

## WDD-20260708-004: Make Context Health And Coordinator Handoff Routine

Status: Accepted
Date: 2026-07-08
Scope: Coordinator continuity.

Decision:

Treat coordinator handoff as a normal workflow event triggered by context
health, not as an emergency response after the chat has already degraded.

Context:

The RMQ work depends on high-context synthesis, but long chats can create stale
branch assumptions and audit-text overfitting. Fresh coordinators work best when
given a checked frontier packet rather than raw transcript sprawl.

Options considered:

- Keep a single coordinator chat until it fails.
- Export all raw transcripts as the main handoff evidence.
- Use a structured handoff packet with git state, theorem frontier, docs
  frontier, design decisions, verification evidence, and next prompts.

Rationale:

Structured handoff preserves continuity while forcing the next coordinator to
reconstruct from source. It also avoids treating private chat traces as public
artifact evidence.

Consequences:

Before major proof branches, merge waves, public-claim freezes, or low-context
continuations, create a handoff packet using the coordinator template.

Evidence:

- `docs/internal/templates/COORDINATOR_REENTRY_PROMPT.md`
- `docs/internal/templates/COORDINATOR_HANDOFF_PACKET.md`
- `.agents/skills/rmq-coordinator/SKILL.md`

Follow-up:

Practice the handoff template after the first final-roadmap worker branch.

Supersedes:

None.

## WDD-20260708-005: Make Design Logs Serve Future Paper Exposition

Status: Accepted
Date: 2026-07-08
Scope: Design-decision writing standard.

Decision:

Design-decision entries should be written so a future coordinator can assemble
paper exposition about design choices, rejected alternatives, model boundaries,
and workflow provenance without reverse-engineering chat history.

Context:

Publication venues expect discussion of design choices, alternatives, related
work, limitations, and proof-assistant lessons. A terse implementation diary is
not enough; the design logs should preserve the argumentative shape of the
formalization.

Options considered:

- Use design logs only as internal reminders.
- Put paper exposition only in the final manuscript.
- Record rationale, alternatives, consequences, and evidence at decision time.

Rationale:

Decision-time logging captures the live reason for a choice while it is still
fresh and makes later paper writing much less archaeology-heavy.

Consequences:

Both design ledgers should include context, options considered, rationale,
consequences, evidence, follow-up, and supersession when a nontrivial decision
is logged.

Evidence:

- `docs/internal/DESIGN_DECISIONS.md`
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
- `docs/internal/templates/WORKER_PROMPT.md`

Follow-up:

Audit future design-log entries during branch integration for paper-exposition
usefulness, not merely existence.

Supersedes:

None.

## WDD-20260708-006: Make Claim-Drift Scans Policy-Governed Tripwires

Status: Accepted
Date: 2026-07-08
Scope: Claim drift and public wording scans.

Decision:

Claim-drift scans should be governed by a versioned policy. Sensitive terms are
tripwires whose allowed status changes when theorem or artifact truth changes.

Context:

Some scanned terms, such as `196727`, can move from public theorem truth to
legacy compatibility language after proof work. A static grep list would either
freeze old claims or create noisy false positives.

Options considered:

- Keep a hard-coded scan list with no policy.
- Remove terms once they become superseded.
- Keep policy entries that classify terms as current, qualified, scoped,
  legacy-only, historical, or forbidden.

Rationale:

Policy-governed scans enforce freshness and precision without preventing real
progress from changing the public claim surface.

Consequences:

When a sensitive theorem or public claim is superseded, workers must update the
theorem/docs, claim-drift policy, and design log together.

Evidence:

- `docs/internal/CLAIM_DRIFT_POLICY.md`
- `docs/internal/CLAIM_DRIFT_POLICY.json`
- `scripts/claim_drift_scan.ps1`

Follow-up:

Move policy entries from advisory to strict as patterns stabilize.

Supersedes:

None.

## WDD-20260708-007: Make Model Recommendations And Worker Commits Explicit

Status: Accepted, amended by WDD-20260709-009
Date: 2026-07-08
Scope: Worker prompt protocol and model routing.

Decision:

Every coordinator-issued delegation package should include a recommended
model/mode and a short reason, but the model recommendation belongs in the
coordinator's chat with the user rather than in the prompt text pasted to the
worker. Nontrivial Lean proof work should use 5.5 Extra High or a stronger
available mode by default. Smaller docs, grep-only audit, validation, or
mechanical tooling tasks may use cheaper modes when their outputs are
straightforward to verify. Worker prompts should still instruct workers to
commit their finished branch by default, stage only intended files, and report
the commit hash, unless the task is explicitly read-only or no-commit.

Context:

The project is starting to become token-conscious rather than reflexively
spending the highest-capability setting on every task. At the same time,
ambitious proof work still has high coordination and proof-search risk, so
model downgrades there would be false economy until there is real comparative
evidence. Requiring commits at handoff gives the coordinator an exact artifact
to audit and merge instead of an ambiguous dirty worktree.

Options considered:

- Keep all chats on the same high mode forever.
- Let each worker choose its own model/mode and whether to commit.
- Require the coordinator to name model/mode and require commits for completed
  write tasks.

Rationale:

Explicit model recommendations turn model choice into a reviewable routing
decision without making model identity part of the proof trust base. Commit
requirements reduce coordinator cleanup, make branch audits reproducible, and
force workers to distinguish intended changes from scratch files.

Consequences:

Coordinator reports and prompt handoff notes must carry model/mode metadata.
Worker prompt text should not include model/mode instructions unless a specific
external system requires it. Completion reports for write tasks should include
a commit hash. If a worker does not commit, the coordinator should treat that as
an integration issue unless the prompt was read-only or no-commit.

Evidence:

- `docs/internal/templates/WORKER_PROMPT.md`
- `docs/internal/templates/COORDINATOR_REENTRY_PROMPT.md`
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`

Follow-up:

After several comparable tasks, build a model-routing matrix that records
quality, cleanup cost, missed-blocker rate, and token/time cost by task class.

Supersedes:

None.

## WDD-20260709-009: Split Launch Metadata From Worker Prompts

Status: Accepted
Date: 2026-07-09
Scope: Worker launch protocol and active-worker tracking.

Decision:

Coordinator responses that hand prompts to the user should include launch
metadata outside the worker prompt text: recommended model/mode, why that mode
is recommended, and whether the prompt should go to a fresh worker chat or an
existing worker. The worker prompt itself should omit model/mode instructions.
The coordinator should assign active worker handles using a lightweight
monotone scheme such as `W01-r2-cost`, `W02-r2-scout`, and carry that handle in
the worker prompt and completion report.

Context:

The user chooses the actual chat/model surface. Putting model instructions in
the pasted worker prompt is noisy and can confuse the worker's task focus.
Separately, as worker chats persist across tasks, branch names identify code
artifacts but not necessarily the live worker chat being reused.

Options considered:

- Put model recommendations directly inside worker prompts.
- Omit model recommendations entirely and let every worker run on the default
  chat setting.
- Tell the user the recommended mode/freshness separately, while keeping the
  worker prompt task-focused.
- Identify workers only by branch name.
- Use heavyweight random hashes for worker chats.
- Use simple monotone handles plus branch names.

Rationale:

Separating launch metadata keeps prompts cleaner while preserving
token-conscious routing as a coordinator responsibility. Simple handles are
enough for human coordination, while branch names and commit hashes remain the
durable Git identities for audit and merge.

Consequences:

Future coordinator reports should present each prompt with a short header such
as "Send to fresh worker W03-r3-refactor; recommended mode: 5.5 Extra High".
Worker prompts should include the assigned worker handle, exact branch name,
base branch, and completion-report fields, but not model/mode text. Existing
workers can be reused only when their prior task is complete or the new prompt
is a direct continuation; otherwise use a fresh worker.

Evidence:

- `docs/internal/templates/WORKER_PROMPT.md`
- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`

Follow-up:

If active worker count grows beyond what chat memory can track reliably, add an
`ACTIVE_WORKERS.md` scratch or internal ledger. Until then, coordinator reports
can carry the handle mapping.

Supersedes:

The "worker prompts should name the recommended model/mode explicitly" wording
from WDD-20260708-007.

## WDD-20260709-010: Require Coordinator Close-Out Prompt Engineering

Status: Accepted
Date: 2026-07-09
Scope: Coordinator finish protocol and roadmap delegation.

Decision:

After completed-worker audits, branch integrations, or roadmap-planning turns,
the coordinator should end by engineering the best next ambitious prompt or
prompt set, ready for the user to paste into worker or external-auditor chats,
unless the correct next step is explicitly to wait, hand off, or not launch more
work yet. Launch metadata remains outside the prompt text, as in
WDD-20260709-009.

Context:

The coordinator role is not only to falsify a worker branch or summarize what
landed. The useful cycle is audit, integrate, re-read the roadmap/frontier, and
turn the result into the next concrete delegation. A final line such as "next
target: R3" leaves too much coordination work for the user and increases the
chance that the next worker receives an underspecified or stale prompt.

Options considered:

- Let coordinator reports end with a generic next target.
- Require full prompt engineering only when the user explicitly asks.
- Make prompt engineering the default coordinator close-out, with an explicit
  no-launch reason when delegation would be premature.

Rationale:

Ready-to-paste prompts preserve the current source-grounded frontier at the
moment it is freshest, make maximum effective parallelization explicit, and
reduce prompt drift between audit verdict and next worker launch. Requiring an
explicit no-launch reason also prevents ceremonial delegation when a handoff,
user decision, or unmerged dependency is the wiser next move.

Consequences:

The `rmq-coordinator` skill's finish section now requires final reports to
include what remains open, what not to work on next, and concrete next prompt
artifacts with coordinator-facing launch metadata outside the prompt text.
Future coordinator audits should not stop at "next best target" when a
responsible worker or auditor prompt can be written.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/templates/WORKER_PROMPT.md`
- `docs/internal/templates/AUDIT_PROMPT.md`

Follow-up:

After several uses, check whether coordinator reports are becoming too long and
whether prompt artifacts should move into a short dedicated "Launch" subsection.

Supersedes:

None.

## WDD-20260709-012: Prefix Worker Chat Titles With Worker Handles

Status: Accepted
Date: 2026-07-09
Scope: Worker launch protocol and active-worker tracking.

Decision:

Worker prompts should request chat/thread titles of the form
`({worker handle}) {short task summary}`, for example
`(W03-r3-zero-block) shrink zero-block RMQ cost`. If the environment supports
renaming the chat/thread, the worker should set that title before starting. If
not, the worker should repeat the requested title at the top of the completion
report.

Context:

Workers usually receive automatic descriptive chat names, which is helpful, but
parallel ADD work benefits from seeing both the worker handle and task summary
at a glance. Branch names identify durable Git artifacts; chat titles identify
live coordination surfaces.

Options considered:

- Keep relying on automatically generated task summaries.
- Put only the worker handle in the chat title.
- Prefix the descriptive title with the worker handle in parentheses.

Rationale:

The prefix convention preserves descriptive task names while making active
worker ownership visible in the chat list. It is lightweight enough for humans,
does not require random hashes, and does not replace branch names, worktree
paths, or commit hashes in completion reports.

Consequences:

`docs/internal/templates/WORKER_PROMPT.md` now includes a requested chat/thread
title. `rmq-coordinator` and the coordinator re-entry template remind
coordinators to include that title in launch metadata and generated worker
prompts.

Evidence:

- `docs/internal/templates/WORKER_PROMPT.md`
- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/templates/COORDINATOR_REENTRY_PROMPT.md`

Follow-up:

If live worker counts grow large enough that chat titles are still insufficient,
add an `ACTIVE_WORKERS.md` scratch ledger as described in WDD-20260709-009.

Supersedes:

None.

## WDD-20260709-011: Store Material Audit Reports In The Repo

Status: Accepted
Date: 2026-07-09
Scope: Audit provenance and coordinator accessibility.

Decision:

Material external audit reports should be stored under
`docs/internal/audit_reports/` in addition to being returned in chat. Audit
prompts should name the preferred report file path. If an auditor has write
access, it may write only that report file while source/proof files remain
read-only; if not, the coordinator stores the chat report or a faithful
summary.

Context:

Chat-only audit reports are easy to lose and force future coordinators to rely
on copy-paste context. The ADD workflow benefits from a running, searchable
collection of audit evidence, accepted findings, rejected findings, and
coordinator dispositions.

Options considered:

- Leave audit reports only in chat.
- Store raw transcript dumps as the audit log.
- Store scoped, sanitized markdown reports in the repository.

Rationale:

Repo-native reports make audits discoverable to future coordinators while
preserving the trust boundary: reports are process evidence, not proof
evidence. Scoped markdown files are easier to cite and review than raw chat
transcripts, and they can record coordinator disposition when an auditor
finding is accepted with correction.

Consequences:

`docs/internal/AUDIT_PROTOCOL.md`, `.agents/skills/rmq-audit/SKILL.md`, and
`docs/internal/templates/AUDIT_PROMPT.md` now require or request a durable
report path for material audits. The first stored report is
`docs/internal/audit_reports/2026-07-09_A01_rmq_frontier_audit.md`.

Evidence:

- `docs/internal/AUDIT_PROTOCOL.md`
- `.agents/skills/rmq-audit/SKILL.md`
- `docs/internal/templates/AUDIT_PROMPT.md`
- `docs/internal/audit_reports/README.md`

Follow-up:

If the collection grows large, add an index or split reports by year/month.

Supersedes:

None.

## WDD-20260709-008: Require Explicit Worker Branch Contracts

Status: Accepted
Date: 2026-07-09
Scope: Worker prompt protocol and branch auditability.

Decision:

Every coordinator-issued worker prompt for a write task should name the exact
branch the worker must create, the base branch, and the fresh-worktree
requirement. Completion reports must include the branch name, worktree path,
base branch, and final commit hash. Read-only audit prompts may omit the create
step, but they should still identify the branch, commit, and base being
audited.

Context:

As ADD parallelism increases, the coordinator frequently audits several worker
branches that finish close together. Relying on descriptive prose or chat
memory to identify a worker's branch creates avoidable lookup work and raises
the risk of auditing or merging the wrong artifact.

Options considered:

- Let workers choose branch names freely.
- Ask workers to report branch names after the fact but not prescribe them.
- Require coordinator prompts to prescribe exact branch names and report fields.

Rationale:

Exact branch contracts make worker output mechanically discoverable via
`git worktree list`, `git for-each-ref`, branch comparison, and merge commands.
They also make future paper/process exposition easier: each roadmap rung can be
traced to a named branch, base, commit, checks, and coordinator audit.

Consequences:

`docs/internal/templates/WORKER_PROMPT.md` now includes explicit branch,
worktree, base, and final-report fields. The coordinator skill must fill those
fields before sending a worker prompt. Missing branch/report metadata should be
treated as a coordination defect during worker audit, unless the task was
explicitly read-only or branchless.

Evidence:

- `docs/internal/templates/WORKER_PROMPT.md`
- `.agents/skills/rmq-coordinator/SKILL.md`

Follow-up:

Use roadmap-rung branch names such as `codex/rmq-r2-clean-allsize-cost` for
proof branches, and keep names short enough for audit reports and command-line
use.

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

This branch implements the first pass of prompt templates, advisory scripts,
skills, policy files, and CI hooks. Future ADD work should practice and refine
these pieces before experimenting with a full automation harness.

Evidence:

- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`
- `docs/internal/AUDIT_PROTOCOL.md`

Follow-up:

After two or more real uses, revisit whether to create dedicated `rmq-audit` and
`rmq-worker` skills or a non-interactive orchestration command.

Supersedes:

None.
