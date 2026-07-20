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

## Current Decision Index

WDD-20260709-015 through WDD-20260709-019, WDD-20260710-001 through
WDD-20260710-002, WDD-20260711-001 through WDD-20260711-002, and
WDD-20260716-001 govern the current audit-context, obstruction, skill-context,
lifecycle, scout, durable read-only-report, model-routing, proof-completion,
and worker-prompt-readiness policies. WDD-20260719-011 governs current-cost
claim enforcement and default-sensitive design classification;
WDD-20260719-012 governs neutral-path shadowing in those classifiers. Earlier
entries retain stable IDs and historical insertion order; read their Status
rather than inferring current priority from file order.

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

## WDD-20260709-014: Name The Worker Skill In Delegation Prompts

Status: Accepted
Date: 2026-07-09
Scope: Worker prompt protocol and skill routing.

Decision:

Coordinator-issued worker prompts should explicitly name the RMQ skill the
worker should use before starting. For narrow Lean proof, construction,
cost/space, executable-validation, or theorem-surface implementation work, the
default is `$rmq-proof-sprint`; other skills should be named only when the
coordinator intentionally routes the task elsewhere.

Context:

Workers may sometimes infer the right skill from the repository context, but
that is weaker than making the role contract explicit. The proof-sprint skill
contains current proof discipline, verification expectations, and
design-decision reporting norms; relying on spontaneous skill selection risks
workers missing the latest workflow rules.

Options considered:

- Let workers choose skills implicitly from task context.
- Put skill recommendations only in coordinator-facing launch metadata.
- Put the assigned skill directly in the worker prompt while keeping model/mode
  recommendations outside the prompt.

Rationale:

The skill is part of the worker's process contract, unlike model/mode choice,
which remains user-facing launch metadata. Naming the skill in the pasted
prompt makes design-log and verification discipline more reliable without
making model identity part of the proof trust base.

Consequences:

`docs/internal/templates/WORKER_PROMPT.md` now includes a skill section, and
`rmq-coordinator` must fill it when engineering worker prompts. Completed-worker
audits should note when a worker made a real design decision without updating
the appropriate design ledger.

Evidence:

- `docs/internal/templates/WORKER_PROMPT.md`
- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`

Follow-up:

After a few more worker launches, check whether a dedicated `$rmq-worker` skill
would be useful or whether `$rmq-proof-sprint` plus explicit skill routing is
enough.

Supersedes:

None.

## WDD-20260709-013: Keep Claim-Drift Status Labels Current With Public Cost Moves

Status: Accepted
Date: 2026-07-09
Scope: Claim-drift policy maintenance.

Decision:

When a checked public cost constant changes, update the claim-drift policy
status labels that explain compatibility-only constants, even if the scanned
pattern itself is unchanged.

Context:

The all-size clean RMQ bound moved from `65585` to `4144`, while the legacy
aggregate pattern `196727` remains compatibility-only. Leaving the policy status
label tied to the old route-split value would make scan output stale despite
the checker still passing.

Options considered:

- Leave policy labels as historical hints.
- Update only public prose.
- Keep policy labels synchronized with current public theorem constants.

Rationale:

The scan is an audit aid. Its labels should summarize the current theorem
surface, not require auditors to know which historical bound the label came
from.

Consequences:

Future public cost moves should update `docs/internal/CLAIM_DRIFT_POLICY.*`
alongside theorem maps and artifact claims.

Evidence:

- `docs/internal/CLAIM_DRIFT_POLICY.md`
- `docs/internal/CLAIM_DRIFT_POLICY.json`
- `scripts/claim_drift_scan.ps1`

Follow-up:

Consider adding the current clean all-size constant itself as a policy term if
stale cost numbers continue to recur in non-historical docs.

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
- `.agents/skills/rmq-audit-prompt/SKILL.md` (renamed from `rmq-audit` by
  WDD-20260718-003)
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
- `.agents/skills/rmq-audit-prompt/SKILL.md`
- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `docs/internal/templates/AUDIT_PROMPT.md`

Follow-up:

Completed by WDD-20260718-003: rename the skill to `rmq-audit-prompt` so the
prompt-authoring boundary is explicit without the longer proposed name.

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

Hardening (2026-07-13): after a worker left its automatically generated title
unchanged, the template now begins with the imperative `Make the title of this
chat exactly: ...`. The coordinator skill requires that sentence as the first
line; title metadata alone is insufficient.

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

`docs/internal/AUDIT_PROTOCOL.md`, `.agents/skills/rmq-audit-prompt/SKILL.md`, and
`docs/internal/templates/AUDIT_PROMPT.md` now require or request a durable
report path for material audits. The first stored report is
`docs/internal/audit_reports/2026-07-09_A01_rmq_frontier_audit.md`.

Evidence:

- `docs/internal/AUDIT_PROTOCOL.md`
- `.agents/skills/rmq-audit-prompt/SKILL.md`
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

Status: Fulfilled; retained as sequencing rationale
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

The coordinator and external-audit skills are now landed. Continue with the
structured read-only automation and evidence-manifest steps in
`ADD_WORKFLOW_TOOLING_PLAN.md` rather than creating a duplicate worker skill.

Supersedes:

None.
## WDD-20260709-015: Use Low-History High-Evidence External Audits

Status: Accepted
Date: 2026-07-09
Scope: External auditor context and independence.

Decision:

Use fresh blind sessions for independent milestone gates, the same session for
one correction loop, persistent sessions for periodic longitudinal architecture
review, and a fresh session again for final acceptance. Fresh auditors receive
exact base/target commits, a bounded audit packet, design intent, load-bearing
surfaces, and acceptance criteria, but not previous verdicts or full
transcripts.

Context:

A persistent auditor saves rereading tokens but accumulates framing and
confirmation bias. A context-free auditor is independent but may waste effort
rediscovering source facts.

Options considered:

- Reuse one primary auditor for every gate.
- Start every audit with only a commit hash.
- Separate blind-delta, continuation, longitudinal, and whole-frontier modes.

Rationale:

Low history preserves independence; high evidence prevents whole-repo
rediscovery. A commit alone does not express scope or intended design.

Consequences:

Audit prompts must state mode. Continuation audits are efficient correction
checks but never the sole final gate.

Evidence:

- `docs/internal/AUDIT_PROTOCOL.md`
- `docs/internal/templates/AUDIT_PROMPT.md`

Follow-up:

Measure token use and missed findings across several blind/continuation pairs.

Supersedes:

None.

## WDD-20260709-016: Replace Numeric Attempt Quotas With Obstruction Dossiers

Status: Accepted
Date: 2026-07-09
Scope: Proof-worker stop conditions.

Decision:

Remove the fixed fifty-attempt exhaustion rule. A short-of-target stop requires
a closed target, a minimal formal obstruction, an external blocker, or an
obstruction dossier covering materially distinct construction families and the
coordinator-level choice now required.

Context:

Counting attempts rewards repetition and is difficult to audit. One precise
counterexample can be stronger than many minor proof variants.

Options considered:

- Keep the numeric quota.
- Let workers stop after any reported difficulty.
- Require evidence classified by distinct construction family and structural
  failure.

Rationale:

The dossier tests information gained and design consequence, not persistence
theater. It preserves the anti-premature-stop norm without wasting tokens.

Consequences:

Normative autonomy, orchestration, checklist, and proof-sprint guidance now use
the dossier.

Evidence:

- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`
- `docs/internal/CODEX_AUTONOMY.md`

Follow-up:

Audit the first real obstruction dossier against this standard.

Supersedes:

The fixed-count stop language in the previous proof-sprint/autonomy documents.

## WDD-20260709-017: Keep Skills Thin And Load History On Demand

Status: Accepted
Date: 2026-07-09
Scope: Skill context and token discipline.

Decision:

Skills contain the operating contract and routing rules. The roadmap, audit
protocol, and ledgers remain source documents. Historical proof traps move to
task-specific references loaded only when relevant.

Context:

The proof-sprint skill had grown into a long duplicate of historical C1/C2
planning and stop policy. Every worker paid that context cost regardless of
task.

Options considered:

- Keep all history in the skill.
- Remove historical guidance entirely.
- Keep a concise skill with an on-demand failure-mode reference.

Rationale:

This preserves hard-won constraints while reducing stale duplication and token
load. It also makes policy ownership clear.

Consequences:

Worker prompts request only task-specific context. Updating one source of truth
is preferred to synchronizing repeated prose.

Evidence:

- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`
- `docs/internal/templates/WORKER_PROMPT.md`

Follow-up:

Apply the same compression test to coordinator/audit skills after two more
cycles.

Supersedes:

None.

## WDD-20260709-018: Treat Worktree Retirement As Part Of Task Completion

Status: Accepted
Date: 2026-07-09
Scope: Worker branch and worktree lifecycle.

Decision:

Track tasks from planned through submitted, audited, integrated/rejected/ported,
archived, and retired. Integration alone is not operational completion.
Coordinator-owned cleanup happens only after evidence is preserved and a
dry-run confirms no uncommitted work would be lost.

Context:

The repository has accumulated many worktrees and branches because creation and
integration were governed but retirement was not.

Options considered:

- Keep all worktrees indefinitely.
- Automatically delete them after merge.
- Add explicit lifecycle states and cautious coordinator retirement.

Rationale:

Explicit retirement reduces coordination cost without risking destructive loss.
Milestone and evidence branches can still be retained deliberately.

Consequences:

Completion reports request a lifecycle disposition. Destructive cleanup remains
manual/approved.

Evidence:

- `docs/internal/WORKER_LIFECYCLE.md`
- `docs/internal/WORKER_INTEGRATION_CHECKLIST.md`

Follow-up:

Produce a read-only inventory and retirement proposal for existing worktrees;
do not bulk-delete as part of this consolidation.

Supersedes:

None.

## WDD-20260709-019: Join Read-Only Architecture Scouts Before Shared Implementation

Status: Accepted
Date: 2026-07-09
Scope: Final-roadmap delegation order.

Decision:

Run declaration-closure, total-parameter, and naming/module scouts in parallel
against one exact frontier. The coordinator synthesizes their reports into one
approved interface before assigning the total-parameter implementation.

Context:

The next technical step changes a shared abstraction used by routing, payload,
and cost proofs. Parallel implementation would create competing root records
and theorem signatures.

Options considered:

- Assign one implementation worker immediately.
- Run three implementation experiments.
- Parallelize independent read-only evidence/design leaves, then give the joined
  abstraction one owner.

Rationale:

This maximizes effective parallelism while respecting causal ownership.

Consequences:

The scouts do not edit source or make competing branches. Their output is
consolidated before `U1`.

Evidence:

- `docs/internal/RMQ_FINAL_ROADMAP.md`
- `docs/internal/CODEX_ORCHESTRATION.md`

Follow-up:

Launch the three scouts against the consolidation commit.

Supersedes:

None.
## WDD-20260710-001: Make Material Read-Only Scout Results Durable

Status: Accepted
Date: 2026-07-10
Scope: Read-only worker evidence and task recovery.

Decision:

A material read-only scout must either write one assigned report-only file or be
incorporated promptly into a durable coordinator synthesis. Chat/task history
alone is not the project record.

Context:

The W12 total-parameter scout completed successfully, but its task became
unopenable in the desktop UI and displayed "Content not found." The task-history
API still exposed the completed turn, so the coordinator recovered and audited
it. Without that recovery path, a critical architecture decision would have
been stranded in transient UI state.

Options considered:

- Treat chat history as sufficient.
- Require every scout to create its own report branch.
- Permit report-only output or immediate coordinator synthesis, depending on
  task size and concurrency.

Rationale:

Durable source-grounded synthesis prevents UI/session corruption from losing
design evidence without creating a branch for every small read-only task. It
also keeps raw transcripts out of the public artifact.

Consequences:

Coordinator prompts for material scouts should name the intended durable
disposition. The coordinator closes the lifecycle only after the report is
stored or incorporated. Duplicate/corrupted task entries are process failures,
not reasons to rerun completed source analysis automatically.

Evidence:

- `docs/internal/RELATIVE_RMM_LAYOUT_DESIGN.md`
- `docs/internal/RMQ_DECLARATION_CLOSURE_2026_07_10.md`
- `docs/internal/WORKER_LIFECYCLE.md`

Follow-up:

The worker template now carries the durable report/synthesis disposition.
Evaluate whether the later audit-packet generator should enforce that field for
material read-only tasks.

Supersedes:

None.

## WDD-20260710-002: Name The Exact Model Variant In Launch Recommendations

Status: Accepted
Date: 2026-07-10
Scope: Coordinator model routing and token-conscious delegation.

Decision:

Every coordinator launch recommendation must name the exact model variant,
reasoning level, and speed/service mode outside the worker prompt. A family-only
label such as `5.6` is insufficient.

Default routing is:

- `GPT-5.6 Sol, Extra High, Fast` for nontrivial Lean proofs, architecture,
  integration, or adversarial audits;
- `GPT-5.6 Terra` with a task-appropriate reasoning level for bounded,
  lower-risk engineering, documentation, or tooling work;
- `GPT-5.6 Luna` only for mechanical, low-risk scans, formatting, inventory, or
  status tasks whose outputs are independently checked.

Context:

The 5.6 family contains materially different variants. Saying only `5.6` leaves
the user unable to reproduce the coordinator's quality/cost choice or evaluate
which lower-tier delegation experiments succeed.

Options considered:

- Continue naming only the model family and reasoning mode.
- Use Sol for every task.
- Name the exact variant and route by proof risk, coupling, and audit burden.

Rationale:

Explicit variant recommendations make delegation reproducible and permit
careful token/cost experiments without silently lowering the quality floor for
load-bearing proof work. Keeping this metadata outside worker prompts avoids
spending worker context on coordinator resource policy.

Consequences:

Coordinator reports must state the variant, reasoning level, speed/service
mode, fresh-versus-existing worker choice, and reason. Deviations from the
default routing should be explained and later compared using verification and
audit outcomes rather than subjective impressions alone.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/templates/WORKER_PROMPT.md`
- WDD-20260708-007 and WDD-20260709-009

Follow-up:

Record enough launch/outcome metadata to evaluate whether Terra or Luna can
replace Sol for recurring low-risk ADD tasks without increasing rework.

Supersedes:

The underspecified model-family wording in WDD-20260708-007 and WDD-20260709-009;
their requirement to keep launch metadata outside worker prompts remains active.

## WDD-20260711-001: Make Proof Completion Evidence-Gated

Status: Accepted
Date: 2026-07-11
Scope: Proof-worker completion, coordinator integration, and external audit.

Decision:

A nontrivial proof or representation worker may declare completion only after a
requirement-to-evidence matrix closes every explicit prompt requirement, named
downstream consumer, applicable inherited RMQ invariant, and requested check.
The proof-sprint skill owns a mandatory completion gate; worker prompts,
coordinator integration, and external audits independently apply the same
contract.

The inherited gate includes counted-store provenance, dependency of returned
values on charged reads, execution-derived traces and footprints,
supplied-store agreement, successful-read backing, machine-width words,
machine-width addresses and operands, all assigned edge cases, and the absence
of proof-only answers, decorative reads, and hidden regime dispatch.

Context:

Recent uniform-directory work produced mathematically useful checkpoints with
green builds and candid self-audits. One checkpoint still obtained a logical
cell before replaying charged reads; a repair established real per-table reads
but identified an open composed-footprint obligation; the next repair closed
that footprint but missed the inherited machine-address-capacity condition on
tiny instances. The reports were honest, yet the workers treated local rungs
or commits as completion even when their own caveats named work required by the
assigned consumer.

This exposed a workflow ambiguity: the existing rule that a green build is not
closure did not force workers to preserve the full acceptance contract across
local proof steps or to distinguish a useful submitted checkpoint from a
completed target.

Options considered:

- Trust worker completion reports and rely on occasional external audits.
- Leave completion discipline entirely to the coordinator's post hoc review.
- Add more target-specific prose to every proof prompt.
- Define one reusable evidence gate, require prompts to instantiate it, and
  require coordinators and auditors to reconstruct it independently.

Rationale:

A reusable matrix prevents the target from shrinking as implementation details
accumulate. Inherited invariants keep architectural obligations live even when
a prompt author forgets to repeat them. Independent reconstruction by the
coordinator and auditor limits self-confirming interpretations.

The gate also improves paper exposition. It preserves a traceable connection
from each implementation decision to the reviewer-facing claims it supports:
where answers come from, which storage is counted, how execution footprints are
formed, and why machine bounds cover all cases.

Consequences:

A commit, push, green build, local helper, or candid remaining-risk paragraph
is a checkpoint, not completion. If a post-commit self-audit finds a locally
repairable unmet criterion, the same worker continues on the same branch and
adds another commit. A submitted branch remains one lifecycle task until the
owned target closes, is formally obstructed, is externally blocked, or is
explicitly redirected.

Completion reports must include the matrix, one controlled status, and the
exact declaration `No assigned or inherited acceptance criterion remains
unmet` for `COMPLETE`. Machine/layout work must test tiny and threshold cases,
trace returned values backward to charged reads, and prove actual footprint
addresses, including dead/sentinel addresses, fit modeled capacity.

Evidence:

- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`
- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `docs/internal/templates/WORKER_PROMPT.md`
- `docs/internal/WORKER_INTEGRATION_CHECKLIST.md`
- `docs/internal/templates/AUDIT_PROMPT.md`
- `docs/internal/WORKER_LIFECYCLE.md`

Follow-up:

Apply the gate to the next same-worker uniform-directory repair. After two proof
cycles, audit whether the matrix catches omissions before commit and whether
any invariant needs a more theorem-specific checklist.

Supersedes:

No earlier decision. It strengthens WDD-20260709-016's stop conditions and
WDD-20260709-017's thin-skill policy by placing detailed completion rules in a
required on-demand reference.

## WDD-20260711-002: Separate Local-Rung Closure From Roadmap Closure

Status: Accepted
Date: 2026-07-11
Scope: Coordinator frontier tracking, worker bases, and delegation prompts.

Decision:

Coordinators must track two completion states independently:

- whether the worker's exact local rung is closed;
- whether the larger roadmap node and its named downstream consumer are closed.

Every worker prompt names both states and says which one the assignment owns.
A local prerequisite may be reported complete without implying that its roadmap
node is complete. Roadmap status changes only after coordinator integration and
consumer-level verification.

Before launch, the coordinator also verifies that the worker's exact base
contains the current workflow skills and prompt policy. When proof and workflow
changes are sibling branches, the coordinator creates an explicit integration
base or requires the worker to merge the named workflow commit before invoking
the skill.

Context:

The machine-backed uniform-directory campaign produced several valuable local
rungs: the uniform directory, the per-component machine store, and the composed
range-store footprint. Those rungs materially advance U2, but the final
close/LCA reviewer path still consumes the legacy three-way interior route and
the old zero-block path remains live. Calling a local rung complete and calling
U2 complete are therefore different statements.

At the same time, the completion-gate policy landed on a sibling branch rather
than the current U2 proof branch. A prompt that merely says to use the latest
skill is ineffective if the checkout does not contain that skill version.

Options considered:

- Use only roadmap-node-sized assignments.
- Let workers use "complete" informally and rely on prose context.
- Track local and roadmap closure separately but leave branch policy implicit.
- Track both statuses explicitly and require the worker base to contain the
  governing workflow policy.

Rationale:

Some proof campaigns are causally too large for one safe write assignment, so
local rungs remain useful. Explicit dual status preserves that granularity
without allowing checkpoint language to drift into a public frontier claim.

Joining workflow policy into the worker base makes the process contract
reproducible. It also leaves a publication-friendly history: the project can
explain which intermediate abstractions were established, which consumer made
them meaningful, and when the larger theorem architecture actually changed.

Consequences:

Coordinator reports and integration checklists distinguish local-rung and
roadmap-node status. Worker prompts identify the downstream closure condition
even when the current task owns only a prerequisite. A worker cannot infer
policy from a sibling branch or chat description; the policy commit must be in
the checkout it uses.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/templates/WORKER_PROMPT.md`
- `docs/internal/WORKER_INTEGRATION_CHECKLIST.md`
- sibling frontiers `8c92a4a` and `856fb74` above common base `0c5d422`

Follow-up:

Use the dual-status fields for the next U2 addressability repair and the
subsequent final-route migration. Mark U2 complete only after the canonical
directory is consumed by the reviewer close/LCA path and the zero-block route
is no longer reachable there.

Supersedes:

No earlier decision. It operationalizes WDD-20260711-001 without weakening its
completion standard.

## WDD-20260712-001: Separate Worker Candidate Completion From Acceptance

Status: Accepted
Date: 2026-07-12
Scope: Proof-worker evidence, coordinator acceptance, external audit, and
paper-capstone integration.

Decision:

Workers freeze stable acceptance IDs and verbatim requirements before editing,
then report only `CANDIDATE_COMPLETE`. Matrix evidence must quote checked
theorem conclusions and show the identity/composition chain to the named
consumer; declaration names alone do not close rows. Only the coordinator may
record `ACCEPTED` after independently reconstructing the matrix from source.

Public paper capstones, trust-boundary changes, combined space/execution
theorems, and roadmap-node closures additionally require a fresh blind audit of
the exact candidate commit before acceptance or merge. Fresh auditors receive
the frozen contract, but not the worker verdict or narrative.

Context:

The U2 final-route worker produced substantial correct work and a polished
completion matrix, but selected nearby theorem names as evidence for stronger
requirements. The public space theorem still counted a different payload from
the executed canonical reviewer payload; the physical embedding covered only
the interior suffix; and the advertised word-model theorem did not relate the
chosen capacity to input size. Stale claim-drift policy also allowed stale
public constants to pass the scan. The worker nevertheless declared U2 closed
and stated that no acceptance criterion remained.

Options considered:

- Add another prose warning while retaining worker self-certification.
- Require more theorem names in the completion report.
- Keep mutable matrix requirements and rely on post hoc coordinator review.
- Freeze exact acceptance IDs, require conclusion-level and object-identity
  evidence, make worker completion provisional, and use a two-person gate for
  public milestones.

Rationale:

The failure was semantic entailment, not honesty or build hygiene. Stable
requirements prevent target shrinkage. Quoted theorem conclusions expose weak
evidence. Explicit identity chains catch true statements about sibling
payloads that do not compose into the public claim. Provisional worker status
and blind milestone review prevent the implementer's narrative from becoming
the acceptance standard.

This structure also makes paper exposition easier: each public claim has a
recoverable chain from construction identity through storage, execution, word
model, and theorem statement, with rejected alternatives and audit evidence.

Consequences:

Worker prompts assign applicable invariant IDs. The proof-sprint gate and
matrix template require exact propositions, consumers, falsifiers, and residual
gaps. Coordinators inspect theorem types and definitions, audit claim-scan
policies themselves, and reserve `ACCEPTED` for their verdict. External audit
cost rises for public milestones but not for ordinary isolated leaves.

Evidence:

- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`
- `.agents/skills/rmq-coordinator/SKILL.md`
- `docs/internal/WORKER_INTEGRATION_CHECKLIST.md`
- `docs/internal/templates/AUDIT_PROMPT.md`
- `docs/internal/AUDIT_PROTOCOL.md`
- U2 candidate commits `b8ae4aa` and `ba49ae9`

Follow-up:

Apply this contract to the same-worker U2 repair. After that branch reaches
candidate completion, run a fresh blind exact-commit audit before accepting U2
or starting U3. Evaluate after two public milestones whether any invariant IDs
need splitting or automation.

Supersedes:

It strengthens WDD-20260711-001 and WDD-20260711-002. Their evidence-gating,
dual-status, and current-policy-base requirements remain active.

## WDD-20260713-001: Require Counterfactual Semantic Closure Evidence

Status: Accepted
Date: 2026-07-13
Scope: Proof-worker completion, coordinator reconstruction, external audits,
and publication-facing evidence for semantic coverage claims.

Decision:

Semantic liveness, coverage, ownership, dependency, refinement, and public
composition rows now require counterfactual evidence in addition to theorem
types and green gates. The worker, coordinator, and auditor expand the
load-bearing definitions and identify which checked theorem rejects applicable
mutations: adding a dead manifest source, removing an operationally used
source, assigning a consumer label without an evaluator edge, replacing a
semantic predicate by a tautology, ignoring a returned read value, or mixing
guarded and unguarded executions.

Bundled requirements receive one attempted mutation per applicable semantic
subclaim. Projection-specific evidence must match the public claim's
quantification and validity domain: a singleton corruption witness cannot prove
universal dependency, and a valid-range bridge cannot justify unconditional raw
adequacy inside an otherwise guarded all-input record.

Returned-value and routing requirements must be supported at the relevant
projection; inequality of an aggregate trace record is insufficient when its
log alone forces the inequality. Public wrappers with validity guards must use
one execution domain across result, trace, cost, footprint, and adequacy fields,
or provide a checked equivalence under the valid-range premise and an explicit
invalid-input semantics.

Worker candidate reports must begin with the exact provisional status and
declaration. Informal substitutes such as "closed at worker/gate level",
"complete", or "merge-ready" are protocol failures and are treated as
`INCOMPLETE`. The durable acceptance matrix records anti-vacuity challenges
actually attempted and their outcomes, not merely plausible falsifiers.

Context:

The W17 U2 candidate at `9d19613` made substantial genuine progress: one
counted/executed payload, a real supplied-store adapter, physical footprints,
whole-query width bounds, and a uniform reviewer route. Its report nevertheless
declared worker/gate closure from a declaration-name inventory. In source,
`ReviewerSource.Live` was definitionally `True`; consumer ownership came from a
second hand-written table rather than evaluator reachability; a store
corruption theorem could differ only through its logged read; and the public
list packet combined guarded result fields with an unguarded raw adequacy
packet on invalid ranges. CI, artifact reproduction, axiom inventories, and
claim scans all passed because these were semantic entailment failures rather
than compilation or trust failures.

Options considered:

- Rely on the mandatory blind audit to catch such defects after every worker.
- Add more theorem names and executable examples to completion reports.
- Ban particular definitions such as `Live := True` globally.
- Require definition expansion, projection-specific evidence, and targeted
  counterfactual mutations at worker, coordinator, and auditor gates.

Rationale:

Blind audit remains necessary for public milestones but should validate a real
candidate, not perform the implementer's missing semantic self-audit. More
theorem names reproduce the same failure, while a global syntactic ban would
reject legitimate propositions that happen to be universally true. A
counterfactual challenge tests the intended meaning directly: an exact live
manifest should reject a dead source, a consumer theorem should reject a forged
label, and value dependency should fail when the decisive read is ignored.

This evidence is also paper-friendly. It exposes why the formal definitions
capture the operational concepts used in the exposition, records the boundary
between traces and returned values, and gives reviewers compact falsification
tests instead of asking them to infer non-vacuity from a large theorem stack.

Consequences:

The proof-sprint gate and worker matrix are slightly more demanding for
semantic rows, but ordinary arithmetic or local helper proofs are unaffected.
Coordinator and external-audit passes gain explicit mutation checks. Exact
status syntax prevents polished prose from blurring provisional worker status
with coordinator acceptance. Green build and CI evidence remain necessary but
are explicitly lower-tier than semantic closure evidence.

Evidence:

- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`
- `.agents/skills/rmq-proof-sprint/SKILL.md`
- `.agents/skills/rmq-coordinator/SKILL.md`
- `.agents/skills/rmq-audit-prompt/SKILL.md`
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`
- `docs/internal/templates/WORKER_PROMPT.md`
- `docs/internal/templates/AUDIT_PROMPT.md`
- `docs/internal/WORKER_INTEGRATION_CHECKLIST.md`
- `docs/internal/AUDIT_PROTOCOL.md`
- `docs/internal/WORKER_LIFECYCLE.md`
- W17 candidate commit `9d19613`

Follow-up:

Apply the revised gate to the same-worker W17 repair. A fresh blind auditor of
the repaired exact commit must independently repeat the applicable mutations
before the coordinator records U2 `ACCEPTED`. Because W17's original frozen
matrix predates `INV-SEMANTIC-NONVACUITY`, its repair prompt must record an
explicit coordinator-approved contract amendment adding that row and reopening
the bundled manifest, value-dependency, and public-composition rows. After two
semantic-capstone cycles, assess whether a lightweight structured-report linter
would prevent status or matrix-format drift without pretending to automate
semantic review.

Supersedes:

It strengthens WDD-20260712-001. Frozen requirements, provisional worker
status, coordinator reconstruction, and mandatory blind public-capstone audit
remain active.

## WDD-20260713-002: Require occurrence-level evidence for producer provenance

Status: accepted workflow clarification for the W18 repair.

Decision:

When a public acceptance row claims that a trace event was produced by a
program instruction, its evidence must retain the same event in that actual
instruction occurrence's local trace at the actual state obtained from the
program prefix.  Separately true source-map, leaf-category, instruction-list,
or arbitrary-state evaluator facts may remain compatibility evidence, but they
cannot close producer provenance.

Reverse source liveness must exhibit a concrete possible read path in the
construction.  For shared storage, the source and named consumer must be tied
through one event/path witness.  Counterfactual sources with plausible existing
labels must be rejected by the same operational relation used for accepted
sources, not by assigning them a false or unlisted liveness predicate.

Context:

The W17 semantic repair passed its build, mutation, and axiom gates but its
emitted-read theorem classified the segment with a functional leaf map and
then selected an arbitrary instruction with that category.  The selected
instruction need not have emitted the event, and `WholeQueryState.empty` is
not the pre-state of later LCA/rank instructions.  Its shared-BP evidence could
also combine a source witness from segment `0` with an unrelated leaf witness
from segment `20`.

Options considered:

- Keep category joins and explain their intended operational reading in prose.
- Add another label-consistency mutation to the W17 gate.
- Require actual occurrence/state/event and same-event source/path witnesses.

Rationale:

The first two options cannot distinguish a correctly labeled nonproducer from
the instruction that actually emitted an event.  Occurrence-level trace
decomposition mirrors evaluator composition and is therefore stable under
later program-state dependencies.  A relational path is necessary because
one logical segment can be consumed by multiple instruction families.

Consequences:

- W17's `REQ-02.a`, `REQ-02.b`, `INV-SEMANTIC-NONVACUITY`, and dependent public
  rows are recorded as `REPAIR_REQUIRED`; W18 evidence is a superseding matrix
  section rather than a silent reinterpretation of the old green ledger.
- Claim policy and reviewer docs reserve “producer provenance” for the
  same-event actual-state relation.
- Category-only declarations may stay for compatibility but are removed from
  the load-bearing headline and axiom surface.
- Worker status remains candidate-only pending coordinator reconstruction and
  a fresh blind exact-commit audit.

Evidence:

- `docs/internal/W15_U2_CANONICAL_PAYLOAD_WHOLE_MACHINE_ACCEPTANCE_MATRIX.md`
- `docs/internal/DESIGN_DECISIONS.md`, DD-20260713-003
- `docs/internal/CLAIM_DRIFT_POLICY.md`
- `RMQ/Core/SuccinctFinalRAM.lean`
- `RMQ/Core/SuccinctFinalModelAdequacy.lean`
- `RMQ/Headlines/RMQ.lean`

## WDD-20260713-003: predicate-identical counterfactuals and failure-mode feedback

Status: accepted.
Date: 2026-07-13.
Scope: proof-worker completion, coordinator integration, external audits,
claim-drift checks, and publication-facing ADD evidence.

Decision:

- Every semantic counterfactual records the accepted predicate `P`, rejected
  predicate `Q`, and their guards and quantifiers. Closure requires the same
  predicate or a checked `P -> Q` bridge.
- Provenance evidence is labeled by the information retained in its theorem
  conclusion: event value, occurrence position, multiplicity, producing
  instruction, folded pre-state, local occurrence, and invocation parameters.
  Data used while building a proof but erased from the proposition does not
  support the stronger label.
- Workers cannot unilaterally call a residual skeptical question "strictly
  stronger", future hardening, or out of scope. They map it to the frozen
  requirements and inherited invariants; only the coordinator may amend the
  contract.
- Every coordinator worker audit now includes a failure-mode feedback loop.
  The coordinator names the gap, decides whether it is isolated or reusable,
  patches the smallest appropriate workflow layer when generalizable, records
  the decision, uses the failed candidate as a regression fixture, and only
  then engineers the next worker prompts.

Context:

W18 commit `63d503d24aadeb501284a658c303bf69861953df`
reported candidate completion after materially improving W17. Its accepted
source theorem used direct component `HasProducerMayPath`, while its fresh-
source mutation rejected the stronger `HasOperationalProducer`; no bridge
connected them. The forward provenance theorem began from `List.Mem` and the
public path record erased invocation parameters, despite prose claiming an
actual occurrence and invocation. The worker disclosed top-level reachability
as a possible stronger future theorem, but that question fell inside the
frozen operational-provenance and semantic-nonvacuity criteria.

Options considered:

- Treat W18 as an isolated proof bug and repair only its Lean definitions.
- Add task-specific prose to the next worker prompt.
- Require blind auditors to discover predicate mismatch after every milestone.
- Add predicate parity and information-preservation checks to the shared
  worker, coordinator, auditor, matrix, and claim-policy layers, with a
  standard coordinator feedback loop for future recurring failures.

Rationale:

Counterfactual evidence is useful only when it challenges the property being
accepted. A stronger negative relation can reject a mutation while leaving the
weaker positive relation vacuous or operationally irrelevant. Likewise,
occurrence-level prose is not entailed by event-value membership. Making these
comparisons explicit is a small, reusable check that would have rejected the
W18 report before public-capstone review.

The coordinator feedback loop prevents the process from repeatedly paying for
the same class of failure. Restricting workflow patches to recurring or
generalizable misses avoids turning ordinary proof bugs into permanent process
overhead.

Publication-facing significance:

The decision log now preserves why the formal notion of producer provenance
was strengthened and how ADD responds when a machine-checked theorem satisfies
the words of a requirement but loses its intended operational information.
This supports a methods section that explains falsification tests, evidence
levels, and workflow evolution without relying on chat transcripts.

Consequences:

- Proof-sprint, completion-gate, known-failure, matrix, worker-prompt,
  coordinator, audit, and audit-prompt guidance share the same predicate and
  provenance checks.
- W18 is a named workflow regression fixture.
- Claim-drift policy rejects stale current-facing W17 and category-only source
  stories while W19 is pending.
- The checks add no burden to ordinary local arithmetic proofs and do not make
  automated scans a substitute for semantic reconstruction.

Evidence:

- `.agents/skills/rmq-proof-sprint/SKILL.md`.
- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`.
- `.agents/skills/rmq-coordinator/SKILL.md`.
- `.agents/skills/rmq-audit-prompt/SKILL.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
- `docs/internal/templates/AUDIT_PROMPT.md`.
- `docs/internal/CLAIM_DRIFT_POLICY.md` and `.json`.
- W18 commit `63d503d24aadeb501284a658c303bf69861953df`.

Follow-up:

Apply the revised contract to W19, then give a fresh blind auditor the exact
commit and frozen predicates without the worker narrative. After two more
public-capstone cycles, evaluate whether structured extraction of `P`, `Q`,
domains, and provenance level from acceptance matrices is worth automating.

## WDD-20260713-004: W19 applies the predicate-parity gate

Status: Accepted after coordinator reconstruction and the A04 blind audit of
exact U2 target `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`.
Date: 2026-07-13; amended 2026-07-14.

Decision:

- Record positive predicate `P`, mutation predicate `Q`, their common claim
  domain, result quantifiers, and the checked `P -> Q` bridge in the amended
  acceptance matrix.
- Require global and local indices, the instruction occurrence, prefix-folded
  state, invocation parameters, and the composed-trace offset in the
  load-bearing provenance proposition.
- Require reverse witnesses to finish at a successful event in an actual
  closed valid whole-query execution. Component may-read and arbitrary-state
  instruction traces remain named compatibility evidence, not completion.
- Keep the repeated-equal-event singleton as an executable regression and the
  generic two-position receipt theorem as kernel evidence.

Outcome:

The W19 candidate exercises the workflow checks introduced after W18 rather
than satisfying them in prose. The long-super and sparse-local witness
arithmetic is proved symbolically in Lean. The scout report at commit
`17287f25d1241ab6e4609f19863eced66dd9e62b` informed proof order only; it was
not counted as evidence and its erroneous prose source summary was corrected
from its table. The next workflow consumer is a coordinator reconstruction and
blind exact-commit audit. U3 remains gated on U2 acceptance.

## WDD-20260713-005: gate global liveness separately from query provenance

Status: Accepted after coordinator reconstruction and the A04 blind audit of
exact U2 target `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`.
Date: 2026-07-13.

Decision:

- Curated axiom inventories name one query-independent reviewer-manifest packet
  and the existing valid-query raw/occurrence surfaces. They no longer print
  wrappers whose `xs`, bounds, and `ValidRange` premises were unused by a
  global existential conclusion.
- Claim drift classifies `2^128` by role: explicit legacy compatibility premise
  or W19 proof-only sparse-local witness, never current canonical execution
  activation. The scanner now recognizes both spaced and unspaced notation and
  rejects ordinary canonical-activation wording in both directions: a canonical
  execution/route/query may name `2^128` as its activation premise, or the
  exponent may name the canonical consumer that it activates.
- The liveness policy status explicitly says `global-existential-some-valid-
  query-not-current-query`, while indexed occurrence policy remains tied to the
  current trace.
- Verification continues to run both native executables from their direct
  `SuccinctRMQClassic` roots. Importing the proof-only provenance seam into an
  executable root remains prohibited because it would link symbolic witness
  construction.

Outcome:

The completion gate now checks the theorem's real quantifier boundary rather
than accepting vacuous current-query parameters. The three primary axiom
inventories expose both scopes, strict claim scanning recognizes the proof-only
`N = 2^128` witness, and the genuine native execution closure is unchanged.

Failure discovered after the accepted composition checkpoint:

Policy version 7 passed its strict scan while failing the natural subject-first
canonical-activation mutation recorded in the regression script. Its first
alternative required `activation premise` before the exponent, so it checked a
stilted word order rather than the prohibited claim itself.

Rejected alternatives:

- Add only that one sentence to a test fixture; this would leave `requires`,
  `has`, exponent-first wording, and spaced notation unprotected.
- Broaden the strict rule without negative-role fixtures; this would risk
  rejecting the truthful no-canonical-activation statement, compatibility
  companions, or W19's proof-only sparse-local witness.
- Treat a green repository scan as sufficient; existing prose need not contain
  the misuse that a future edit could introduce.

Regression evidence:

`scripts/claim_drift_policy_regression.ps1`, invoked by `scripts/gate.ps1`,
uses `rg --pcre2` against five must-reject mutations and five must-accept
role-scoped fixtures. It independently exercises both word orders, both
spaced/unspaced exponent spellings, negated canonical claims, compatibility,
and the symbolic sparse-local proof witness.

Second failure discovered at checkpoint `82406d93`:

The first regression asserted only raw forbidden-pattern matches. It did not
exercise the scanner's line/path allowances, term `strict` flag, accumulated
failure count, or exit code. It was therefore fixture-overfit: nearby
possessive, activated-at, and threshold claims still escaped. In addition,
`scripts/gate.ps1` ran only that raw-pattern regression, while CI ran the real
claim scan without `-Strict` in an explicitly advisory step. A forbidden
publication claim could therefore remain gate-green.

Running fixtures through the real scanner exposed a second concrete scope bug:
when `rg` received exactly one file it omitted the filename, but the scanner
parser required `file:line:text`. Ordinary matching lines were silently
dropped; only fixture text containing another colon happened to parse.
`--with-filename` now preserves the scanner's input contract for both focused
and repository-wide scans.

Amended decision:

- The forbidden term is a broad 240-character suspicious-token window over a
  standalone canonical role followed by execution/route/query language and,
  on the same line, `2^128` (spaced or unspaced), plus the then-required
  activation/premise/threshold language. It is intentionally a controlled
  claim-language lint, not a complete natural-language semantic checker.
- Its allowances are anchored, explicit roles: direct negation, historical
  note/record, compatibility companion/history, or proof-only witness. The
  canonical token boundary excludes `noncanonical` and `non-canonical`.
- The regression delegates every fixture to `claim_drift_scan.ps1 -Strict` in
  a child process and asserts the scanner's final exit verdict. Must-accept
  fixtures that exercise an allowance also require the scanner's `[allowed]`
  classification; both exact contract/policy path allowances are exercised
  separately.
- The aggregate gate runs both the focused regression and the full repository
  strict scan. CI gives the same strict scan its own blocking step, so no later
  command can overwrite its exit status, and retains the aggregate gate as an
  independent blocking consumer.

Rejected alternatives:

- Continue appending grammatical alternatives and negative lookarounds to the
  checkpoint regex. This repeats the fixture-overfitting failure and makes the
  accepted roles implicit.
- Reimplement allowance and strictness logic inside the regression. Two
  classifiers could disagree while both local test suites remained green.
- Gate only the focused fixtures. That protects known mutations but permits a
  strict failure already present elsewhere in publication-facing prose.
- Keep CI's scan advisory because the aggregate gate runs the regression. The
  checkpoint showed that raw fixture success and repository strict cleanliness
  are different obligations.

Publication-facing rationale:

The paper and artifact must distinguish a current canonical execution premise
from compatibility theorems and a proof-only symbolic witness. Small prose
reorderings must not silently reactivate the false canonical `2^128` story, but
truthful scoped history must remain writable. A blocking controlled-language
lint makes that boundary reproducible without pretending to solve unrestricted
natural-language semantics.

Amended regression evidence:

- 13 must-reject fixtures receive the forbidden term's final strict failure;
- 11 must-accept fixtures receive a final strict pass, including explicit
  allowance cases that also report `[allowed]`;
- both exact path allowances are exercised through the scanner;
- the full repository strict scan reports 576 classified hits and zero strict
  failures;
- the base-relative strict design check covers eight changed files; and
- `scripts/gate.ps1` completes with `GATE PASS`, while CI names and invokes its
  claim scan as strict.

Third failure discovered at checkpoint `c3c3b51b`:

The previous repair still classified grammatical examples instead of the
policy category. It required a third activation/premise/threshold token, so
ordinary statements such as a requirement, availability condition, or need
could pair the canonical role with the exponent and escape. Its exact
acceptance-matrix path allowance also accepted every matching line in that
file, not just the frozen contract rows that quote rejected examples. Finally,
the scanner still split human-formatted `file:line:text` output at colons. That
made drive-qualified and other colon-bearing paths part of the classifier's
semantics even though the policy was meant to classify line content and
explicit contexts.

Category-level amended decision:

- The production suspicion boundary now has two token classes only: standalone
  canonical execution/route/query language and the spaced or unspaced
  exponent. A bounded line containing both is suspicious regardless of its
  verb or whether it says activation, premise, or threshold.
- Explicit negation and explicit historical, compatibility, and proof-only
  role prefixes remain narrow line allowances. Negative-looking words outside
  those forms do not whitelist a line.
- The policy files retain their exact whole-path allowance. The acceptance
  matrix instead requires both its exact path and an exact frozen `POLICY-01`
  through `POLICY-06` or `POLICY-R1` through `POLICY-R6` table-row marker.
  Filename alone is not an allowance.
- The scanner consumes `rg --json` match records and normalizes absolute paths
  under the repository before matching policy paths. Relative, drive-qualified
  Windows, colon-bearing, and focused single-file inputs use the same parser.
- Mutation sentences are lower bounds. The production-verdict regression now
  adds category-level held-out verbs/orderings, negative and role-prefix bypass
  attempts, an unmarked live acceptance-matrix mutation, and absolute-path
  scans. The shared completion gate, known-failure list, worker prompt, matrix
  template, and proof-sprint skill now require this evidence class.

CI design-decision disposition:

Retain the separate strict design-decision step added before this checkpoint.
It is a blocking workflow invariant: claim-policy, scanner, gate, CI, and
worker-guidance changes must carry a base-relative workflow decision rather
than silently changing publication controls. Pull requests fetch and compare
the target branch; push builds compare `HEAD~1`. The separate `if: always()`
step reports a missing decision even if the broader repository gate fails
first, and its nonzero verdict still fails the job.

Rejected alternatives:

- Add more verbs or word orders to the old three-token detector. That makes
  the known fixtures the architecture and leaves the next unseen verb open.
- Admit the whole acceptance matrix by filename. A future false publication
  claim elsewhere in that durable file would become invisible.
- Copy allowance logic into the regression. Two final-verdict implementations
  could diverge while each test remained green.
- Keep delimiter parsing and special-case a drive prefix. Absolute, relative,
  colon-bearing, and focused inputs would still have separate semantics.
- Revert the CI design-decision step or make it advisory. That would allow a
  publication-control change to land without recording its rationale.
- Fold design-decision checking only into the aggregate gate. The gate has no
  event-specific base selection and would not independently report the process
  failure after an earlier gate error.

Operational and publication-facing consequences:

The lint deliberately over-approximates suspicious prose and relies on narrow,
reviewable role allowances; it remains a controlled claim-language check, not
a natural-language theorem prover. A fresh false canonical premise cannot hide
behind a new verb, the matrix filename, or a Windows drive colon. Truthful
negation, compatibility history, and the proof-only sparse witness remain
writable. Because this boundary protects the paper-facing distinction between
the current route, legacy compatibility, and proof construction, both the
claim verdict and changes to its workflow contract are blocking in CI.

Category-level regression evidence:

- 26 category, grammatical, and allowance-bypass fixtures receive the
  production forbidden term's final strict failure verdict;
- 15 truthful fixtures receive a final strict pass, including 11 suspicious
  lines admitted only by explicit negation or role allowance;
- five path/context verdicts cover the policy path, marked matrix rows,
  drive-qualified absolute input, absolute path normalization, and a fresh
  unmarked matrix-file misuse;
- the repository scan reports 581 classified hits and zero strict failures;
- the base-relative strict design check covers 12 changed files; and
- the full aggregate gate passes on the implementation tree in 243.4 seconds
  and again on the completed-ledger tree in 249.1 seconds, both with
  `GATE PASS`.

The final local/remote candidate SHA remains a post-push lifecycle fact and is
recorded in the acceptance ledger and handoff only after it is observed.

## WDD-20260714-001: certify the submitted audit report tree

Status: Accepted.
Date: 2026-07-14.
Scope: report-only external audits and coordinator acceptance gates.

Decision:

An auditor must rerun report-sensitive checks after the durable report is
written and before committing it. Strict claim drift, applicable strict design
decision checking, and `git diff --check` run on the final report tree. The
coordinator independently verifies the committed report tree before accepting
the audit. Audit-report paths receive no blanket claim-policy allowance.

Context:

A04 correctly audited U2 target `4f7ec8b`, but ran the strict claim scan before
writing its report. The report's stale-objection table then quoted a forbidden
current canonical/`2^128` claim. Commit `f5c2ab0` therefore failed both the
aggregate repository gate and the separate strict scan in CI run
`29354845274`, even though the audited Lean target itself had green CI. The
mathematical verdict remained sound, but the submitted audit artifact was not
gate-clean and the completion response did not preserve that distinction.

Options considered:

- Treat a pre-report gate as sufficient because the report is process evidence.
- Add a broad allowance for `docs/internal/audit_reports/`.
- Rerun report-sensitive checks on the final tree and paraphrase forbidden
  counterexamples unless an existing narrow role allowance is justified.

Rationale:

Audit reports are publication-adjacent provenance and can themselves introduce
claim drift. A blanket path allowance would hide exactly the class of false
current-facing statement the scanner protects against. Final-tree checks are
cheap relative to the proof audit and make the submitted commit, report, and
claimed verification ledger refer to the same object.

Consequences:

- `rmq-audit-prompt`, `AUDIT_PROMPT.md`, and `AUDIT_PROTOCOL.md` require post-report
  final-tree checks.
- `rmq-coordinator` independently verifies report-only commits before recording
  `ACCEPTED`.
- Reports distinguish checks run on the audited source from checks run after
  the report edit.
- Counterexample wording is paraphrased or role-scoped; policy allowlists do not
  expand merely to accommodate reports.

Evidence:

- Failed A04 report commit `f5c2ab03a064e56f90a17574041cd116568416d8`.
- GitHub Actions CI run `29354845274` and its exact strict-scan failure.
- Corrected A04 report and final-tree verification in the U2 acceptance
  integration change.

Publication-facing significance:

The audit trail can be cited as evidence of falsification-oriented review
without asking readers to excuse a report that bypasses the repository's own
claim controls. The report's command ledger now identifies which exact tree was
checked.

## WDD-20260714-002: migrate the current cost token only after public consumption

Status: Accepted.
Date: 2026-07-14.
Scope: U3 roadmap state and the current-versus-transitional cost claim policy.

Decision:

The claim-drift policy treats `76` as the current canonical charged-trace cost
only after the named algebra, non-synthetic certificate/length/`Costed` bridge,
executable-trace bound, supplied-store transfer, final adequacy theorem,
`List Int` theorem, headline aliases, and paper root all consume the same U2
execution. The policy retains `328` as an explicitly historical transitional
token. Frozen U2 matrices and audits are not rewritten; live roadmap and claim
surfaces identify U3 as candidate-complete pending the normal coordinator audit
boundary.

Context:

U2 deliberately landed `328` as a checked but conservative bound. U3 replaces
that live default with the operation-derived expression
`2 * 13 + (2 * 4 + 2 * 4 + 30) + 4 = 76`. Updating policy before this theorem
chain was public would let prose lead the formal result. Leaving the policy at
`328` after public consumption would instead make the strict scanner certify a
stale claim vocabulary.

Options considered:

- Keep `328` current until a conventional word-RAM small-step machine exists.
- Replace every historical `328` occurrence, including frozen U2 evidence.
- Move only the current token to `76`, preserve named transitional history, and
  state that controller operations remain uncharged pending E1.

Rationale:

The third option matches the actual proof boundary. U3 is candidate-complete
for cost derivation inside the current explicit trace model, while E1 remains
responsible for defining and simulating fully charged controller semantics.
Preserving frozen evidence keeps the audit trail truthful; role-qualified
transitional statements remain reviewable without competing with the current
claim.

Consequences:

- Strict claim scans require the principled charged-trace `76` vocabulary on
  current-facing surfaces and classify `328` as transitional history.
- The roadmap can mark U3 candidate-complete only after the public theorem chain
  and publication-facing documents agree.
- No policy token claims `query(serializedPayload, left, right)`, preprocessing
  complexity, or conventional word-RAM constant time.
- Completion evidence uses `WordRAM.TraceEvent.nonSyntheticWeight` on the actual
  emitted trace as a certificate weight, with checked genuine-event
  classification, no-synthetic, certificate-sum/length equality,
  certificate-sum/`Costed` equality, and the `76` bound. `TraceResult.toCosted`
  still charges full trace length and would count a synthetic compatibility
  marker if one appeared. Controller omissions remain documentary; U3 does not
  hand E1 a parallel instruction vocabulary.

Evidence:

- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq` checks the
  numeric equality `76`.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`
  connects that algebra to the accepted executable trace.
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_eq_cost`
  and `..._nonSyntheticWeight_sum_le_76` connect actual emitted events to the same
  `Costed` execution and final cap.
- `RMQ.Headlines.succinctRMQQueryCostEq` and `RMQPaper` expose the new default.
- `docs/internal/W21_U3_PRINCIPLED_ALLSIZE_COST_ACCEPTANCE_MATRIX.md` records the
  requirement mapping, the old-to-final decomposition, and the verification
  ledger.

Publication-facing significance:

The public claim language now changes only after the corresponding formal route
is consumed end to end. Reviewers can distinguish the improved charged-trace
constant from both its conservative predecessor and the stronger machine-model
claims intentionally deferred to E1 and M1.

## WDD-20260714-003: gate the curated paper topology structurally

Status: Amended candidate complete on the W21 implementation branch; fresh
blind exact-commit audit remains coordinator-owned.
Date: 2026-07-14.
Scope: RMQ paper imports, headline axiom inventory, public claim tables, and
claim-drift regression.

Decision:

Add `scripts/paper_topology_lint.ps1` as a blocking gate. It checks the exact
curated surfaces rather than attempting to infer publication role from every
transitively imported declaration. The lint forbids the six retired aliases and
old execution-regime tokens in `RMQ.Headlines.RMQ`, `RMQPaper`, and the headline
axiom inventory; rejects retired aliases and active historical rows in the
public claim tables; requires the canonical combined profile and weighted-trace
anchor; verifies that `RMQPaper` imports only the canonical RMQ module; verifies
that the broad barrel explicitly imports the compatibility module; and requires
every declaration in that compatibility module to contain `Legacy` or
`Compatibility`.

The first two versions of this decision were incomplete. Lexical scans and
selected table-row checks did not establish that removed spellings were gone
from prose and fenced inventories, nor that documentary theorem references
actually resolved. The first structural repair then exempted all of
`docs/digests/` and `docs/internal/audit_reports/` and treated a casual
`FROZEN-HISTORY` token as sufficient. Those directory-level bypasses could hide
a retired current-facing alias in the README-linked publication digest or in a
new audit report.

The amended lint searches every tracked text surface for each removed spelling
and resolves documentary `RMQ.Headlines.*` identifiers under the broad barrel
and the narrower `RMQPaper` import where appropriate. Its only historical
exceptions couple one of two exact immutable June snapshot paths to exact
case-sensitive marker-plus-line content, require each registered occurrence
exactly once, and reject that marker everywhere else. The current publication
digest and every audit report are fully scanned; neither directory has a
blanket role. The mutation regression covers prose, fenced code, a dead name, a
renamed W18 remnant, compatibility-as-current misuse, current-digest and
audit-report injections, valid exact history, wrong-scope history, and forged,
casual, or duplicate markers.

The aggregate gate now runs the headline axiom inventory, topology lint, and
topology mutation regression. Claim policy version 14 removes digest and audit
prefix alternatives and expresses the same two exceptions as exact
path-and-line pairs. Its regression drives all boundary cases through the
production strict scanner while checking tracked state before and after every
virtual mutation.
Workflow-sensitive path detection includes both topology scripts, the gate,
claim regression, and policy, so future changes require an explicit workflow
decision.

Rejected alternatives:

- Depend only on prose-oriented claim drift to understand Lean import topology.
- Treat a repository-wide zero-match scan as sufficient without elaborating the
  replacement documentary names under their advertised imports.
- Allow historical names in the current headline inventory because their
  source theorems remain sound.
- Treat a same-line word such as "compatibility" as a blanket lint bypass.
- Treat every file below a digest or audit-report directory as immutable
  history.
- Let a casual or forged frozen-history marker authorize its own exception.
- Omit the headline axiom inventory from the aggregate gate.

Consequences:

The regression boundary tests the claimed publication topology directly: a
historical theorem may remain checked and reachable through the broad barrel,
but it cannot silently regain an unqualified paper alias, current claim row, or
headline-inventory role. The Lean theorem remains the semantic evidence that
space and query concern the same object; the lint protects only its curated
exposure.

Evidence:

- `scripts/paper_topology_lint.ps1`.
- `scripts/paper_topology_lint_regression.ps1`.
- `scripts/gate.ps1` headline inventory and topology-lint steps.
- `docs/internal/CLAIM_DRIFT_POLICY.json` version 14 exact path-and-line pairs.
- `scripts/claim_drift_policy_regression.ps1` removed-name and frozen-scope
  production fixtures.

## WDD-20260715-001: bound editorial migrations and gate once at the end

Status: Accepted.
Date: 2026-07-15.
Scope: publication-document migrations after a theorem surface changes.

Decision:

1. Start a disputed editorial migration from the last accepted theorem commit,
   not from a branch that has accumulated speculative policy machinery.
2. Freeze a short reader-facing document set before editing. Change unrelated
   spoke, provenance, or workflow documents only when they contain a broken
   link or a directly false current claim.
3. Review prose against the canonical theorem type and public consumer chain.
   Claim-drift and topology scripts are lexical/name-resolution tripwires, not
   semantic proof systems.
4. Run focused scans, link/name checks, and `git diff --check` while editing.
   Run the full repository gate once after the candidate text is stable. A
   content change after that gate reruns only affected focused checks, plus the
   full gate if the final committed tree changed materially.
5. Use a fresh low-context blind audit on the exact final commit. The auditor
   should compare the small public document set directly with theorem bodies
   and imports, rather than evaluating whether a growing policy framework can
   classify arbitrary English.
6. A lint that searches `git ls-files` must explicitly add required publication
   files and its virtual mutation target. New replacement documents are
   untracked before staging; omitting them can turn a cheap lexical rejection
   into a slow and misleading Lean-resolution path.

Rejected alternatives:

- Run the multi-minute aggregate gate after every prose adjustment.
- Expand a missed sentence into a repository-wide document-role ontology or a
  natural-language classifier implemented with regular expressions.
- Copy a canonical paragraph into every document to satisfy surface scans.
- Keep patching a sprawling editorial branch when a clean theorem checkpoint
  makes the intended change smaller and easier to audit.

Consequences:

Editorial work has a bounded cost and a clear completion condition. The final
gate still protects the repository, while focused checks provide fast feedback
during drafting. Future paper exposition remains recoverable from the theorem
map and design decisions without preserving worker-chat chronology in public
claims.

Amendment after the A06 blind audit:

The paper-topology lint now rejects two exact editorial leftovers on the
bounded current surface: worker/roadmap phase tokens of the form `W<number>` or
`U<number>`, and dated `Snapshot: YYYY-MM-DD` preambles. Mutation tests cover
both failures. This is intentionally a lexical tripwire for known process
artifacts, not a general classifier for publication prose; direct review
against theorem types remains the semantic gate.

The lint also exits after its lexical/structural phase when that phase has
already rejected the tree. Valid trees and acceptance controls still perform
the complete documentary identifier collection and Lean elaboration. This
preserves the evidence boundary while preventing each expected-reject mutation
from paying for checks that cannot change its verdict.

## WDD-20260715-002: treat project skill catalog/frontier mismatch as a startup blocker

Status: Accepted.
Date: 2026-07-15.
Scope: RMQ task initialization, project-skill discovery, coordinator re-entry,
worker handoff, and workflow-governance versioning.

Decision:

1. The exact workflow-governance ref is a separate task input from an older
   source or audit target. The canonical RMQ skill set is the set of tracked
   `.agents/skills/*/SKILL.md` packages at that governance ref.
2. Before substantive work, every RMQ task compares that canonical set with
   both the checkout skill inventory and the RMQ skills shown in the task's
   runtime available-skills catalog. The applicable skill is named explicitly.
3. A missing preflight script, governance ref outside checkout ancestry,
   missing or stale checkout skill, omitted runtime catalog, or missing
   canonical/required runtime skill is a hard stop. The agent reports CWD,
   checkout HEAD, governance ref, expected/checkout/runtime sets, and the
   missing or stale names. It does not substitute another skill or continue
   best-effort.
4. Resume requires a new or restarted task rooted at a checkout containing the
   governing workflow commit and exposing the complete project-skill catalog.
   A user may explicitly authorize a fallback after disclosure, but that run
   cannot record coordinator acceptance, integration, or roadmap closure.
5. Keep repo-local RMQ skills authoritative. Do not maintain user-global copies
   as the default repair: duplicate skill names can coexist, and unversioned
   copies replace a visible missing-skill failure with silent policy drift.
6. Treat the `3f6f1e3`/`c1d39a4` incident as a named regression fixture. The
   production preflight consumes the real governance ref and caller-supplied
   runtime catalog; the deterministic regression uses an equivalent synthetic
   two-commit repository so shallow CI does not depend on historical objects.

Trigger and exact evidence:

An RMQ coordinator task started in the dirty historical checkout
`3f6f1e3a4c246095370917245639fcc741bb4d25` while the prompt declared
`c1d39a43d41183a518257184497958b5937f93d6` as the expected frontier and
explicitly required `$rmq-coordinator`. The runtime catalog exposed only
`rmq-proof-sprint`, matching the historical checkout. At `c1d39a4`, the tracked
project inventory is `rmq-audit`, `rmq-coordinator`, and `rmq-proof-sprint`;
`rmq-audit` and `rmq-coordinator` entered through
`956effafb453f20b3c395b7711e7c667b6bc8999`, which is an ancestor of `c1d39a4`
but not `3f6f1e3`. The task continued with another skill instead of stopping,
so its coordinator dispositions were procedurally provisional even where its
source findings remained useful.

Options considered:

- Treat the runtime catalog as advisory and use the closest available skill.
- Read a missing skill from another worktree and silently continue.
- Copy all RMQ skills into a user-global directory and rely on manual syncing.
- Require only the explicitly named skill, leaving other project-role skills
  undiscovered.
- Pin a workflow-governance ref, compare its full canonical inventory with the
  checkout and explicit runtime catalog, and hard-stop/restart on mismatch.

Rationale:

Codex discovers repo skills from `.agents/skills` in the current working
directory ancestry. It does not reconstruct a newer skill set from another Git
ref or worktree, and repository code cannot refresh a catalog already injected
into a running task. The only sound response to a stale-checkout mismatch is to
make it visible before substantive work and restart from the governing
checkout. Comparing the full canonical set also catches the subtler case where
the named skill exists but another role skill or bundled reference is stale.

Consequences:

- Coordinator, worker, and handoff templates carry the exact governance ref
  and an explicit preflight obligation.
- `AGENTS.md` makes missing applicable skills a repository-wide startup stop,
  even when the missing skill cannot load its own instructions.
- The coordinator skill repeats the gate and cannot grant acceptance from an
  explicitly authorized fallback run.
- The aggregate gate runs a synthetic production-path regression covering
  stale checkout, stale runtime catalog, omitted catalog, undefined required
  skill, frontmatter mismatch, complete catalog, and unrelated extra skills.
- Historical audit remains possible from a current governance/control
  checkout; the source target may be older without becoming the workflow base.
- After this policy lands, the coordinator/project checkout must advance to the
  governing commit and affected tasks must restart. This commit cannot repair
  an already initialized task catalog.

Evidence:

- `AGENTS.md`.
- `.agents/skills/rmq-coordinator/SKILL.md`.
- `.agents/skills/rmq-coordinator/agents/openai.yaml`.
- `docs/internal/templates/COORDINATOR_REENTRY_PROMPT.md`.
- `docs/internal/templates/COORDINATOR_HANDOFF_PACKET.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md`.
- `scripts/project_skill_preflight.ps1`.
- `scripts/project_skill_preflight_regression.ps1`.
- `scripts/gate.ps1`.

Publication-facing significance:

Coordinator acceptance and roadmap state are process evidence that organize the
paper's theorem history. Pinning the workflow frontier prevents those records
from depending on whichever historical checkout happened to initialize a chat,
without changing Lean's proof trust base or treating agent orchestration as
mathematical evidence.

Amends:

- WDD-20260711-002, which required worker bases to contain workflow policy but
  did not guard the coordinator task's own runtime catalog.
- WDD-20260713-003, by adding this catalog/frontier mismatch as a reusable ADD
  failure handled through its failure-mode feedback loop.

## WDD-20260715-003: capture large axiom inventories without streaming them through the gate

Status: Accepted.
Date: 2026-07-15.
Scope: aggregate repository-gate execution and axiom-inventory diagnostics.

Decision:

Run each curated Lean axiom inventory with its complete output redirected to a
temporary file. Preserve the exact process exit-code check and the existing
`sorryAx|ofReduceBool` scan. On success, emit one compact pass line; on failure,
emit the last 80 log lines before failing the gate. Do not stream every
`#print axioms` line through `Tee-Object` during a successful gate.

Trigger:

While validating WDD-20260715-002, the aggregate gate repeatedly terminated in
the sequential axiom phase after emitting tens of thousands of output tokens.
The exact full `lake build`, `scripts/wordram_axiom_check.lean`, and
`scripts/axiom_check.lean` commands passed independently when their output was
captured to temporary files. The failure therefore belonged to gate output
transport/resource behavior, not to a changed theorem or forbidden axiom.

Options considered:

- Accept focused checks and leave the aggregate gate red.
- Remove or weaken one or more axiom inventories.
- Continue teeing all successful output and retry until resource timing happens
  to pass.
- Capture complete output, preserve the exit/pattern checks, and print bounded
  diagnostics only when needed.

Rationale and consequences:

The trust decision depends on the Lean exit code and forbidden-axiom scan, not
on echoing thousands of successful inventory lines into the coordinator chat.
File capture retains all evidence for the duration of the check while reducing
pipeline pressure. Failure remains blocking and now returns a bounded useful
diagnostic. No theorem, axiom allowance, or trust boundary changes.

Evidence:

- `scripts/gate.ps1` `RunAxiomCheck`.
- Exact independent successful runs of `lake build`,
  `lake env lean scripts/wordram_axiom_check.lean`, and
  `lake env lean scripts/axiom_check.lean` on
  `codex/rmq-skill-discovery-hard-stop`.

Publication-facing significance:

The curated axiom inventories remain kernel-facing evidence. Making their gate
transport reliable prevents an output-volume artifact from being confused with
a proof-trust failure while preserving the same acceptance rule.

## WDD-20260718-001: B3 current-anchor migration in the paper topology gate

Status: Accepted.
Date: 2026-07-18.
Scope: `scripts/paper_topology_lint.ps1`, `scripts/headline_axiom_check.lean`
required-anchor lists for the B3 chunked in-word rank/select swap.

Decision:

The paper topology gate migrates its CURRENT weight-bound anchor from
`succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe142` to
`succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe207`
in the same commit that renames the headline abbrev (the B2 precedent for
the 76 -> 142 migration, coordinator-ratified per the B3 worklog), and
GAINS one new required anchor:
`succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` (the B3
vocabulary signature). The headline axiom inventory prints the same two
anchors. Frozen historical anchors are untouched; the frozen 142 constant
lives on as `canonicalSilentWordRankSelectQueryCost` in the Lean surface,
not as a lint anchor.

Options considered:

- Keep the 142 anchor alongside 207 (rejected: the lint anchors name the
  CURRENT paper surface; historical constants are policed by the
  claim-drift policy, not the topology gate).
- Defer the new vocabulary anchor to B5 doc migration (rejected: the
  anchor exists to keep the paper-facing signature theorem resolvable
  from `RMQ.Headlines`; adding it at the swap commit makes the gate catch
  regressions immediately).

Consequences: `paper_topology_lint.ps1` and `headline_axiom_check.lean`
fail if the renamed or new anchor disappears from `Headlines/RMQ.lean`;
documentary claim registries were synced to the new anchor in the same
change.

Evidence: the B3 M5 swap commit and the M6 battery ledger in
`docs/internal/B3_WORKLOG.md`.

## WDD-20260718-002: B4 roadmap W19-paragraph stale-count sync

Status: Accepted.
Date: 2026-07-18.
Scope: `docs/internal/RMQ_FINAL_ROADMAP.md` (workflow-sensitive file) edits
in the B4 M2 bookkeeping commit.

Decision:

The B4 provenance-hardening rung syncs the roadmap's W19 description to
the post-B2/B3 store universe under the established stale-doc-constant
policy: "typed 20-source universe" becomes "typed 22-source universe (23
logical segments; segments 0 and 19 share the BP-code source) ... and the
B2/B3 fringe/select chunk-table sources", and "Fresh segment 21 is
rejected" becomes "Fresh segment 23 is rejected" (the dead-source
anti-vacuity witness moved 21 -> 22 -> 23 across the B2/B3 store
extensions). No roadmap process step, gate, or plan is changed - counts
and segment numerals only.

Options considered:

- Leave the roadmap stale until B5 doc migration (rejected: the B4
  delegation is exactly the provenance-hardening pass, and the stale
  counts misdescribe the W19 packet that B4 extends; the C05 round-3
  audit queued these fixes).
- Fold the sync into a DESIGN_DECISIONS entry only (rejected: the
  design-decision gate classifies the roadmap as workflow-sensitive and
  requires this log).

Evidence: B4 M2 commit `954baea` (diff hunks limited to the two W19
sentences); `design_decision_check.ps1 -Strict` green after this entry.

## WDD-20260719-001: B7 topology-anchor migration `SumLe207` -> `SumLe210`

Status: Accepted.
Date: 2026-07-19.
Scope: `scripts/paper_topology_lint.ps1` and `scripts/headline_axiom_check.lean`
(workflow-sensitive files) edited in B7 commit A (`f6000c3`), plus the
single-line README reconciliation carried separately in `34a1c9d`.

Decision:

The charged sparse-level recharge moves the live whole-query literal
`207 -> 210`, so the CURRENT topology anchor moves with it:

  succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe207
  -> succinctRMQWholeQueryGlobalWordTraceResultNonSyntheticWeightSumLe210

in `paper_topology_lint.ps1` (`$weightBoundAlias`) and in the
`#print axioms` inventory line of `headline_axiom_check.lean`. The frozen
legacy anchors are untouched, per the coordinator ruling recorded in
`docs/internal/B7_WORKLOG.md`.

The numeral is carried in the IDENTIFIER, not only in the statement, so a
migration that moved the literal while leaving the anchor name would leave
a theorem named `...SumLe207` asserting `<= 210`. Renaming is therefore
mandatory rather than cosmetic. The anchor is a LIVE anchor; nothing
frozen is renamed or deleted, and the retired `207` is preserved as
`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq`.

Options considered:

- Keep the anchor name and move only the bound (rejected: produces a
  self-contradictory name, and the rung's own rules forbid asserted or
  misdescribed constants).
- Introduce a numeral-free anchor name so future recharges need no script
  edit (rejected for THIS rung, though it is the better long-run shape:
  it would rename a paper-facing identifier that four documentary
  registries cite, which is a strictly larger blast radius than the
  migration itself, and it would do so in a commit whose purpose is a
  cost migration. Recorded here as a candidate cleanup.)
- Defer the script edits to the swap commit (rejected: the anchor must
  resolve at every commit or the topology gate is red in between, and the
  rename is forced by commit A, not by the swap).

Consequences: `paper_topology_lint.ps1` resolves every documentary
headline identifier against the real `RMQ.Headlines` namespace, so any
documentary registry still naming `...SumLe207` fails the gate
structurally. This is what forced the README reconciliation in `34a1c9d`;
it is also why README.md and `docs/FAMILY_SUMMARY.md` still carrying the
stale `207` NUMERAL do not fail the gate (prose numerals are not resolved
as identifiers) and are reported as outstanding rather than silently
taken from `claude/a07-blocker-repairs`.

Evidence: `paper_topology_lint.ps1` before the README line moved:
"PAPER-TOPOLOGY: FAIL [broad-documentary-symbol-resolution] ... unknown
identifier '...SumLe207'", 1 failure, exit 1. After: "PAPER-TOPOLOGY PASS
(83 broad documentary identifiers; 49 paper identifiers resolved)", exit
0. `lake env lean scripts/headline_axiom_check.lean` exit 0.
## WDD-20260716-001: gate worker-prompt readiness and anti-bypass evidence

Status: Accepted.
Date: 2026-07-16.
Scope: completed-worker repair delegation, read-only acceptance audits,
small-step machine evidence, public-certificate anti-bypass, committed-range
hygiene, and PowerShell workflow portability.

Decision:

1. Classify every proposed worker prompt as `READY_TO_SEND` or
   `DRAFT_DO_NOT_SEND`. A prompt is ready only after its first-line title
   instruction, exact governed base, worker identity/branch, required skill,
   and failure-mode disposition pass `scripts/worker_prompt_preflight.ps1`.
2. When an audit is read-only, classify reusable misses immediately but leave
   durable patching and regression `PENDING`. A repair specification requested
   by the audit may be returned only as `DRAFT_DO_NOT_SEND`; a later governance
   turn must complete the feedback loop before launch.
3. Keep coordinator launch metadata outside the pasted worker prompt, but make
   prompt status and the preflight result mandatory coordinator evidence.
4. Treat E1 candidate
   `fd5e3d24d045c9ec503c258dfeb87599fe002e19` as the named regression fixture
   for small-step atomicity, independent oracles, constructor-exhaustive width,
   input-dependent program accounting, validation reach, and committed-range
   hygiene. Install those rules in the proof-sprint completion gate, known
   failure reference, and matrix template rather than expanding the
   coordinator skill with Lean-specific details.
5. Invoke child PowerShell processes through the current host executable rather
   than the Windows-only command name `powershell`. Run both startup-skill and
   worker-prompt policy regressions in the aggregate gate.
6. Treat M1 candidate
   `9e68c48a52692fa4fb26f1790179d5c623cb47f1` as the named regression fixture
   for mandatory certificate-field consumption. Require a checked typed
   consumer that projects every mandatory field at the exact propositions and
   object arguments promised by the acceptance contract.
7. Preflight every emitted prompt artifact, including drafts, and require the
   populated worker-identity, checkout, roadmap, acceptance, verification, and
   report contracts. Literal title/SHA/skill/branch presence is necessary but
   not sufficient for `READY_TO_SEND`.
8. Treat prompt preflight as a structural lower bound. Reject trivially short
   contract fields and acceptance lists without stable IDs, but require the
   coordinator to record a separate semantic-contract review `COMPLETE` before
   `READY_TO_SEND`; lexical length cannot establish theorem/roadmap fidelity.
9. Verify the destination task's runtime skill inventory independently of the
   governed worker base. A returning task is ready only with explicit current
   runtime evidence. Unknown or stale returning tasks must be replaced by fresh
   Codex worktree tasks started from the exact governed repair-base branch.

Trigger and exact evidence:

The E1 worker reported every matrix row closed at `fd5e3d2`, but an independent
audit found a recursive `.localBPWindow` evaluator charged as one step,
multi-arithmetic `.candidateOfSummary`, invalid test expectations copied from
the raw machine output, an instruction-width predicate that constrained only
`.natConst`, shape-specialized uncounted code literals, validators that did not
run the new machine, and trailing whitespace missed by a clean-working-tree
`git diff --check`. The coordinator then drafted a repair prompt with `Title:`
metadata instead of the required first-line rename instruction, called it ready
before completing this feedback loop, and named an E1 base that did not contain
the current governance commit.

Separately, GitHub CI runs `29545437694` and `29545437344` failed on governance
commit `4a608537e153cc82009c740bcb719b82b5694e60` because
`project_skill_preflight_regression.ps1` invoked `powershell` from an Ubuntu
`pwsh` runner.

The M1 worker supplied a reviewer-native machine certificate at `9e68c48a`, but
the independent audit found that the public theorem accepted the record
opaquely. No checked typed consumer pinned every mandatory field to the exact
well-formedness and supplied-store propositions. Deleting a field and repairing
constructor initializers could therefore leave the advertised dependency
unchecked.

Fresh-context forward testing of governance `2c30a3a8417704a860187263aac70066e3b9ebc6`
found that a seven-line prompt containing only the exact title, governance/base
SHAs, skill, branch, and status literals passed `worker_prompt_preflight.ps1`.
It omitted the roadmap target, frozen acceptance IDs, write scope, verification
contract, and completion-report obligations. The same test also exposed an
ambiguity about whether an emitted `DRAFT_DO_NOT_SEND` artifact should be
preflighted.

A second fresh-context test of `e2515a6a` confirmed that the skeletal bypass was
closed, then showed that every required heading/field filled with `x.` could
still pass. This is partly mechanically preventable and partly irreducible:
the preflight can reject trivial values and require stable acceptance IDs, but
only a coordinator source review can determine whether a nontrivial-looking
goal and proposition contract are actually correct.

The first E1-01R1 and M1-01R1 repair launches were incorrectly recommended as
returning tasks. Both exact bases contained all three governed RMQ skills, but
the old task runtimes exposed only `rmq-proof-sprint`; creating or selecting a
later branch did not rebuild their catalogs. Both workers correctly stopped
before edits. Prompt/base preflight had certified repository state while
silently treating the destination runtime as if it were the same object.

Regression mapping:

- The exact-title and governed-base mutations are rejected by
  `worker_prompt_preflight_regression.ps1`.
- `READY_TO_SEND` with feedback `PENDING` rejects, while the same prompt labeled
  `DRAFT_DO_NOT_SEND` accepts without granting launch authority.
- The `.localBPWindow` and `.candidateOfSummary` evidence fails
  `INV-INSTRUCTION-ATOMICITY` even though category receipts and one-step
  increment theorems remain true.
- Self-derived invalid expectations fail `INV-ORACLE-INDEPENDENCE`.
- A width predicate that defaults non-`.natConst` constructors to `True` fails
  the constructor-exhaustive `INV-ADDRESS-WIDTH` mutation.
- Shape-dependent code literals fail `INV-PROGRAM-ACCOUNTING` until counted or
  uniformly derived.
- Predecessor-only executable checks fail `INV-VALIDATION-REACH`.
- The committed whitespace is rejected by `git diff --check <base>..HEAD` even
  when plain post-commit `git diff --check` is green.
- A certificate passed opaquely fails `INV-CERTIFICATE-ANTI-BYPASS` until one
  checked typed consumer projects every mandatory field at its exact
  proposition and object arguments; field-deletion, weakening, and sibling-
  substitution mutations must break that consumer.
- The skeletal forward-test prompt is rejected unless every required template
  section and load-bearing field is populated, including the committed-range
  diff check and candidate-report status contract.
- Trivial filler values and acceptance text without a stable ID reject, and
  `READY_TO_SEND` with semantic-contract review `PENDING` rejects. A recorded
  review remains coordinator evidence, not mathematical proof.
- A returning prompt with destination runtime `UNKNOWN` or `STALE` rejects. A
  fresh prompt is ready only when configured to start its Codex worktree from
  the governed repair-base branch and still runs project-skill preflight first.

Rejected alternatives:

- Add another prose reminder for titles without mechanically checking it.
- Let a returning worker merge workflow policy after beginning implementation.
- Ask the proof worker to patch coordinator process as part of the proof repair.
- Treat constructor/category coverage as evidence about evaluator atomicity.
- Let the implementation result serve as the expected edge-case oracle.
- Run only the predecessor validator and call it E1 executable evidence.
- Treat record construction, field-name inventories, or opaque record passage
  as proof that every mandatory certificate field is load-bearing.
- Treat a title/SHA/skill/branch token check as certification that the roadmap,
  acceptance, verification, and report contracts were populated.
- Pretend regexes can establish that plausible-looking roadmap prose is
  semantically faithful, or omit an explicit human/agent source reread.
- Infer a destination task's runtime catalog from repository files, or assume a
  branch/worktree created inside an old task refreshes its available skills.
- Preserve the Windows-only `powershell` invocation because local checks pass.

Consequences:

- A launch-ready repair prompt now has a reproducible readiness certificate and
  one exact governance-containing base, and the certificate rejects skeletal
  prompts that omit the task's load-bearing contracts.
- Read-only audits can satisfy a request for a repair specification without
  silently bypassing the failure-mode feedback loop.
- Fully charged machine reviews must inspect executable bodies, code/data
  accounting, and validation reach rather than infer semantics from theorem
  names or category inventories.
- Reviewer-native certificate reviews must follow exact field projections into
  typed consumers rather than infer anti-bypass from record construction or a
  public theorem parameter.
- Existing legitimate weaker claims remain available when labeled accurately:
  `fd5e3d2` still supplies a transition-system simulation and fuel bound, but
  not the rejected fully charged familiar-machine capstone.
- No Lean theorem, payload representation, public identity, or proof trust base
  changes in this workflow decision, so no separate proof/code design decision
  is required.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`.
- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
- `scripts/worker_prompt_preflight.ps1`.
- `scripts/worker_prompt_preflight_regression.ps1`.
- `scripts/project_skill_preflight_regression.ps1`.
- `scripts/gate.ps1`.
- Aggregate `scripts/gate.ps1` pass on 2026-07-16, including all Lean builds,
  eight axiom inventories, both workflow regressions, strict claim drift, and
  paper-topology mutations.

Publication-facing significance:

Worker and coordinator statuses organize how machine-model claims reach the
paper frontier. Preventing a macro-step, self-oracle, uncounted-code, stale-
validator, or opaque-certificate candidate from being labeled ready keeps
workflow evidence aligned with the theorem actually available, without
treating the workflow machinery itself as mathematical proof.

## WDD-20260717-001: make verification cost-aware and forbid blind expensive reruns

Status: Accepted.
Date: 2026-07-17.
Scope: worker proof loops, completed-worker audits, local repository gates,
timeouts, cold-worktree warm-up, and final exact-tree certification.

Decision:

1. Require a verification coverage ledger that classifies commands as
   development-loop, final-required, or conditional and maps each command to
   changed paths, acceptance rows, unique failure coverage, exact tree state,
   expected runtime, timeout, observed duration, and rerun reason.
2. Order verification by information per unit time: static hygiene, focused
   targets, direct public consumers and relevant trust checks, then broad roots
   or the aggregate gate only when scope or the frozen contract requires them.
3. Run only one heavy Lean/Lake process at a time against a shared build tree.
4. Treat a wrapper timeout or quiet output as an execution-state question, not
   a semantic failure. Inspect child liveness, CPU/artifact progress, missing
   import artifacts, environment, and accidental full-build fallback before
   deciding to stop or retry.
5. Forbid launching the same expensive command again on an unchanged tree
   without first accounting for the old process and recording a material
   changed condition. If the child survived, wait for it; if it ended, retry
   only after a fix, dependency warm-up, environment correction, target
   narrowing, or evidence-based timeout change.
6. Run an aggregate gate at most once on an unchanged final tree. Debug a late
   failure with its smallest component and reserve the next aggregate run for
   final certification.
7. Do not equate repeated gate runs with independent evidence. Worker results
   remain untrusted for acceptance, but their durations and failure locations
   may guide proportionate independent audit scheduling and cache use.

Trigger and evidence:

The user identified recurring RMQ runs where a 20-minute command reached a
timeout and the same work was then paid again for 30 minutes or more. The active
E1 repair transcript also showed why the policy needs nuance: large source
checks were repeated after genuine source changes, while an adapter proof first
exceeded the default heartbeat allowance and later exceeded a larger allowance.
Some reruns were dependency-valid; the missing rule was to distinguish those
from unchanged blind retries before spending another long interval.

Historical evidence already records two related cases: high-volume axiom
output made the aggregate gate look broken even when direct commands passed,
and topology/full-gate runs could appear hung because of stale Lean processes
or a focused mutation falling back to full resolution. Together these show
that silence, wrapper termination, semantic failure, stale children, and cold
dependency work are different states and must not share one retry policy.

Rejected alternatives:

- Require the full gate after every edit or at every audit checkpoint.
- Put a universal short timeout on Lean commands and retry when it expires.
- Solve timeout risk by using arbitrarily huge limits without inspecting
  progress or target scope.
- Run several heavy Lean jobs concurrently and assume wall-clock time improves.
- Trust worker gate results as acceptance evidence merely to avoid local work.
- Skip all broad gates, including final public/integration certification.

Consequences:

- Narrow work receives narrow verification, while public capstones,
  integration commits, artifacts, and trust-boundary changes still receive the
  broad checks their contracts require.
- Expensive checks are scheduled once for final certification instead of being
  reflexively duplicated before and inside the aggregate gate.
- A timeout now requires process and cache diagnosis before a retry, reducing
  duplicate survivors, cold rebuilds, and misleading failure reports.
- Exact-tree identity remains essential: a source or checker edit invalidates
  its dependent checks, while a docs-only edit does not automatically erase
  unrelated Lean compilation evidence.
- This is workflow policy only. It changes no Lean theorem, public claim,
  payload accounting, cost model, or trust allowance.

Evidence:

- `AGENTS.md` verification guidance.
- `.agents/skills/rmq-coordinator/SKILL.md` verification economics.
- `.agents/skills/rmq-proof-sprint/SKILL.md` verification workflow.
- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md` command ledger
  and rerun rules.
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md` expensive-
  verification regression pattern.
- `docs/internal/templates/WORKER_PROMPT.md` tiered verification contract.
- `scripts/worker_prompt_preflight_regression.ps1`: all cases passed in 108.2
  seconds on the seven-file governance diff.
- `scripts/project_skill_preflight_regression.ps1`: all cases passed in 84.6
  seconds on the same tree.
- `scripts/design_decision_check.ps1 -Strict` and `git diff --check`: passed.

Publication-facing significance:

Gate evidence supports confidence in the theorem and artifact frontier, but
the amount of repeated compute is not itself mathematical evidence. This rule
preserves the checks that matter while preventing timeout behavior from being
misreported as proof failure or mistaken for stronger validation.

## WDD-20260717-002: require committed mutation evidence for public dependencies

Status: Accepted.
Date: 2026-07-17.
Scope: public certificate anti-bypass, paper-theorem dependency checks,
mutation campaigns, worker completion evidence, and repair-prompt readiness.

Decision:

1. Add `INV-MUTATION-REPRODUCIBILITY` whenever acceptance relies on an
   exhaustive, production, or public-dependency mutation campaign.
2. Require the candidate to commit a replayable runner or stable fixture set
   that names every claimed mutation, expected verdict, exact failing surface,
   expected-accept controls, and restoration/clean-tree check.
3. Treat matrix prose, copied terminal output, one-off edited worktrees, and
   unreferenced Git objects as discovery or process evidence, never as
   replayable acceptance evidence.
4. For a public dependency, require a checked expected-type consumer whose
   proof route consumes the public theorem and whose elaboration fails when the
   advertised conjunct is removed. Axiom printing or checking the theorem's
   current mutable type does not pin the dependency.
5. Use M1 R2 candidate
   `1f50e5698a0842b8c50c1e08d101b076152d6bef` as the named regression
   fixture, while preserving its legitimate improvement over the earlier M1
   candidate: the 24-field independent typed projection is real and remains
   required.

Trigger and exact evidence:

The independent M1 R2 audit found that `RequiredFacts` repeated all 24 exact
certificate propositions and that `.requiredFacts` used every literal field
projection. The guarded list packet and paper theorem consumed the new object.
However, no M1 mutation runner or fixture existed under `scripts/`, and the
matrix's cited snapshot was outside the candidate ancestry and had no ref.

In a disposable exact-candidate worktree, removing only the paper theorem's
guarded `RequiredFacts` conjunct and corresponding tuple element still passed
`lake build RMQPaper RMQ` and
`lake env lean scripts/headline_axiom_check.lean`. The existing axiom check
followed the theorem's current type, so it could not reject deletion of the new
public dependency. The source topology was materially improved, but the frozen
public anti-deletion acceptance row was not reproducibly enforced.

Regression mapping:

- Candidate `1f50e569...` fails `INV-MUTATION-REPRODUCIBILITY` because
  `git ls-tree -r --name-only <candidate> scripts` contains no M1 mutation
  runner or fixtures.
- The public-dependency deletion passes the candidate's production paper build
  and headline axiom check, so those checks alone do not satisfy the new rule.
- A repair closes the rule only when its committed runner rejects that deletion
  through an expected-type consumer and also accepts one explicitly
  non-load-bearing packet-only control.
- A legitimately weaker theorem or packet remains permitted when it does not
  advertise the deleted fact as load-bearing and its expected-accept control
  records that boundary.

Rejected alternatives:

- Accept a mutation campaign summarized only in the worker report or matrix.
- Preserve local mutation commits as unreachable objects and assume reviewers
  can reconstruct them.
- Treat `#print axioms` as an assertion of the theorem's full public type.
- Require every packet restatement to be load-bearing, eliminating useful
  compatibility or documentary packaging.
- Discard the genuine R2 typed-field improvement because its public mutation
  evidence was incomplete.

Consequences:

- M1 R3 remains narrow: it adds durable enforcement around the sound R2
  topology instead of redesigning the certificate or evaluator.
- Future public capstones cannot claim anti-deletion coverage without shipping
  the cases needed to replay it.
- Expected-accept controls preserve honest non-load-bearing packaging and keep
  the rule from equating every nearby proposition with a required public input.
- The workflow change adds no Lean axiom, payload bit, modeled tick, machine
  event, or runtime claim.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`.
- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`.
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- Exact-candidate mutation audit of
  `1f50e5698a0842b8c50c1e08d101b076152d6bef`.
- System `quick_validate.py`: both modified RMQ skills valid.
- `scripts/worker_prompt_preflight_regression.ps1`: all cases passed in
  139.7 seconds.
- `scripts/project_skill_preflight_regression.ps1`: all cases passed in
  117.7 seconds.
- `scripts/design_decision_check.ps1 -Strict` and `git diff --check`: passed.

Publication-facing significance:

The paper theorem's advertised conjunction is part of the reviewer-facing
claim surface. Requiring a replayable deletion test and independent expected-
type consumer prevents later refactors from silently removing a claimed
machine-adequacy dependency while all current-name and current-type checks stay
green.

## WDD-20260717-003: permit opt-in audited worker chains

Status: Accepted.
Date: 2026-07-17.
Scope: Codex task launch, completion monitoring, completed-worker audit,
successor-prompt launch, model routing, and automation authority boundaries.

Decision:

1. When the user explicitly opts in, allow the RMQ coordinator to create a
   fresh governed Codex worker task from a preflighted `READY_TO_SEND` prompt,
   select a contract-appropriate model/reasoning level, and attach a completion
   logical monitor record to the owning coordinator task.
2. While a worker is active, the monitor reads status without opening or
   steering the task and emits only a terse update. Completion is determined
   from task state, not silence or elapsed time.
3. On completion, run the ordinary `rmq-coordinator` exact-commit audit,
   including independent reconstruction, proportionate verification, mandatory
   blind leaves, and the reusable failure-mode feedback loop.
4. Automatically launch successor prompts only after semantic review and
   failure-mode feedback are complete and `worker_prompt_preflight.ps1` marks
   each artifact `READY_TO_SEND` against an exact base containing current
   governance. Suppress duplicate handle/base/branch launches and attach a new
   logical monitor record to every launched successor.
5. Stop for user direction when a next step requires merge/push authority,
   destructive lifecycle work, missing runtime skills, an unresolved
   dependency, a new proof-architecture choice, or unsafe/wasteful heavy-worker
   concurrency.
6. Default public theorem and nontrivial Lean work to `gpt-5.6-sol` with `max`
   reasoning, use `xhigh` for bounded mechanically checked repairs, and use
   `gpt-5.6-terra` with `xhigh` for read-only or lower-risk tooling work. Do not
   select `ultra` without an explicit coordinator record that `max` is
   inadequate for the exact task.
7. Use a 30-minute monitor cadence by default and make launch recovery
   idempotent: inventory exact handle/base/branch ownership before creation; if
   task creation succeeds but monitor attachment fails, retain the task and
   retry only its monitor rather than creating a duplicate.
8. When the platform permits only one heartbeat per coordinator task,
   multiplex exact per-worker logical records in that heartbeat. Remove only a
   completed worker's record after audit/disposition, update the heartbeat while
   others remain, and delete it only when the watch set is empty. Do not create
   a cron workaround.

Trigger and evidence:

The user requested that M1 R3 be launched directly, monitored like E1 R2, and
that either completion automatically trigger coordinator audit, next ambitious
prompt engineering, successor task creation, and a successor monitor. The
repository already had stable prompt preflight, runtime-skill preflight,
failure-mode feedback, worker lifecycle, and exact-commit audit rules. Those
gates make a bounded opt-in chain materially different from the unreviewed
proof-writing loop rejected by WDD-20260708-002.

The live E1 R2 monitor also exposed a scheduling risk: a 30-minute aggregate
gate timed out and the worker immediately began the same full gate again with a
one-hour ceiling. Automated chaining therefore inherits verification economics
and must not treat repeated expensive commands or concurrent heavy workers as
evidence of rigor.

Rejected alternatives:

- Keep requiring the user to copy every preflighted prompt and manually create
  every completion timer.
- Launch successors directly from worker self-reports without coordinator
  reconstruction or failure-mode feedback.
- Build an unconstrained recursive proof-writing daemon that can merge, push,
  delete worktrees, or choose new proof architecture.
- Use an unstructured global monitor that lacks exact per-worker records and
  risks confusing task identity or deleting the wrong watch entry.
- Route every task to `ultra` irrespective of scope, or route proof work to a
  cheaper model merely because the check surface is automated.
- Start duplicate or dependency-conflicting workers simply because a prompt
  can be generated.

Consequences:

- Routine launch/monitor/audit/prompt handoffs no longer require manual copying
  once the user opts in.
- Mathematical acceptance remains coordinator-owned and source-grounded; task
  creation and model choice add no proof evidence.
- Each worker has a concrete logical record and stop condition even when one
  platform heartbeat multiplexes the watch set, preventing an invisible
  uncontrolled recursive loop.
- A coordinator restart or partial launch failure can be reconstructed from
  task/automation inventory without multiplying workers.
- Integration and destructive lifecycle actions remain explicit boundaries, so
  an accepted candidate may still require user direction before a dependent
  A1/V1 launch.
- Model routing remains strong but cost-aware, with `ultra` exceptional rather
  than routine.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md` opt-in automated completion loop.
- `AGENTS.md` automated-chain authority boundary.
- `docs/internal/ADD_WORKFLOW_TOOLING_PLAN.md` reviewed-worker automation stage.
- `docs/internal/WORKER_LIFECYCLE.md` one-monitor-per-worker lifecycle rule.
- `scripts/project_skill_preflight.ps1` and
  `scripts/worker_prompt_preflight.ps1` launch gates.
- Live E1 R2 and M1 R3 coordinator task/monitor exercise on 2026-07-17.

Publication-facing significance:

Automation changes who performs coordination steps, not what the paper proves.
Exact-commit audits, committed evidence, trust checks, and public theorem
consumption remain unchanged; agent reports and monitor state remain process
evidence outside the proof trust base.

## WDD-20260717-004: require quantifier-matched formal obstructions

Status: Accepted.
Date: 2026-07-17.
Scope: proof-sprint stop conditions, completed-worker audit, acceptance
matrices, and worker prompts for formal obstruction claims.

Decision:

1. A formal obstruction may stop a worker only when its checked proposition
   negates the frozen target or a checked theorem derives `False` from that
   target on the same domain, objects, guards, and quantifiers.
2. Separate facts about an arbitrary mutated state, an unbounded shape
   parameter, and one reachable execution cannot be composed by prose.  If
   their conjunction is load-bearing, one checked canonical reachable family
   must preserve the growing parameter and actual invocation together.
3. Every obstruction report must distinguish impossibility of the frozen
   target from failure of the current implementation or one proposed
   decomposition.  The latter is valuable checkpoint evidence but does not
   authorize target-level `Status: OBSTRUCTED`.
4. Use E1 R2 candidate
   `39e97e08b14e8960c484cc7948409d550a97c955` as the named regression: its
   three true witness theorems do not establish the missing common canonical
   reachable family and therefore must be rejected as target-level closure.

Trigger and evidence:

The E1 R2 report combined an arbitrary register mutation, unbounded canonical
block geometry, and a singleton reachable `.localBPWindow` execution into a
claim that the frozen fully charged familiar-machine target was impossible.
Independent source reconstruction found no theorem connecting those witnesses
and no proof that all permitted familiar decompositions fail.  The candidate
does correctly prove that its current macro instruction and fixed scalar
unrolling are inadequate; the workflow defect was upgrading that narrower
result to a target obstruction.

Rejected alternatives:

- Accept narrative witness composition when every cited theorem is true.
- Require only theorem names, without comparing domains and quantifiers.
- Discard narrow implementation obstructions that are accurately labeled.
- Amend the E1 architecture automatically from an incomplete obstruction.

Consequences:

- Workers must retain load-bearing witness identity through the obstruction
  proposition instead of relying on a prose join.
- Coordinators and blind auditors can distinguish a real design fork from a
  repairable implementation checkpoint before changing the roadmap contract.
- The rule adds no Lean axiom, payload data, modeled tick, trace event, or
  runtime claim.

Evidence:

- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.
- `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`.
- `.agents/skills/rmq-coordinator/SKILL.md`.
- `docs/internal/templates/PROOF_ACCEPTANCE_MATRIX.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- Exact-candidate audit of
  `39e97e08b14e8960c484cc7948409d550a97c955`.
- System `quick_validate.py`: both modified RMQ skills valid.
- `scripts/worker_prompt_preflight_regression.ps1`: all cases passed in
  141.7 seconds.
- `scripts/design_decision_check.ps1 -Strict` and `git diff --check`: passed.

Publication-facing significance:

Obstruction claims determine whether the project changes its machine model or
payload architecture. Requiring a checked quantifier-matched obstruction
prevents process prose from forcing a paper-level design amendment that the
formal evidence does not establish.

## WDD-20260717-005: require nonvacuous and bounded replay harnesses

Status: Accepted.
Date: 2026-07-17.
Scope: mutation-runner acceptance, focused replay selectors, child-process
economics, worker-prompt preflight, and completed-worker audit.

Decision:

1. A harness claiming exhaustive replay must declare the exact ordered frozen
   case registry, prove uniqueness and set equality, check any ID-to-field or
   ID-to-object mapping, and check exact verdict counts. A total pass count is
   not coverage evidence.
2. A focused selector must execute exactly one requested frozen ID and reject
   unknown IDs. Cheap controls must cover an omitted middle ID, a duplicated
   middle ID, a valid frozen ID, and an unknown ID.
3. Every external compiler or tool stage used by a replay harness must have a
   positive evidence-based deadline, classify timeout as failure, terminate its
   owned process tree, and run cleanup plus live-tree integrity checks in
   `finally`. A cheap sleeper self-test exercises this path without hanging the
   semantic campaign.
4. Worker prompts carry the stable anchors `REPLAY-EXACT-REGISTRY`,
   `REPLAY-SELECTOR-NONVACUITY`, and `REPLAY-SUBPROCESS-DEADLINE`; prompt
   preflight rejects any missing anchor before launch.

Trigger and evidence:

The exact-commit audit of M1 R3 candidate
`868166550fe0df905aef2f7719147d62e88c87bf` found that its topology regression
registered descriptive names while the frozen matrix named `A01` and `A02`.
`-OnlyCase A01`, `-OnlyCase A02`, and an unknown selector all exited zero with
`0 reject; 0 accept`. The mutation runner's current 41 IDs are correct, but its
only aggregate completeness check is `$passes -eq 41`, so a missing middle case
can be replaced by a duplicate without detection. Its synchronous Lean child
has no deadline or process-tree cleanup path, so a hang can prevent case
cleanup, live-integrity comparison, and final verdict indefinitely.

Rejected alternatives:

- Accept a zero-case focused run because the full aggregate run happened to
  pass once.
- Treat boundary-name lint plus a total pass count as an exact registry proof.
- Add an arbitrarily large outer gate timeout without a per-stage timeout,
  owned-process cleanup, or cheap timeout self-test.
- Rerun the 40-minute aggregate gate to diagnose defects already reproduced by
  static inspection and focused ten-second controls.

Consequences:

- Exact case IDs become reviewer-replayable rather than documentary labels.
- Registry drift and selector vacuity fail cheaply before any Lean mutation
  sweep starts.
- A hung compiler becomes a bounded failed case with cleanup evidence instead
  of an indefinite gate and an incentive for wasteful unchanged reruns.
- The workflow rule changes no Lean proposition, payload bit, proof field,
  modeled tick, trace event, or runtime claim.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- `scripts/worker_prompt_preflight.ps1`.
- Named regressions `m1r3-exact-registry-omitted`,
  `m1r3-zero-case-selector`, and `m1r3-unbounded-subprocess` in
  `scripts/worker_prompt_preflight_regression.ps1`.
- Fresh-blind exact-candidate audits of M1 R3 candidate `8681665`.

Publication-facing significance:

Mutation evidence protects the reviewer-facing public theorem dependency.
Requiring exact, nonvacuous, bounded replay prevents a green process transcript
from standing in for actual coverage of the frozen public acceptance contract.

## WDD-20260717-006: complete opt-in chains through private repair bases

Status: Accepted.
Date: 2026-07-17.
Scope: audited-worker successor construction, repair-base authority, terminal
watch retirement, and automatic-chain stop boundaries.

Decision:

1. Explicit opt-in to the audited worker chain authorizes the coordinator to
   create a dedicated local unpublished repair-base branch joining a completed
   candidate with current governance when that sibling relationship is the sole
   blocker to a preflighted repair successor.
2. The join must preserve the candidate as first parent and current governance
   as second parent, avoid `main` and published/frontier branches, remain local,
   and pass exact ancestry, scope, clean-state, range, and project-skill checks.
   Any semantic/public-theorem conflict or proof choice stops for user review.
3. This narrow authority does not authorize candidate acceptance, roadmap/main
   integration, push, branch/worktree deletion, publication, or proof-
   architecture selection.
4. A terminal-worker audit is not complete while its logical watch remains
   live. Use the automation API first. If self-deletion of the currently
   executing empty heartbeat is locked, verify its exact ID, target thread, and
   empty watch set, then move only that catalog record recoverably outside the
   live automation directory and report its location.

Trigger and evidence:

The user explicitly opted into automatic launch, monitoring, completed-worker
audit, next-prompt engineering, successor launch, and repeated monitoring. After
M1-01R3 candidate `868166550fe0df905aef2f7719147d62e88c87bf` was rejected, the
coordinator correctly engineered M1-01R4 but left it `DRAFT_DO_NOT_SEND` because
candidate and governance `5efb1515c543e866cda67e66866f3dc34149ed42` were siblings.
That treated the private governed repair-base join already required by the
delegation section as forbidden integration, breaking the opted-in chain. The
old heartbeat also kept polling the terminal M1 task because its automation API
could not delete itself while its active run held the record; the record was
eventually retired recoverably from the live catalog.

Rejected alternatives:

- Require the user to manually construct every mechanical candidate-plus-
  governance repair base after opting into the automatic chain.
- Treat a private local repair-base join as equivalent to merging an accepted
  candidate into `main`.
- Permit automatic resolution of proof, public-theorem, or architecture
  conflicts.
- Leave an empty terminal-worker watch active because the preferred API is
  self-locked, causing repeated stale audits and user noise.
- Delete arbitrary automation records or use a duplicate cron workaround.

Consequences:

- The automatic chain now advances through mechanically governed repair loops
  without silently expanding authority to publication or roadmap integration.
- Ambiguous semantic joins still stop for the user.
- Terminal watches have a bounded, recoverable retirement path and cannot keep
  re-querying already audited workers indefinitely.
- The workflow change adds no Lean axiom, payload data, proof field, modeled
  tick, trace event, or runtime claim.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md` anchors
  `AUTO-CHAIN-PRIVATE-REPAIR-BASE` and `AUTO-CHAIN-MONITOR-RETIREMENT`.
- Named regressions `auto-chain-private-repair-base-allowed`,
  `auto-chain-main-merge-stopped`, and `auto-chain-terminal-watch-retired` in
  `scripts/worker_prompt_preflight_regression.ps1`.
- Exact M1-01R3 audit and successor disposition in coordinator task
  `019f6d85-7626-7433-a60b-81f8be29689a`.

Publication-facing significance:

This changes only who performs mechanical workflow joins and watch cleanup.
Mathematical acceptance, exact-commit audit, public theorem identity, and
submission integration remain independently gated.

## WDD-20260717-007: proxy obstructions require checked target implication

Status: Accepted.
Date: 2026-07-17.
Scope: theorem-shaped stop conditions, operational reachability, and completed-
worker obstruction audit.

Decision:

1. A proxy proposition may support `Status: OBSTRUCTED` only when every
   load-bearing clause is frozen verbatim or a checked theorem proves that the
   full frozen target implies the proxy.
2. A worker may not insert the contradiction-producing lower bound as a field
   of a stronger proxy and treat its negation as a negation of the assigned
   target.
3. Boundary values, guard validity, accepted logical output, and same-block
   arithmetic do not establish execution reachability.  When an instruction
   occurrence is load-bearing, the checked witness must retain its occurrence,
   pre-state, full instruction and evaluated operands, post-state, and exact
   run or receipt object, or prove an equivalent operational bridge.
4. A sound negation lacking those bridges remains valuable as a narrowly
   labeled decomposition obstruction, but it does not close the roadmap node.

Trigger and evidence:

The exact-commit audit of E1 R3 candidate
`7fe5b8ba353b955b8e989ddd2ae8dc2371140518` found a sound unbounded family of
accepted same-block boundary intervals and a sound negation of a newly defined
scalar packet target.  The packet target stipulated
`localCount <= localBPSteps`; the frozen contract permitted an equally familiar
primitive decomposition and did not state that lower bound.  Its canonical
invocation predicate retained no actual run, transition, receipt occurrence,
instruction operands, pre-state, or post-state.  Three fresh-blind audit leaves
independently reproduced the mismatch.

Rejected alternatives:

- Accept a stronger proxy because its theorem name and surrounding matrix prose
  describe the frozen target.
- Treat accepted boundary arithmetic as proof that the production machine
  executes the relevant instruction.
- Discard the narrow arithmetic obstruction entirely because it does not close
  the broader target.
- Amend the frozen machine contract implicitly during a repair attempt.

Consequences:

- Obstruction claims now preserve predicate identity and execution-object
  identity through the contradiction.
- Narrow decomposition impossibilities remain publishable checkpoint evidence
  when labeled precisely.
- Workers must derive, rather than stipulate, the lower bound that drives an
  impossibility argument.
- The workflow rule changes no Lean proposition, payload bit, proof field,
  modeled tick, trace event, or runtime behavior.

Evidence:

- `.agents/skills/rmq-proof-sprint/references/COMPLETION_GATE.md`.
- Named regression `E1R3-SURROGATE-OBSTRUCTION-REGRESSION` in
  `.agents/skills/rmq-proof-sprint/references/KNOWN_FAILURE_MODES.md`.
- Fresh-blind target-fidelity, execution-semantics, and trust/topology audits of
  exact candidate `7fe5b8ba353b955b8e989ddd2ae8dc2371140518`.

Publication-facing significance:

An obstruction can force a paper-level model or payload decision.  Requiring a
checked implication from the frozen target prevents a decomposition-specific
lower bound from being mistaken for an impossibility of the claimed machine
architecture.

## WDD-20260718-003: name audit prompt engineering and scope runtime skills by role

Status: Accepted.
Date: 2026-07-18.
Scope: project-skill identity, runtime discovery, startup preflight, and worker
restart policy.

Decision:

1. Rename the coordinator-side `rmq-audit` skill to `rmq-audit-prompt` and make
   its metadata state explicitly that it engineers external-auditor prompts and
   evidence packets. It is not an audit-worker execution skill.
2. Keep the full canonical skill inventory mandatory in the governed checkout
   and working tree, including frontmatter and freshness checks.
3. Require the runtime catalog to expose every skill explicitly required by the
   task's role, but do not require unrelated canonical skills to be injected.
   A proof-only worker may therefore pass with only `rmq-proof-sprint`; a
   coordinator must expose `rmq-coordinator`; prompt engineering must expose
   `rmq-audit-prompt` in addition to any other skill it actually uses.
4. Continue to hard-stop on an omitted runtime catalog, undefined required
   skill, missing required runtime skill, incomplete/stale canonical checkout,
   frontmatter mismatch, or governance ancestry failure.

Trigger and evidence:

R1, titled `(R1) Repair the A07 blocking findings`, was a proof-only repair task
whose prompt required `rmq-proof-sprint`. Its checkout contained all three
canonical skills, but the task runtime exposed only `rmq-proof-sprint`. The old
preflight compared the entire canonical set to the runtime set and stopped R1
for missing `rmq-audit` and `rmq-coordinator`, although neither was applicable
to the work. The name `rmq-audit` also suggested an auditor execution skill even
though WDD-20260708-008 had already repurposed it to coordinator-side prompt
engineering.

Rejected alternatives:

- Install every canonical skill globally so every task always sees all roles.
  That duplicates versioned repository policy and can silently drift.
- Drop canonical checkout validation and check only the required runtime name.
  That would permit a governed task to start from an incomplete or stale skill
  frontier.
- Keep the ambiguous `rmq-audit` name and explain the distinction only in prose.
- Let proof workers bypass a known failing preflight ad hoc. That weakens a
  deterministic gate instead of correcting its overly broad predicate.

Consequences:

- Fresh tasks still need a governance-containing checkout because runtime skill
  discovery occurs when a task is initialized and cannot be repaired by later
  branch movement alone.
- Role-specific tasks no longer fail merely because unrelated coordinator-side
  skills are absent from their injected runtime catalog.
- External audit workers follow their frozen prompt and
  `docs/internal/AUDIT_PROTOCOL.md`; coordinators use `rmq-audit-prompt` when
  authoring that prompt or packet.
- Historical records may retain the former name when quoting an old catalog;
  all live paths, metadata, templates, and tooling use the new identity.
- No Lean proposition, payload bit, proof field, modeled tick, trace event, or
  runtime claim changes.

Evidence:

- `.agents/skills/rmq-audit-prompt/SKILL.md` and `agents/openai.yaml`.
- `AGENTS.md` and `.agents/skills/rmq-coordinator/SKILL.md`.
- `scripts/project_skill_preflight.ps1`.
- Named regressions `role-runtime-proof-sprint-only-pass`,
  `coordinator-role-missing-from-runtime`,
  `audit-prompt-role-missing-from-runtime`, and
  `legacy-rmq-audit-name-rejected` in
  `scripts/project_skill_preflight_regression.ps1`.
- Worker R1 task `019f7801-d565-70e2-83cf-1546a1f62090` and its exact blocked
  preflight report.

Supersedes:

- WDD-20260708-008 for the skill name only; its responsibility split remains.
- WDD-20260715-002 points 2 through 4 only where they required the complete
  canonical set in every runtime. Full canonical checkout validation and hard
  stops for missing applicable skills remain in force.

Publication-facing significance:

This is workflow infrastructure only. It preserves versioned role policy while
preventing unrelated skill injection from becoming false evidence that a proof
worker is unqualified to run its assigned theorem campaign.

## WDD-20260718-004: update the aggregate-gate topology comment without changing the gate

Status: Accepted.
Date: 2026-07-18.
Scope: the topology description in `scripts/gate.ps1` only.

Decision:

Update the stale physical-payload/76 topology comment to describe the live
canonical reviewer-payload, `readWord`-only, derived-207 topology.  This is a
comment-only correction: it changes no workflow command, command ordering,
failure condition, mutex handling, gate semantics, or executable behavior.

Rejected alternatives:

- Leave the stale comment in place, which would continue to misdescribe the
  checks performed by the unchanged gate.
- Change a checker or executable command together with the prose correction;
  no behavioral change is required for this repair.

Consequences:

- Readers see the topology that the existing gate already checks.
- Gate scheduling, execution, and verdicts are unchanged.

Evidence:

- The committed-range diff of `scripts/gate.ps1` changes only the topology
  comment.
- `scripts/design_decision_check.ps1 -Strict -Base
  6155d48dde13dfc8e4b3da108b4b81e258300b86` checks this decision record.
## WDD-20260718-005: strict drift policy separates live claims from frozen history

Status: Accepted.
Date: 2026-07-18.
Scope: current RMQ public surfaces, historical evidence, claim-drift policy,
and completed-worker public-claim audits.

Decision:

1. Treat the pre-A07 current constants and fixtures as strict failures on live
   public/current surfaces: cost bounds `76` or `142`, a 20-source manifest,
   fresh or rejected segment `21`, and repeated-read global positions `0` and
   `12`.
2. Admit those literals only in explicitly frozen historical surfaces such as
   dated digests, audit reports, acceptance matrices, worklogs, and design-
   decision ledgers. A broad `docs/internal` allowance is not sufficient.
3. Keep the production scanner's final strict verdict as the policy result and
   reproduce the failed candidate's exact evidence pattern with named
   regression fixtures plus current-value expected-accept controls.
4. The live replacement facts are cost `207` with algebra
   `2*35 + (2*11 + 2*37 + 30) + 11 = 207`, 22 physical sources over logical
   segments `0..22` with segments `0` and `19` sharing BP, live segment `21`,
   rejected fresh segment `23`, and repeated-read positions `0` and `15` from
   producing instruction positions `0` and `1`.

Trigger and evidence:

The exact-commit audit of R1-R1 candidate
`3a2b47261ba6a15829a3160a7fce352b62c88380` found its Lean theorem and manifest
consumer sound but found retired current facts across live artifact, paper,
roadmap, review-packet, and current-digest surfaces. The candidate worklog
claimed those values remained only in historical records, while
`scripts/claim_drift_scan.ps1 -Strict` exited successfully with 746 hits and no
strict failure. The policy had marked `76` and the 20-source manifest as current
and did not classify the stale fresh-segment or trace-position fixtures.

Rejected alternatives:

- Rely on a worker's repository-wide search transcript without checking the
  policy classifier and its allowances.
- Ban the retired literals everywhere, which would corrupt frozen audit and
  design history.
- Add one broad `docs/internal` exception, which would also exempt the live
  final roadmap and current claim policy.
- Repair prose alone while leaving the scanner blind to the reproduced miss.

Consequences:

- A docs-only repair cannot report a clean current surface while these exact
  retired formulations remain live.
- Frozen historical evidence remains readable and truthful.
- The strict policy is a lower-bound consistency check; coordinators still
  reconstruct source theorem identities and semantics independently.
- No Lean proposition, payload bit, proof field, modeled tick, trace event, or
  runtime behavior changes.

Evidence:

- `docs/internal/CLAIM_DRIFT_POLICY.json` and `.md`.
- Named `r1r1-3a2b472-*` reject and current-value control fixtures in
  `scripts/claim_drift_policy_regression.ps1`.
- Exact rejected candidate
  `3a2b47261ba6a15829a3160a7fce352b62c88380`.

Publication-facing significance:

The artifact's numeric cost, physical-source universe, freshness witness, and
trace-position provenance are reviewer-visible claims. The strict live-versus-
historical boundary prevents obsolete but once-valid facts from surviving a
submission freeze under a green consistency gate.

## WDD-20260718-006: worker write scopes include workflow-sensitive companions

Status: Accepted.
Date: 2026-07-18.
Scope: worker-prompt construction, write-scope preflight, and strict workflow-
decision evidence.

Decision:

1. Close transitive write scope before a prompt is marked `READY_TO_SEND`.
2. If a write prompt may edit `scripts/gate.ps1`, require
   `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` in the same declared write
   scope. This applies even when the gate edit is comment-only because the
   strict decision checker intentionally treats the gate as process-sensitive.
3. Enforce the relation in `worker_prompt_preflight.ps1`, document it in the
   worker template and coordinator skill, and retain both failing and passing
   regression cases.

Trigger and evidence:

R1-R1 was assigned a stale-comment correction in `scripts/gate.ps1` while its
frozen write scope omitted the workflow-decision ledger. The worker completed
the substantive theorem repair, then correctly stopped when
`design_decision_check.ps1 -Strict` required a workflow entry it lacked
authority to write. A later coordinator scope amendment was safe but avoidable.

Rejected alternatives:

- Let workers silently expand their scope when a strict checker requests a
  companion file.
- Exempt comment-only gate edits from process-sensitive classification.
- Mention the companion only in prose without making prompt preflight reject
  the incomplete scope.
- Add every design ledger to every prompt regardless of changed paths.

Consequences:

- Gate-edit prompts arrive with enough authority to satisfy their known strict
  workflow evidence dependency.
- Workers still stop on any other unanticipated scope expansion.
- Narrow prompts that do not touch the gate gain no extra write authority.
- The rule changes no command, gate order, Lean proposition, payload data,
  modeled cost, trace, or runtime semantics.

Evidence:

- `.agents/skills/rmq-coordinator/SKILL.md`.
- `docs/internal/templates/WORKER_PROMPT.md`.
- `scripts/worker_prompt_preflight.ps1`.
- Named regressions `gate-strict-wdd-outside-write-scope-rejected` and
  `gate-strict-wdd-in-write-scope-accepted` in
  `scripts/worker_prompt_preflight_regression.ps1`.

Publication-facing significance:

This is workflow infrastructure. It prevents a mechanically predictable scope
block from interrupting a submission-hardening repair while preserving the
same strict audit trail for aggregate-gate changes.

## WDD-20260719-001: treat R1-R2 as public-claim synchronization, not roadmap change

Status: Accepted.
Date: 2026-07-19.
Scope: live current documentation, `docs/internal/RMQ_FINAL_ROADMAP.md`, and
the R1-R2 evidence ledger.

Decision:

The R1-R2 documentation repair synchronizes reviewer-facing descriptions to
already-checked R1-R1 source facts. Updating the workflow-sensitive final
roadmap is not a roadmap dependency, acceptance, workflow-command, command-
ordering, gate-semantics, or executable-behavior change.

Rejected alternatives:

- Leave the live roadmap stale because it is workflow-sensitive.
- Treat the prose repair as coordinator acceptance or a new roadmap node.
- Edit historical roadmap/audit chronology to remove old facts.

Consequences and evidence:

- The roadmap remains an accurate current reader surface without changing its
  dependency graph or acceptance ownership.
- Coordinator exact-commit re-audit remains required.
- The strict claim scan, topology lint, strict decision check, and committed
  range audit record this limited workflow disposition.

## WDD-20260719-002: derive exhaustive current-claim repair scope from one registry

Status: Accepted.
Date: 2026-07-19.
Scope: current-claim policy, worker-prompt construction, and R1-R2 repair
auditing.

Decision:

1. Treat `docs/internal/CLAIM_DRIFT_POLICY.json`
   `currentFactSurfacePathRegex` as the canonical current-reader-surface
   registry for exhaustive synchronization tasks.
2. Include the reviewer-grade claim correspondence, family summary, and model
   adequacy packet in that registry.
3. Reject the exact stale current-route vocabulary preserved by rejected
   candidate `48147cbc67c6c01c4abcf2565f9b981adb5eacb8`: the accepted canonical
   trace is `readWord`-only, while three-constructor language is allowed only
   when accurately labeled compatibility or frozen history.
4. Require worker prompts claiming exhaustive current-surface synchronization
   to name the registry and inspect every matched tracked path before launch.

Trigger and evidence:

R1-R2 repaired every path in its hand-written 17-file scope and passed strict
claim drift, yet `artifact/CLAIMS.md`, `docs/PAPER_CLAIM_CORRESPONDENCE.md`, and
`docs/FAMILY_SUMMARY.md` retained the weaker three-constructor current-route
story. The policy omitted two of those authoritative surfaces and had no
event-vocabulary term for the included artifact row.

Rejected alternatives:

- Treat the weaker statement as sufficient because it remains logically true.
- Add only the three prose files to one repair prompt while leaving governance
  unable to reproduce the miss.
- Ban `wordRank` and `wordSelect` globally, which would corrupt accurate model
  definitions, compatibility surfaces, and frozen history.
- Continue maintaining an unrelated prompt-local surface list and scanner list.

Consequences and evidence:

- `claim_drift_policy_regression.ps1` freezes the exact rejected candidate
  patterns plus current readWord-only and compatibility-labeled controls.
- `worker_prompt_preflight.ps1` rejects an exhaustive synchronization prompt
  that does not name the canonical registry.
- Coordinators must still reread source theorems and every matched current
  surface; scanner success remains a lower bound rather than semantic proof.
- No Lean proposition, payload, modeled cost, trace, or runtime behavior
  changes.

Publication-facing significance:

The paper claim map and family summary are authoritative reviewer navigation
surfaces. Keeping them in the same closed inventory as the artifact and theorem
map prevents an obsolete but weaker execution vocabulary from surviving a
submission freeze under a green scanner.

## WDD-20260719-003: attest the closed current-surface set before worker launch

Status: Accepted.
Date: 2026-07-19.
Scope: exhaustive current-claim prompt construction, write-scope closure, and
claim-drift vocabulary coverage.

Decision:

1. Before an exhaustive current-surface prompt becomes `READY_TO_SEND`, the
   coordinator records the exact base-derived registry match count, complete
   inspected path set, and expected repair paths in the prompt artifact.
2. `worker_prompt_preflight.ps1` independently reconstructs the registry from
   the exact worker base, rejects count/path-set disagreement, and rejects any
   declared repair path absent from write scope.
3. The current-event vocabulary policy rejects the exact README paraphrases
   found at governed base `a835720ddae8816727febb16c636eee4a5f57076`, including
   `payload read, word-rank, or word-select` and `payload read or bounded word
   primitive`, unless the same line accurately labels compatibility or the
   current readWord-only route.

Trigger and evidence:

R1-R3 received a prompt that named `currentFactSurfacePathRegex` but delegated
the first complete enumeration to the worker. The worker correctly stopped
clean before editing when registered `README.md` contained a required repair
outside its write scope. The coordinator rule already required pre-launch
inspection, but the structural preflight accepted an unattested instruction to
inspect later, and policy version 16 did not match the README paraphrase.

Rejected alternatives:

- Treat a clean worker scope stop as adequate recurring behavior.
- Add only `README.md` to this task without making future inventory evidence
  mechanically replayable.
- Grant every documentation worker blanket repository write access.
- Ban all mentions of word-rank/select primitives, including accurate model,
  component, compatibility, and historical descriptions.

Consequences and evidence:

- Exhaustive prompts carry a reproducible closed read set and a narrower owned
  repair set; workers still stop on genuinely new semantic discoveries.
- Named prompt regressions reject an unattested inventory and an expected
  repair outside write scope, while an exact counted/path-complete prompt
  accepts.
- Named claim-policy regressions reproduce the R1-R3 README spellings and keep
  an explicitly compatibility-labeled weaker-story control accepted.
- This changes no Lean proposition, payload, modeled cost, trace, machine, or
  runtime behavior.

Publication-facing significance:

README is the first reviewer navigation surface. Requiring its presence in the
same pre-launch closed inventory as the paper map and artifact prevents a true
but weaker compatibility story from surviving under a nominally exhaustive
submission-freeze repair.

## WDD-20260719-004: require theorem identity for strong current claims

Status: Accepted.
Date: 2026-07-19.
Scope: public-claim attribution, claim-drift policy, and completed-worker
failure-mode feedback.

Decision:

1. A current registered publication surface that states the strong
   `readWord`-only property must name the exact public theorem
   `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`.
2. `CLAIM_DRIFT_POLICY.json` records this as a structured file-level required
   attribution rather than another same-line vocabulary exception.
3. The strong alias remains distinct from the generic execution story, the
   weaker three-constructor compatibility alias, and the construction-facing
   capstone. Those declarations may still be cited for their actual checked
   propositions, but cannot be the sole identity beside the stronger claim.

Trigger and evidence:

Rejected R1-R3 candidate `bad14d0f1f7561f5f4200c19259a4ae5c8375499`
passed the line-oriented strict scanner after synchronizing four surfaces, yet
seven registered current documents still stated the strong fact without naming
its theorem. Five also attributed that fact to a weaker theorem or capstone.
The worker's closed inventory therefore confused truth of a separate theorem
with membership of that proposition in the declaration cited by the prose.

Rejected alternatives:

- Accept the prose because the strong property is true elsewhere in the same
  Lean module.
- Add more same-line negative vocabulary patterns, which cannot reliably
  connect a multi-line claim to its cited declaration.
- Ban the weaker declarations from public documents, which would erase useful
  and accurate compatibility and construction structure.
- Require every current document to reproduce the full Lean proposition.

Consequences and evidence:

- Policy version 18 adds a file-level `requiredAttributions` contract and the
  production scanner enforces it in strict mode.
- Named regressions `r1r3-bad14d0-*` reproduce all seven missing-identity
  surfaces; strong-alias and accurately labeled weaker-story controls remain
  accepted.
- This is a necessary tripwire, not semantic proof. Coordinators and auditors
  must still compare each sentence with the actual theorem type and repair
  false attribution rather than merely inserting the required name elsewhere.
- No Lean proposition, payload, proof data, modeled tick, trace, allocation,
  or runtime behavior changes.

Publication-facing significance:

Reviewer navigation must identify which checked theorem actually carries a
headline conjunct. This prevents a true project-level fact from being attached
to a weaker declaration in the theorem map, trust packet, or paper digest.

## WDD-20260719-005: separate semantic matrix evidence from cell placement and upper-bound syntax from attainment

Status: Accepted.
Date: 2026-07-19.
Scope: completed-worker proof gates, external-audit reconstruction, and audit
prompt engineering.

Decision:

1. Auditors enumerate the real frozen IDs and reconstruct each row from every
   evidence location explicitly allowed by the matrix schema. A blank cell or
   coordinator-owned `Open` status is not independently a blocker.
2. Appended evidence remains untrusted until its proposition, consumer, object
   identity, executable result, and anti-vacuity obligation are checked.
3. Tightness, attainment, and impossibility of a smaller cost bound require an
   equality/lower-bound witness or checked counterexample/negation on the same
   reachable object. A direct proof of `cost <= K` proves only that upper bound.

Trigger and evidence:

B7 target `6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25` promoted a direct
`cost <= 33` proof to the statements that 33 was attained and the old 30 bound
was unprovable. A08 report `1bc6b3597b97720c5c5dad0a2e87277cf28fd7ea`
correctly challenged that promotion, but separately rejected 24 rows from
blank cell placement and `Open` status, named nonexistent row IDs, and did not
reconstruct the row-keyed append-only evidence.

Rejected alternatives:

- Treat proof-term shape or absence of transitivity as a semantic lower bound.
- Require every frozen matrix to rewrite table cells after freeze, which would
  defeat append-only evidence designs and confuse worker evidence with
  coordinator acceptance.
- Accept append-only prose at face value merely because its row ID is present.
- Repair only the A08 report without making the two general failure patterns
  durable.

Consequences and regression evidence:

- `B7-UPPER-BOUND-IS-NOT-ATTAINMENT` rejects the exact 6ad4198 evidence pattern
  while allowing accurately labeled upper-bound theorems.
- `A08-EVIDENCE-LOCATION-IS-NOT-EVIDENCE-ABSENCE` rejects the exact 1bc6b35
  row-count argument while still requiring substantive row-by-row evidence.
- Audit prompts and reports must use the protocol evidence tiers and actual
  frozen identifiers; process layout cannot substitute for mathematical or
  executable reconstruction.
- No Lean proposition, payload, proof-only field, modeled tick, trace,
  allocation, or runtime behavior changes.

Publication-facing significance:

Reviewers must be able to distinguish a certified upper bound from a witnessed
worst case and a missing proof from evidence recorded append-only. The rule
prevents both mathematical overstatement and audit rejection based only on
document layout.

## WDD-20260719-006: detect exhaustive current-surface contracts by semantics, not one phrase

Status: Accepted.
Date: 2026-07-19.
Scope: worker-prompt preflight, transitive documentation write scope, and the
B7-R1 repair chain.

Decision:

1. Treat a prompt as an exhaustive current-surface synchronization task when
   it names `currentFactSurfacePathRegex`, uses a stable
   `CURRENT-PUBLIC-SURFACES` acceptance ID, or requires every registered,
   governed, live, current, public, or documentation surface to agree.
2. Apply the existing exact registry-attestation gate to all such wordings:
   matched count, complete inspected path set, expected repair paths, and write
   ownership must agree with the exact worker base.
3. Keep the registry-derived read set distinct from the narrower repair set;
   this hardening does not grant blanket documentation write access.

Trigger and evidence:

B7-R1 prompt base `55e2b9ae3704a16129aaecc9c12f487aee5df12e`
required every governed/registered current surface to state the live B7 facts,
but its hand-written scope omitted five of the 18 paths matched by
`currentFactSurfacePathRegex`. The structural preflight passed because its
trigger recognized `CURRENT-SURFACE-SYNC` and one `every live ... surface`
spelling, but not the B7 acceptance ID or governed/registered variants. Worker
checkpoint `24a166c5959aa1cac52be6d0aeefb3e2811f056c` then stopped correctly
before implementation.

Rejected alternatives:

- Accept recurring clean scope stops as the normal discovery mechanism.
- Add only the five B7 paths without repairing the preflight trigger.
- Trigger on every occurrence of the word `current`, which would impose an
  exhaustive registry contract on unrelated prompts.
- Grant all documentation paths to every public-claim worker.

Consequences and regression evidence:

- `worker_prompt_preflight.ps1` recognizes the B7 stable ID, the registry field,
  and governed/registered exhaustive wording.
- Named regression
  `b7-governed-current-surface-wording-without-inventory-rejected` reproduces
  the missed launch pattern and requires the existing registry-attestation
  failure.
- Existing positive exact-inventory and accurately scoped weaker-task controls
  remain unchanged.
- No Lean proposition, payload, proof field, modeled cost, trace, allocation,
  runtime behavior, or public mathematical claim changes.

Publication-facing significance:

Submission-freeze repairs cannot silently omit current reviewer surfaces merely
because their prompts express exhaustiveness with different natural language.
The worker receives a closed evidence surface before editing, avoiding repeated
documentation-only repair loops and scope stops.

## WDD-20260719-007: public identity migrations close their Lean consumer surface before launch

Status: Accepted.
Date: 2026-07-19.
Scope: worker prompt preflight, transitive Lean/public write scope, and the
B7-R2 repair chain.

Decision:

1. A prompt that restores, renames, splits, or migrates a public theorem or
   historical identity must record an exact-base dependency-surface inventory:
   searched declarations, every directly inspected tracked consumer path, and
   expected repair paths.
2. The inventory covers direct Lean consumers, compatibility/headline aliases,
   validation guards, examples, and trust inventories. Every expected repair
   path must be owned before `READY_TO_SEND`.
3. The structural preflight rejects identity-migration prompts without this
   inventory and rejects any declared repair path not inspected or not in write
   scope. Semantic completeness remains coordinator-reviewed.

Trigger and evidence:

B7-R2 base `e23875542995ca31404567cba5b128c9271e861a` correctly closed all 18
registered current-document surfaces but omitted four direct consumers needed
by `REQ-B7R1-HISTORICAL-328-IDENTITY`:
`RMQ/Core/SuccinctFinalStoreParam.lean`,
`RMQ/Core/SuccinctFinalModelAdequacy.lean`,
`RMQ/Headlines/RMQCompatibility.lean`, and
`RMQ/Validation/SuccinctClassic.lean`. The worker reached a kernel-checked
exact-cost checkpoint and then stopped with substantive uncommitted work
because restoring the public 328 identity while separating the live 352 bound
would otherwise leave those consumers mislabeled or ill-typed.

Rejected alternatives:

- Treat another clean scope stop as normal discovery.
- Add only the four B7 paths without changing prompt policy.
- Grant proof workers blanket repository write access.
- Infer consumer closure from a source theorem build, which does not compile
  separate compatibility, validation, example, or trust roots.

Consequences and regression evidence:

- Named regression
  `b7r2-public-identity-migration-without-consumer-inventory-rejected`
  reproduces the missing-inventory launch pattern.
- Positive control
  `public-identity-migration-with-closed-consumer-inventory-accepted` retains a
  narrowly owned, explicitly inspected migration.
- This changes no Lean proposition, payload, proof-only field, modeled cost,
  trace, allocation, runtime behavior, or public mathematical fact.

Publication-facing significance:

Historical cost identities and live compatibility bounds must remain visibly
different checked objects throughout the theorem, headline, example, and
validator chain. Closing that chain before launch prevents a source-level
repair from leaving public descendants with contradictory names or numerals.

## WDD-20260719-008: replay selectors certify exact executions, not merely a nonempty fixture list

Status: Accepted.
Date: 2026-07-19.
Scope: executable acceptance replay, selector anti-vacuity, and bounded worker
verification for B7-R3 and later repair tasks.

Decision:

1. A frozen multi-case replay contract has one typed ordered registry whose
   entries contain the semantic and comparison fields acceptance actually
   cites. A literal expected-ID sequence plus uniqueness validation rejects
   missing, duplicate, extra, or reordered cases; a count alone is insufficient.
2. The executor returns its actual execution count. Default mode compares that
   count with the complete registry; a stable-ID selector must match and execute
   exactly one entry; unknown and zero-match selections exit nonzero.
3. The in-repository Lean harness remains child-free. External Lean/Lake stages
   carry positive observed-runtime deadlines, one owned process tree, failure
   classification, and cleanup; a quiet timed-out command is diagnosed before
   any changed-state retry.

Trigger and evidence:

The inherited B7 cost harness recursively ran fixture windows but had no stable
case identity or selector. Its empty recursive base returned success, so a
future filtered selector could execute zero cases and pass. B7-R3 replaces that
surface with `replayRegistry : List ReplayCase`, an exact 21-ID sequence,
de-duplication and pinned pre-cost checks, counted traversal, and `--case` /
`--fixture` controls. The final control run requires default `21/21`, known
`1/1`, and exit `4` for both an unknown ID and a zero-match fixture.

Rejected alternatives:

- Treat `registry.length = 21` as sufficient; a duplicate can hide a missing
  load-bearing case.
- Recompute historical pre-repair costs on the repaired implementation.
- Let a shell filter decide which Lean cases ran without receiving an executed
  count from the harness.
- Spawn compiler or replay children inside Lean, where the worker's external
  deadline and process-tree cleanup discipline would be obscured.

Consequences and regression evidence:

- Replay output reports selected and executed counts and validates exact
  answer, independent reference answer, route, post-cost, and disposition for
  every selected entry.
- The load-bearing leftmost interior-tie case has a stable ID and exact pre/post
  cost, while invalid and zero-interior controls remain explicit.
- Selector failure is an executable verdict, not prose evidence. Missing or
  duplicate IDs fail before any query is credited.
- This changes executable verification structure only; payload bits, proof
  fields, modeled query ticks, trace semantics, Lean runtime claims, and paper
  mathematics remain separate.

Publication-facing significance:

An artifact replay claim must identify exactly which cases executed and why
they are semantically load-bearing. Exact registry and selector verdicts make
the comparison reproducible without elevating wall-clock behavior to a theorem.

## WDD-20260719-009: exact replay preparation is cached by typed fixture identity

Status: Accepted.
Date: 2026-07-19.
Scope: B7 exact-registry execution cost and bounded final-candidate replay.

Decision:

1. Exact-registry traversal remains the sole source of case order and semantic
   expectations, but theorem-backed `PreparedInput` construction is performed
   once per distinct typed `FixtureId` selected by that traversal.
2. The executor carries a cache keyed only by `FixtureId`; every case still
   computes and checks its own answer, independent List answer, route, post
   cost, and disposition from the cached prepared object.
3. Successful output checks that the cache contains exactly the number of
   distinct selected fixture IDs. Default replay therefore requires 21
   executed cases and six prepared fixtures; a one-case selector requires one
   of each.

Trigger and evidence:

Diagnosis of a final default replay that accumulated about 1058 seconds of
harness CPU and crossed its positive 20-minute deadline found two independent
runtime-category mistakes. First, the exact-registry implementation called
`prepareInput` inside `reportReplayCase`, repeating the same pure
Cartesian-shape and payload construction for every window; the prior
fixture-based harness had deliberately prepared once per fixture. Second, the
new value-dependency proof had exported closed size-3469 witness values, which
DD-20260719-004 moves into proof-erased theorem-local lets. This workflow
decision governs the separate registry-sharing issue rather than attributing
the whole timeout to it.

Rejected alternatives:

- Raise the deadline and repeat the unchanged opaque command.
- Drop, reorder, or summarize registry cases to shorten the replay.
- Treat 21 individually selected cases as a substitute for exercising default
  ordered traversal.
- Cache by an untyped string or by query result, which could become a routing
  oracle rather than construction reuse.

Consequences and regression evidence:

- `ReplayPreparedCache` stores only `(FixtureId, PreparedInput)` pairs;
  `reportReplayCasesCached` still recurses over the exact selected registry.
- `exactPreparedFixtureCount` is part of the executable success verdict, not a
  prose observation.
- After DD-20260719-004 removed the independent import-time regression, final
  default replay reported `selectedCases=21`, `executedCases=21`, and exactly
  six prepared fixtures in 29.158 seconds; the known one-case selector reported
  one prepared fixture in 282 ms.
- This changes verification runtime only. It does not change a fixture,
  expected answer, route, modeled tick, trace, payload bit, proof field,
  theorem proposition, or public mathematical claim.

Publication-facing significance:

Exact artifact replay should be complete and bounded without confusing
repeated host-language reconstruction with the modeled query cost. Typed
fixture sharing preserves the case contract while keeping runtime evidence in
its proper category.
## WDD-20260719-010: probe executable startup before full replay and certification

Status: Accepted.
Date: 2026-07-19.
Scope: proof-worker verification ordering for changed executable import
closures.

Decision:

1. When a replay executable imports changed Lean modules, verification runs a
   bounded startup/shape smoke test, then one known exact selector, then the
   complete registry.
2. An unexpectedly slow smoke test triggers inspection of import-time
   initialization and proof-only closed data before any deadline increase.
3. Broad trust, policy, topology, and aggregate certification follows the
   successful replay controls and content freeze rather than preceding them.

Trigger and evidence:

B7-R3 checkpoint `024e33eb922355bb811ed20191215c5992328ebc` exported closed
size-3469 address/store values used only by one corruption theorem. The first
full replay crossed a 20-minute deadline; after fixture caching, a shape-only
size-5 probe still crossed 120 seconds. Candidate `879edb0a3c61d44a7a20cee0026e96a121666791`
moved those expressions into theorem-local `let`s. The identical smoke probe
then took about two seconds and the 21-case replay about 29 seconds. The
worker's retrospective identifies roughly 53--62 minutes of avoidable or
deferrable verification, chiefly full-campaign timeouts and certification run
before replay closure.

Rejected alternatives:

- Increase full-replay deadlines without isolating startup.
- Treat modeled query ticks as an explanation of Lean initialization time.
- Run the full registry as the first observation after every executable import
  change.
- Certify broad public/trust surfaces before the executable acceptance control
  is known to terminate on frozen content.

Consequences and regression evidence:

- `COMPLETION_GATE.md` and `WORKER_PROMPT.md` require the smoke/selector/full
  order for changed replay imports.
- Named regression `B7R3-STARTUP-SMOKE-BEFORE-FULL-REPLAY` uses `024e33e` and
  rejects a ledger whose first executable observation is the full registry or
  whose broad certification precedes replay closure.
- Legitimately long full campaigns remain allowed once startup is isolated and
  their deadlines use observed evidence.
- No Lean proposition, payload bit, proof field, modeled tick, trace, store,
  or public mathematical claim changes.

Publication-facing significance:

Artifact evidence remains complete without confusing proof-witness
initialization or repeated host construction with the charged RAM cost model.

## WDD-20260719-011: fail closed on retired current costs and unclassified design paths

Status: Candidate decision; coordinator acceptance pending.
Date: 2026-07-19.
Scope: claim-drift policy, design-decision classification, worker certification
commands, aggregate-gate ordering, and replayable workflow regression.

Decision:

1. The current-cost claim category treats 76, 142, and 207 as retired tokens
   whenever a registered current-fact line presents one as current, canonical,
   principled, uniform, modeled, query, charged-trace, trace-length, or
   Costed.cost. The current 210 token remains accepted.
2. CLAIM-HISTORY-A07-COST is a controlled trailing marker. It admits a single
   historical clause and the two existing truthful compound shapes:
   current-210 followed by retired comparison, or distinctly named live
   compatibility 352 followed by retired comparison. A marker or history word
   in an unrelated clause cannot authorize a stale-current statement.
3. Design classification is opt-out/default-sensitive. The narrow neutral
   classes are the two decision records themselves, internal worklogs and
   acceptance matrices, audit reports, historical digests other than the
   current publication digest, and the digestion evidence log. Workflow roots
   are .agents, .codex, .github, scripts, AGENTS.md, and docs/internal. Lean
   remains code-sensitive under any root; every other non-neutral path defaults
   to code-sensitive. Thus a previously unknown path cannot pass merely because
   its name was absent from an enumeration.
4. Strict design certification requires a resolvable Base and never falls back
   to worktree-only inspection. Production retains symbolic-ref compatibility
   for CI, while governed worker prompts and the proof completion gate require
   the task's exact 40-character base commit. Omitting Base is allowed only in
   deliberate non-strict local-worktree advisory mode.
5. Both production regressions bound every external Git or PowerShell child,
   classify timeouts as failures, clean the owned process tree, and run a cheap
   sleeper control. The claim regression also pins its exact ordered fixture
   registry and verdict totals and proves duplicate, missing, and verdict-drift
   mutations fail.
6. Aggregate ordering is: project-skill and worker-prompt preflight
   regressions; the design-decision production regression; broad builds and
   trust checks; the existing claim-policy regression; the strict repository
   claim scan; topology checks; and final diff hygiene. Each new or existing
   policy regression is invoked exactly once and its exit is checked
   immediately.

Trigger:

The governed claim regression still accepted "The current principled
charged-trace bound is 207" after the live bound moved to 210. Separately,
design_decision_check.ps1 named sensitive paths one by one and a strict
invocation without Base could report no changed files on a clean committed
branch. Both failures let omission from a hand-maintained list or command
argument masquerade as certification.

Options considered and rejected:

- Add 207 to one sentence fixture but retain the broad marker-word allowance.
  That leaves an unrelated historical clause as a bypass.
- Continue appending new Lean, documentation, validation, and script names to
  the sensitive arrays. The next invented path would recreate the same hole.
- Treat every docs/internal path as neutral evidence. That would exempt live
  workflow policy, templates, roadmaps, and scanners.
- Require production Base to be a literal SHA only. Existing CI intentionally
  passes origin/base or HEAD~1; resolvability is the production compatibility
  boundary, while emitted governed prompts pin exact SHAs.
- Reimplement either classifier inside its regression. Divergent copied logic
  could make both suites green.
- Rely on the aggregate gate alone. Isolated production regressions provide
  faster exact failure surfaces and make child deadlines and restoration
  replayable.

Consequences:

- A new non-neutral repository path is design-sensitive by default.
- Decision/evidence/history records remain nonrecursive and can record the
  required rationale without demanding another decision entry.
- Strict branch evidence is base-relative and nonvacuous; local no-Base advice
  remains available but cannot be presented as certification.
- Historical 76, 142, 207, and 328 evidence and distinctly named compatibility
  352 remain truthful, while current-surface use of 207 becomes gate-failing.
- This changes workflow policy only. It changes no Lean proposition, public
  theorem identity, payload bit, proof field, modeled tick, machine state,
  runtime behavior, or measured-performance claim.

Regression evidence:

- design_decision_check_regression.ps1 development run: 10 production
  rejections and 8 production acceptances across isolated Git repositories,
  including missing Base, unresolvable Base, held-out RMQ and validation Lean,
  workflow script, public doc, unknown path, missing/correct decisions,
  nonrecursive evidence/history, non-strict local mode, a drive-qualified
  Windows repository root, sleeper timeout cleanup, and caller-tree
  restoration; exit 0 in 34 seconds.
- claim_drift_policy_regression.ps1 pins 94 ordered sentence fixtures and 15
  ordered path/context fixtures before
  final certification, including the retired-207 category, current-210 and
  historical/compatibility controls, marker-bypass mutations, inherited
  attribution and topology fixtures, and exact-registry mutations.
- Final command outcomes and durations are recorded in
  docs/internal/P1_POLICY_HARDENING_WORKLOG.md.

Publication-facing significance:

Submission-facing consistency no longer depends on remembering the last cost
numeral or the next sensitive filename. Reviewers can distinguish live 210
from frozen cost history, and future branches must carry durable design
rationale before their new paths can pass strict certification.

## WDD-20260719-012: neutral evidence paths cannot shadow code or current claims

Status: Accepted.
Date: 2026-07-19.
Scope: classifier completion evidence, default-sensitive design coverage, and
the P1 repair chain.

Decision:

1. A path classifier that defaults repository changes to design-sensitive may
   opt out only files whose role is constrained, not every file placed under a
   nominally neutral directory.
2. Code-bearing extensions remain code-sensitive under audit-report,
   worklog, history, and digest roots. A neutral-path test must run before
   acceptance and must not take precedence over code identity.
3. Broad evidence/digest roots must not automatically exempt a newly named
   current-looking public surface. Neutral history needs a constrained naming
   or registry rule, and the production regression must exercise a current-like
   counterexample.
4. Claim-policy mutation campaigns must reproduce an actual stale registered
   surface, including line-boundary variants, rather than relying only on
   single-line paraphrases.

Trigger and evidence:

P1 candidate `18d7661898c262ab79c5b87bc24d07bb90498969` declared that Lean
remained code-sensitive under every root and that new public paths defaulted
sensitive. Its production checker nevertheless accepted both
`docs/internal/audit_reports/P1NeutralBypass.lean` and
`docs/digests/PROJECT_DIGESTION_CURRENT_V2.md` as neutral because directory
opt-outs ran first. Its strict claim scan also returned zero failures while
the registered `docs/PUBLICATION_STRATEGY.md` split “current theorem” and `207`
across adjacent lines. The worker's green fixture sets omitted all three exact
counterexamples.

Rejected alternatives:

- Treat directory placement as sufficient evidence of role.
- Repair only the two example paths without changing completion discipline.
- Accept the green enumerated regressions as category completeness.
- Run the expensive unchanged fixture suite again after the production
  counterexamples had already falsified the candidate.

Consequences and regression evidence:

- Named regression `p1-neutral-evidence-path-cannot-shadow-code-or-current-surface`
  requires production rejection of the audit-report Lean injection and the
  current-looking digest injection while preserving legitimate Markdown audit
  reports and explicitly historical digests.
- Named regression `p1-registered-current-cost-cross-line-207-rejected`
  reproduces the exact `PUBLICATION_STRATEGY.md` line-boundary defect through
  the production claim scanner.
- The proof-sprint completion gate now requires both neutral-path boundary
  mutations for opt-out/default-sensitive classifiers.
- No Lean proposition, payload bit, proof field, modeled tick, trace, store,
  runtime behavior, or public mathematical claim changes.

Verification:

- The two production design-check probes exited zero on the rejected P1
  candidate, reproducing the failure and restoring the exact audit tree.
- The strict production claim scan exited zero on the candidate while the
  registered stale two-line claim remained present.
- Governance skill preflight and exact diff checks must pass before this
  decision is used to launch the repair.

Publication-facing significance:

Current cost statements and design-sensitive proof/tooling changes cannot
escape review merely by wrapping across lines or by being stored under an
evidence-labelled directory.
