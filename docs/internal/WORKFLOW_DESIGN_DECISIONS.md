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
WDD-20260710-002, and WDD-20260711-001 through WDD-20260711-002 govern the
current audit-context, obstruction, skill-context, lifecycle, scout, durable
read-only-report, model-routing, and proof-completion policies. Earlier
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
- `.agents/skills/rmq-audit/SKILL.md`
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
- `.agents/skills/rmq-audit/SKILL.md`.
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

Status: implemented candidate; coordinator audit pending.
Date: 2026-07-13.

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

Status: implemented candidate; coordinator audit pending.
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
  canonical execution/route/query role, `2^128` (spaced or unspaced), and
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
