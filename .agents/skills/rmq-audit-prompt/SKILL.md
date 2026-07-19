---
name: rmq-audit-prompt
description: Use to engineer independent external-auditor prompts and evidence packets for RMQ. This is a coordinator-side prompt-authoring skill, not the skill used by audit workers. Select fresh-blind, continuation, longitudinal, or whole-frontier mode and fill the repo audit template from exact commits and source evidence.
---

# RMQ External Audit Prompt Engineering

Use this coordinator-side skill to prepare an external audit prompt and evidence
packet. The auditor follows the resulting prompt and `AUDIT_PROTOCOL.md`; the
auditor does not need this prompt-authoring skill. The coordinator still audits
the report, integrates branches, updates the roadmap, and engineers worker
prompts.

## 1. Choose Independence Mode

Read `docs/internal/AUDIT_PROTOCOL.md` and choose:

- **fresh blind delta** for an independent milestone/merge gate;
- **continuation** for one correction loop on that auditor's findings;
- **longitudinal architecture** for periodic milestone comparison;
- **whole frontier** for release or trust-boundary review.

Default to low history and high evidence. Do not give a fresh auditor prior
verdicts or full transcripts. A commit alone is not enough: name base, target,
scope, design intent, acceptance criteria, load-bearing surfaces, and checks.

Keep model/mode recommendations outside the pasted prompt as coordinator launch
metadata.

## 2. Build The Packet

Use `docs/internal/templates/AUDIT_PROMPT.md` and, when useful,
`scripts/make_audit_packet.ps1`. Include:

- auditor handle and audit mode;
- exact base/target commits and branch;
- active roadmap node and intended change;
- relevant theorem aliases, source theorems, trust/claim docs, and decision
  entries;
- required commands and platform caveats;
- explicit non-goals and rejection conditions;
- durable report path under `docs/internal/audit_reports/`.

For claim wording, also read
`docs/internal/CLAIM_DRIFT_POLICY.md`.

## 3. Demand Adversarial Evidence

Require the auditor to test literal truth and the spirit of the roadmap target.
Specifically look for technically correct wrappers, renamed caveats, decorative
reads, proof-only answers, uncounted storage, synthetic events, or valuable work
that advances a different goal.

Also ask the auditor to reconstruct the requirement-to-evidence matrix from
frozen IDs and exact requirements. In fresh-blind mode, withhold the worker
verdict and narrative. Require checked theorem types and expanded object
arguments; a declaration-name inventory is not evidence. Treat a completion
report's own "remaining risk", "reviewer should ask", or "next consumer must
prove" language as presumptive evidence of incomplete closure.

For combined public claims, require an explicit identity chain showing that
space, execution, provenance, and machine facts concern the same construction.
For whole-machine claims, inventory every segment in the physical embedding and
check that one query-independent width/capacity is related to input size. Audit
claim-drift policies and allowlists rather than treating green output as ground
truth. For machine-backed work, also require backward value dependency and
actual address-capacity checks, including tiny and dead/sentinel cases.

For semantic liveness, source coverage, ownership, or refinement claims,
expand the definitions and run counterfactual mutation checks: add a dead
source, remove an operationally used source, replace a predicate with a
tautology, and assign a consumer label without an evaluator edge. Require the
auditor to identify which checked theorem rejects each applicable mutation.
Require the auditor to quote the accepted predicate `P` and rejected mutation
predicate `Q`, including guards and quantifiers, and demand either predicate
identity or a checked `P -> Q` bridge. Explicitly compare component may-read,
successful read, top-level reachability, and actual emitted occurrence.

For trace provenance, require the auditor to state whether the theorem retains
only event-value membership or also occurrence position, multiplicity,
producing instruction, folded pre-state, local occurrence, and invocation
parameters. `List.Mem` alone is not occurrence-level evidence, and proof-term
construction does not compensate for information erased from the proposition.
For returned-value or routing claims, inspect that projection specifically;
aggregate trace inequality may be caused only by the log, and a singleton
witness does not establish a universal dependency claim. For guarded public
wrappers, compare the validity domain of every conjoined execution and adequacy
field, including invalid ranges; reject raw adequacy left unconditional inside
an otherwise guarded public record.

Positive evidence tiers are kernel theorem, model theorem, executable
validation, artifact evidence, then process evidence. Process reports do not
prove mathematical or executable claims.

Do not inherit the worker's statement that a residual theorem is "strictly
stronger" or optional. The auditor maps it independently to the frozen
requirements and inherited invariants.

## 4. Require A Useful Report

Ask for findings first, P0 through P3, with exact source/theorem/command
evidence, stale objections, verification outcomes, roadmap alignment, and the
best next target. Report-only auditors may write exactly the assigned report
file; proof/source files remain read-only.

After the report text is complete, rerun every report-sensitive final-tree
check before committing. At minimum run strict claim drift, strict design
decision checking when applicable, and `git diff --check` against the tree that
actually contains the report. A gate run from before the report edit is not
evidence that the report commit passes. When a report must discuss a forbidden
claim as a counterexample, paraphrase it or use an explicitly allowed
historical/quoted context rather than silently expanding an allowlist.

Afterward the coordinator verifies the report, records dispositions, updates
the worker lifecycle/roadmap, and engineers the next prompt set.
