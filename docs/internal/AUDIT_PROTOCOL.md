# Audit Protocol

This document fixes the repo-local meaning of "audit" for ADD work. It is
internal workflow guidance; Lean, Lake, and the checked theorem statements
remain the proof artifacts.

## Definition

An audit is a falsification-oriented review of a specific target against
explicit evidence and explicit acceptance criteria.

Every audit should answer:

- What exact claim, branch, theorem surface, document, or worker report is in
  scope?
- What would make the target unacceptable?
- Which checked source, command output, or public claim supports the verdict?
- Which objections were considered and rejected as stale, out of scope, or
  already answered by source evidence?
- What is the next theorem-shaped, document-shaped, or artifact-shaped action?

An audit may recommend work, block a merge, or clear a branch for integration.
It does not add trust beyond the checked sources and commands it cites.

## Evidence Classes

- Kernel evidence: checked Lean theorem statements, public aliases, import
  roots, and axiom-check output.
- Execution evidence: Lake builds, executable validators, artifact scripts,
  benchmark harnesses, and their observed outputs.
- Source evidence: exact files, theorem names, diffs, line references, and
  commits.
- Claim evidence: README, artifact docs, paper theorem maps, and public
  limitation documents.
- Process evidence: worker reports, digests, review notes, and sanitized
  transcript excerpts. Process evidence can explain how a decision was reached,
  but it is never proof of a mathematical or implementation claim.

Private model traces or hidden reasoning are not stable project evidence and
must not be treated as public artifact evidence.

## Claim Evidence Tiers

When an audit discusses a positive claim, it should name the strongest evidence
tier that actually supports it:

- Kernel theorem: checked Lean theorem or alias, with file and theorem name.
- Model theorem: checked theorem about the explicit RAM/store/trace model, not
  Lean runtime.
- Executable validation: checked executable or `lake exe` run that tests the
  relevant definitions, without upgrading the result to a theorem.
- Artifact evidence: reproducible command output, CI log, timing, or bundled
  artifact record.
- Process evidence: audit logs, design decisions, worker reports, and ADD
  provenance.

Process evidence can justify why the team looked somewhere. It cannot justify a
mathematical or executable claim by itself.

## Audit Modes

- Branch audit: compare a branch against its intended base, verify owned
  changes, inspect stale or unrelated edits, run the relevant gates, and decide
  whether it is merge-ready.
- Theorem-surface audit: trace public aliases to source theorems, inspect
  assumptions, constants, imports, and axiom status, and verify that theorem
  names match theorem strength.
- Claim-drift audit: compare public-facing prose with the checked theorem
  truth, especially numerical constants, cost-model wording, novelty language,
  AI/ADD provenance, and artifact readiness.
- Worker-stop audit: decide whether a worker stopped at a genuine obstruction
  or merely stopped at an honest partial checkpoint when local progress remains.
- External-auditor audit: provide a self-contained packet, require concrete
  citations, and translate accepted findings into precise repo targets.
- Literature/parity audit: compare the project against current external
  precedent, record search scope, qualify novelty language, and separate
  reviewer pattern-matching gaps from theorem gaps.

## Severity

- P0: the checked proof or trust story is invalid, a public theorem is false, or
  a merge would corrupt the artifact.
- P1: a public claim materially overstates the checked state, a required gate
  fails, or a theorem surface is weaker than its public name suggests.
- P2: reviewer-friction, maintainability, import-surface, or documentation
  issues that do not falsify the current theorem story.
- P3: polish, clarity, naming, or presentation improvements.

## Required Report Shape

Use this shape unless the user asks for a different format:

1. Scope: branch, commit, base, files, theorem surfaces, and prompt.
2. Verdict: merge-ready, merge-ready with follow-up, blocked, or needs another
   worker pass.
3. Findings: ordered by severity, each with evidence and an actionable target.
4. Stale or rejected objections: audit claims that no longer apply, are
   unsupported, or are answered by checked source.
5. Verification: commands run, commands skipped, and why.
6. Next action: the best next prompt, patch, theorem target, or artifact step.

For review-style requests, lead with findings. For coordinator planning, lead
with the current frontier and the next highest-leverage target.

## Coordinator Rules

- Fetch or otherwise verify the relevant heads before judging branch freshness,
  unless the user explicitly asks about a fixed local snapshot.
- Treat external audits as evidence, not commands. A true finding becomes a
  theorem-shaped, docs-shaped, or artifact-shaped target.
- Do not accept "honestly caveated but weak" as a final state when a stronger
  local repair is available.
- Keep payload bits, proof-only fields, model-level cost ticks, executable Lean
  runtime, and compiled performance in separate buckets.
- When a branch changes a design decision, require an update to
  [`DESIGN_DECISIONS.md`](DESIGN_DECISIONS.md) or an explicit report that no
  design-decision update was needed.

## External Auditor Packets

When sending work to an external auditor, include:

- the branch, commit, and intended base;
- the exact claim or theorem surface to inspect;
- the files and docs that form the public/trust surface;
- the commands that should pass and any platform caveats;
- known non-goals and stale objections;
- the required report format and severity scale;
- a request to cite source, theorem, or command evidence for every finding.

External auditors should not need private chat history to evaluate a checked
claim. If project history matters, provide a short sanitized digest instead of
raw transcript dumps.

## Skill Boundary

This document is the portable source of truth for audit behavior. If the
workflow stabilizes further, it can be turned into a dedicated Codex skill for
auditors, but the skill should point back here rather than inventing a parallel
definition.
