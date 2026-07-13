# Audit Protocol

This document fixes the repo-local meaning of an ADD audit. Lean, Lake, checked
theorems, and reproducible commands remain the evidence; an audit adds no trust
by itself.

## Definition

An audit is a falsification-oriented review of an exact target against explicit
acceptance criteria. It identifies the target and base, rejection conditions,
evidence for each finding, stale objections, and the next concrete action.
Auditors test both literal correctness and design intent. Work that is true but
preserves the abstraction defect the active roadmap is meant to remove is not
successful completion.

For semantic liveness, coverage, ownership, dependency, refinement, or public
composition claims, falsification includes expanding load-bearing definitions
and attempting counterfactual mutations. Examples are adding a dead manifest
source, assigning a consumer without an evaluator edge, ignoring a decisive
read value, or mixing guarded and unguarded executions. The report names the
checked theorem that rejects each applicable mutation. Aggregate-record
inequality is not evidence about the returned value when only a log field is
forced to change, and a concrete witness does not close a universally
quantified dependency claim. A public record cannot leave raw adequacy
unconditional while guarding its other execution fields.

## Evidence Tiers

1. kernel theorem;
2. theorem about the explicit model/store/trace;
3. executable validation;
4. reproducible artifact or CI evidence;
5. process evidence such as audit reports and design logs.

Process evidence explains decisions. It does not prove mathematics, model
adequacy, or executable behavior. Hidden reasoning and private model traces are
not public artifact evidence.

## Audit Modes

### Fresh Blind Delta

Default for merge gates and major milestones. Use a new session with low
history and high evidence. Supply the exact base and target commits, frozen
acceptance IDs and verbatim requirements, an audit packet, and load-bearing
public/trust surfaces. Do not supply the worker's verdict, narrative, prior
verdicts, or findings unless a closed source fact is needed to avoid a known
stale objection.

Inspect the delta plus the public surfaces it can affect, not the whole
repository by default.

### Continuation

Use the same auditor for one correction loop on its own findings. Supply the
new commit, old audited commit, accepted findings, and claimed fixes. This is
token-efficient but not an independent final gate.

### Longitudinal Architecture

Use a persistent auditor periodically to compare selected milestones, detect
accumulated architecture drift, and assess roadmap direction. It may know prior
history. It must not be the only release auditor.

### Whole-Frontier

Use for release candidates, stale-coordinator reconstruction, major
trust-boundary changes, or after several architecture milestones. Scope it with
the paper root and theorem map, not raw chat exports.

## Context Policy

The default is **low history, high evidence**, not zero context. A commit hash
alone is enough only when the auditor has the repo and the prompt also names
scope and acceptance criteria. A normal packet contains:

- target and base commit;
- frozen acceptance IDs and verbatim requirements;
- diff stat and changed-file list;
- active roadmap node and intended design change;
- relevant aliases, source theorems, trust docs, and decision entries;
- required commands and platform caveats;
- known non-goals.

Do not give a fresh auditor full transcripts or a previous report's conclusion.
Use a short source-grounded digest only when history changes the delta's
meaning.

Recommended cadence:

1. fresh blind audit at every public paper capstone, trust-boundary change,
   combined space/execution theorem, or roadmap-node closure;
2. same-session continuation for one correction pass;
3. fresh acceptance audit after material corrections;
4. longitudinal architecture review every two to four milestones.

## Severity And Verdicts

- **P0**: proof/trust invalidity or artifact corruption.
- **P1**: material claim overstatement, failed required gate, or misleading
  theorem surface.
- **P2**: roadmap misalignment, architecture/reviewer friction, missing tests,
  or maintainability risk.
- **P3**: polish and local clarity.

Verdicts: merge-ready, merge-ready with follow-up, blocked, or needs another
worker pass.

## Required Report

1. Scope: mode, auditor, base, target, surfaces, and acceptance criteria.
2. Verdict.
3. Findings ordered P0 to P3 with exact evidence.
4. Evidence tier for every positive claim.
5. Stale/rejected objections.
6. Commands run/skipped and outcomes.
7. Roadmap alignment in letter and spirit.
8. Best next target.
9. Durable report path.

## Coordinator Disposition

The coordinator verifies heads, audits the audit, reconstructs the frozen
acceptance matrix from source, and alone records `ACCEPTED`. It then integrates
or rejects the branch, updates roadmap/lifecycle state, and engineers the next
prompts.

Material reports live under `docs/internal/audit_reports/`. Report-only
auditors may write exactly one assigned report file; source files remain
read-only.

## External Packet Minimum

Use `scripts/make_audit_packet.ps1` plus task-specific material. Include base,
target, scope, design intent, load-bearing surfaces, frozen acceptance IDs and
verbatim requirements, checks, non-goals, severity scale, and report path.
Private chat history is optional process context, never a prerequisite for
checking a theorem claim. A fresh acceptance packet omits the worker verdict and
narrative.
