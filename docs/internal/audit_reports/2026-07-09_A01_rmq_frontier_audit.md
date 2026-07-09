# A01 RMQ Frontier Audit

Date: 2026-07-09

Auditor handle: `A01-rmq-frontier-audit`

Target: `origin/codex/add-audit-decision-log` at commit
`800b9b3a62623cdb2ac09f20ce61da55d8c0ad35`

Base/diff window: `2aec4d1..800b9b3`

Source: external auditor report returned in chat and stored by the coordinator.

Status: Process evidence. This report is not proof evidence; checked Lean
source, theorem statements, and reproducible commands remain the proof/artifact
evidence.

## Auditor Verdict

Paper-surface ready, with follow-up. The auditor reported no P0, P1, or P2
findings. The narrow paper root builds; audited public aliases trace to source
theorems of matching strength; axiom scripts pass with standard Lean axioms;
hygiene scans are clean; and public prose matches the checked truth on
`65585`, `196727`, `118`, `2^128`, supplied stores, footprint agreement,
model-vs-runtime wording, and ADD provenance.

## Findings Reported

### P3-a: Stale Trust Audit Packet Pointer

`docs/TRUST_AUDIT_PACKET.md` still oriented reviewers toward
`RMQ/Headlines.lean` as the most reader-facing RMQ surface and listed that
aggregate barrel first in the reading order. The rest of the paper/artifact
surface now routes reviewers through `RMQPaper` and `RMQ/Headlines/RMQ.lean`.

Coordinator disposition: accepted. The packet was updated to use the narrow
paper root and RMQ-only headline module.

### P3-b: README Digest Pointer Wording

`README.md` described `docs/digests/PROJECT_DIGESTION_2026_07_06.md` as the
current publication-oriented digestion for `main` at `3f6f1e3`, with a later
fast-regime integration note.

Coordinator disposition: accepted with correction. The auditor said the hash
was not on the current lineage, but `git merge-base --is-ancestor 3f6f1e3 HEAD`
showed that it is an ancestor of `800b9b3`. The real issue was stale wording:
the digest has since been updated with supplied-store and route-split notes, so
the README now describes it as a July 2026 digestion originally rooted at
`3f6f1e3` and updated with later supplied-store, fast-regime, and route-split
cost notes.

## Positive Evidence Summarized By Auditor

- Kernel/build evidence: `lake build RMQPaper`, `lake build RMQ`, and
  `lake build RMQExamples` passed in the auditor run.
- Axiom evidence: `scripts/headline_axiom_check.lean`,
  `scripts/wordram_axiom_check.lean`, and `scripts/axiom_check.lean` passed
  with standard Lean axioms only.
- Model theorem evidence: all-size cost now goes through the route-split
  theorem and fixed `4144` corollary; fast-regime `118` retains its readiness
  threshold; legacy `196727` remains checked only as compatibility.
- Artifact/process evidence: claim-drift and design-decision checks passed; ADD
  and audit logs are treated as process evidence, not proof evidence.

## Stale Or Rejected Objections

- Exact all-size `118` is not claimed.
- `196727` appears only as legacy compatibility or history.
- `2^128` appears only in large-regime compatibility or history contexts.
- Broad `import RMQ` is not the paper root.
- ADD logs and audit reports do not prove mathematical claims.
- The zero-block scan and conservative footprint story are live R3 hardening
  targets, not hidden proof defects.

## Post-Report R3 Follow-Up

This report records the pre-R3 surface audited before worker
`W03-r3-zero-block` landed. The R3 follow-up keeps the same structural
zero-block scan but sharpens its counted word cap, replacing the fixed
all-size corollary `65585` with the checked public constant `4144`.

## Coordinator Follow-Up

Applied accepted P3 documentation fixes and added durable audit-report storage
under `docs/internal/audit_reports/`.

Next proof target remains roadmap R3: shrink or replace the zero-block
same-block structural scan route without uncounted answer tables, proof-only
answer fields, synthetic trace events, or public `2^128` activation.
