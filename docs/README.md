# Documentation Guide

Current RMQ publication proposition:
`RMQ.Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`
joins the canonical reviewer payload to the canonical global trace with exact
physical backing, exact valid queries, and uniform charged-trace bound `76`.
Controller operations remain outside the charged event model; this is not a conventional word-RAM or Lean runtime bound.


This repository has two kinds of documentation:

- public artifact docs for readers who want to know what was proved and how to
  check it; and
- engineering notes that record design choices, failed routes, and future
  cleanup/development plans.

## Public Artifact Docs

- [`digests/DEEP_PROJECT_DIGESTION_2026_06_28.md`](digests/DEEP_PROJECT_DIGESTION_2026_06_28.md):
  stress-tested first-contact explanation for a Lean club or mathematically
  mature audience without data-structures background.
- [`digests/PROJECT_DIGESTION_CURRENT.md`](digests/PROJECT_DIGESTION_CURRENT.md):
  sole current publication-oriented digestion for the canonical reviewer
  payload/global-trace theorem and its charged-trace boundary.
- [`digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md`](digests/SUCCINCT_RMQ_COST_COMPATIBILITY_HISTORY.md):
  explicit non-current chronology for earlier cost and dispatch surfaces.
- [`ADD_PROVENANCE.md`](ADD_PROVENANCE.md): public audit-driven-development
  provenance note; ADD and AI assistance are workflow evidence, not proof
  objects or trust-base assumptions.
- [`WHAT_IS_PROVED.md`](WHAT_IS_PROVED.md): compact scope summary for external
  readers.
- [`PAPER_MAIN_THEOREM.md`](PAPER_MAIN_THEOREM.md): English main theorem and
  machine-level theorem map for the paper-facing RMQ artifact.
- [`PAPER_THEOREM_MAP.md`](PAPER_THEOREM_MAP.md): short citation map from paper
  claims to checked Lean theorem names.
- [`PAPER_CLAIM_CORRESPONDENCE.md`](PAPER_CLAIM_CORRESPONDENCE.md):
  reviewer-grade paper claim correspondence table with aliases, source theorem
  names, source files, and exact check commands.
- [`ARTIFACT_REPRODUCIBILITY.md`](ARTIFACT_REPRODUCIBILITY.md): exact
  toolchain, build commands, axiom checks, forbidden-token scans, release-tag
  instructions, and non-claims.
- [`RELATED_WORK_AND_LIMITATIONS.md`](RELATED_WORK_AND_LIMITATIONS.md):
  related-work positioning and model limitations.
- [`PAPER_RELATED_WORK.md`](PAPER_RELATED_WORK.md): paper-ready related-work
  draft and limitations framing for a formalization submission.
- [`AI_ASSISTED_DEVELOPMENT_NOTE.md`](AI_ASSISTED_DEVELOPMENT_NOTE.md): short
  trust-boundary note on AI assistance, ADD provenance, and reviewer checks.
- [`TRUST_BASE.md`](TRUST_BASE.md): build gate, expected axioms, dependency
  policy, and model assumptions.
- [`TRUST_AUDIT_PACKET.md`](TRUST_AUDIT_PACKET.md): compact reviewer packet for
  the headline theorem, including alias chain, theorem shape, axiom excerpt,
  dependency sketch, model glossary, and non-claims.
- [`WORD_RAM_REVIEW_PACKET.md`](WORD_RAM_REVIEW_PACKET.md): focused
  anti-oracle review packet for the first-order Word-RAM interpreter boundary
  and interpreted RMQ/rank-select theorem surfaces.
- [`FAMILY_SUMMARY.md`](FAMILY_SUMMARY.md): full theorem inventory and
  per-structure status matrix.
- [`HUB.md`](HUB.md): reusable hub import surface.
- [`RANK_SELECT_FRONTIER.md`](RANK_SELECT_FRONTIER.md): standalone
  rank/select spoke status and next frontier.
- [`UNION_FIND_FRONTIER.md`](UNION_FIND_FRONTIER.md): union-find spoke status,
  forest-refinement surface, and amortized-analysis frontier.
- [`REPOSITORY_STRATEGY.md`](REPOSITORY_STRATEGY.md): how this RMQ spoke can
  grow into a broader verified data-structures effort.
- [`DIGESTION_LOG.md`](DIGESTION_LOG.md): standing proof-explanation protocol
  for turning verified milestones into auditable, teachable summaries.
- [`digests/RANK_SELECT_COMPRESSED_FID_2026_06_29.md`](digests/RANK_SELECT_COMPRESSED_FID_2026_06_29.md):
  first-contact explanation of the compressed/FID rank/select family theorem.
- [`digests/UNION_FIND_TARJAN_ARCHITECTURE.md`](digests/UNION_FIND_TARJAN_ARCHITECTURE.md):
  architecture note for the sequence/event path toward Tarjan amortization.

## Engineering Notes

- [`CLEANUP_AND_ROADMAP.md`](CLEANUP_AND_ROADMAP.md): completed cleanup record
  and non-blocking post-cleanup roadmap.
- [`ROADMAP.md`](ROADMAP.md): detailed research roadmap.
- [`internal/SUCCINCT_FINAL_PATH.md`](internal/SUCCINCT_FINAL_PATH.md):
  historical theorem-chain plan for the succinct RMQ capstone.
- [`GENERIC_SELECT_REFACTOR_SCOPE.md`](GENERIC_SELECT_REFACTOR_SCOPE.md),
  [`internal/LOCAL_BP_DECODER_PATH.md`](internal/LOCAL_BP_DECODER_PATH.md),
  [`internal/INTERIOR_NAVIGATOR_DESIGN.md`](internal/INTERIOR_NAVIGATOR_DESIGN.md), and
  [`internal/SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md`](internal/SUCCINCT_SELECT_LOCATOR_ARCHITECTURE.md):
  component-specific design notes.
- `AUDIT_*.md`, `*_AUDIT.md`, `CODEX_*.md`, and
  [`internal/WORKER_INTEGRATION_CHECKLIST.md`](internal/WORKER_INTEGRATION_CHECKLIST.md):
  internal audit and orchestration records. They are useful for preserving the
  reasoning trail, but the public theorem surface is the code plus the artifact
  docs above. See [`internal/README.md`](internal/README.md) for the internal
  index.

## Verification

The public gate is:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\gate.ps1
```

The paper-artifact reproduction gate is:

```bash
scripts/reproduce_artifact.sh
```

For a shorter check of the public headline aliases:

```powershell
powershell -ExecutionPolicy Bypass -File scripts\headline_check.ps1
```
