# V1 finalization contract — 2026-10-01

Base and workflow governance: `ee44f04a561f2194b3713f071c26b6faf9ba7fab`.
Candidate branch: `codex/v1-finalization`. Intended version: `1.0.0-rc.1`.
The deliverable is a locally verified release candidate; publication is a separate owner action.

This matrix freezes the requirements before coordinator edits. Evidence is added
as it is obtained. Historical reports remain historical. A clean build or agreement
between reviewers alone does not discharge a requirement.

| ID | Requirement and actual consumer | Evidence obtained | State |
| --- | --- | --- | --- |
| V1-01 | Reconcile LIFE1 formal/native scope across audited, repaired, squash and main objects; disposition all four inherited P3s against actual execution paths. | V1_RECONCILIATION exact 368-module/116-path lineage; repaired EH source and both-profile controls; bounded audits; formal/native disposition in V1_COORDINATOR_ACCEPTANCE. | PASS |
| V1-02 | Synchronize all 18 registered current-fact paths and additional linked reader/source/manuscript paths; distinguish 210, 427, 837572 and lifecycle executions. | Original 18 plus 2 guides remain registered (20); current/source/manuscript inspection and strict scans; source-based 210/427/837572 guards with 88 controls. | PASS |
| V1-03 | Short README, worked half-open leftmost example, theorem/source tour and verified smoke/full commands with observed durations. | Short README, worked example and source tour; cold unpacked smoke and explicitly qualified Linux component evidence; measured host/cache-qualified durations in V1_GUIDE. | PASS |
| V1-04 | Consolidate live rank/select duplicate proofs, remove unused private erase lemma and improve two trace-decomposition proof sites without changing computational definitions or theorem contracts. | V1_PROOF_MATRIX and exact public-type/axiom comparisons; full builds and passing formal components; eight canonical delegations, two removed private wrappers and consumed result decomposition. | PASS |
| V1-05 | Checked universal clients for packed and classic theorems, complete eventual storage, supplied-store reuse, tie and invalid examples. | V1_CLIENT_MATRIX and compiled V1Clients, complete-capacity and supplied-store clients; cold unpacked smoke and passing build components. | PASS |
| V1-06 | Align candidate version and citation metadata; reconcile paper pin with actual source relationship. | Version/citation 1.0.0-rc.1, checked paper source relationship, compiled 20-page PDF and aligned theorem inventory. | PASS |
| V1-07 | Produce clean Git-derived source archive containing claim packet, manuscript, pinned toolchain and hash manifest; verify unpacked contents and documented path without publishing. | Real 6eb source ZIP qualified by 5068 exact Git blobs/modes/paths and cold smoke. Delivered instance is separately bound and verified in external RMQ-V1-DELIVERY.json. | PASS (delivery instance recorded externally) |
| V1-08 | Verify frozen integrated candidate, including build, trust/hygiene, strict design/claim checks, relevant aggregate/mutation/native operational checks with exact identities and logs. | 447 Linux aggregate remains FAIL: 17/20 registered checks pass. All 3 failed checks pass at 250e5932 after documentary repair; exact-input composition, changed guards and d7 finite native evidence are qualified in the coordinator record. Final current-tree results are external. | PASS (delivery instance recorded externally) |
| V1-09 | Obtain fresh blind audit of exact candidate, repair findings and record their disposition with separate audit target identity. | Original exact 447 source audits preserved, disclosed Claude freshness boundary, all findings dispositioned; separate EH and exact-blob correction reviews. | PASS |
| V1-10 | Deliver local candidate and release decision clearly, with all remaining limitations; preserve original dirty checkout. | Clean managed candidate and unchanged original tracked checkout; local source/PDF/evidence delivery with external identities; publication remains separate. | PASS (delivery instance recorded externally) |

Invariants: Lean/Std plus omega only; half-open `List Int` RMQ with leftmost
ties; model cost, payload bits, proof fields and native runtime remain distinct;
no theorem weakening, answer-as-premise substitution, broad module migration,
public API renaming or added performance claim. Standard Lean logical axioms
are inventoried separately from forbidden/custom trust additions.

Evidence order: pin base and scope → source/evidence inventories and disjoint
implementation leaves → source review and integration → current claim/paper
alignment → frozen verification → independent exact-source audit → repairs and
targeted review → archive verification → owner publication decision. Evidence
collection does not depend on the conclusion it is supposed to justify.

Parallel plan: proof worker owns the five assigned Lean modules plus its matrix
and DD entry; client worker owns V1Clients, examples barrel, client guide, matrix
and DD entry. Coordinator owns reconciliation, public prose, metadata, packaging,
integration and final gate. Claude drafts/reviews read-only within the explicitly
approved RMQ materials. Worker proofs require focused checks before integration;
the integrated tree receives one final aggregate gate after edits stabilize.

## Checkout-byte repair amendment

| ID | Requirement and actual consumer | Evidence obtained | State |
| --- | --- | --- | --- |
| REVIEW-NATIVE-CHECKOUT | Preserve the two LF-frozen native contract/matrix files and the three historical CRLF fixture/startup representations across Git checkout settings, without weakening raw hash comparisons. | Fresh checkout fixtures with core.autocrlf true/false/input; native replay at d7d633e0d020352757f7f5f0d139de0dfa42b5d0 and independent6559-pin/142-answer check in V1_NATIVE_REPLAY.json and V1_NATIVE_INDEPENDENT_CHECK.json. | PASS |

The first current native attempt passed the 16-case lifecycle validator but
failed before compilation because Git converted the frozen contract to CRLF.
Its Git blob still matched the frozen hash. The failed receipt remains evidence;
the repair changes checkout attributes, not any historical file or predicate.

## Packaging review amendment

| ID | Requirement and actual consumer | Evidence obtained | State |
| --- | --- | --- | --- |
| REVIEW-PACKAGE-METADATA | Reject citation version mismatch, including a longer version with the expected prefix, and an inconsistent toolchain field with otherwise intact file hashes. Preserve clean exact-Git packaging. | Eleven Windows/Linux packaging tests, independent real archive/Git comparison, cold unpacked smoke. | PASS |
| REVIEW-PACKAGE-CI | Make cheap packaging and native checkout-byte regressions automatic in a separate Windows/Linux CI job, preserving the existing heavy gate and explicitly local EH profiles. State internal manifest consistency separately from commit authentication. | Source review, local Windows/Linux tests, metadata output and reader prose. Hosted CI execution is not claimed. | PASS for implementation and local Windows/Linux checks |

The complete independent source reports are preserved at
`../audit_reports/v1-447751d203a4-fresh.md` and
`../audit_reports/v1-447751d203a4-claude.md`. The latter's requested preservation
path is kept verbatim inside its report; the separate Claude filename avoids
overwriting the other independent report. Review dispositions and current
execution results remain separate from these original source-stage reports.

## Native replay and repair-review evidence

The scoped native campaign at `d7d633e0d020352757f7f5f0d139de0dfa42b5d0`
passed the 16-case validator, fresh native build, startup, 13 fixtures in two
modes, 23 ABI boundaries and four production C++/Rust clients. The independent
checker verified 6559 current file/capture identities and all 142 answer packets
against a separate integer minimum scan with leftmost ties. See the two JSON
records above. This is finite operational evidence, not full historical
LIFE-NATIVE-1 campaign recertification or a compiler/FFI correctness theorem.

Claude's bounded correction report is preserved at
`../audit_reports/v1-review-repairs-claude.md`. Its source-review approvals and
pending evidence are kept intact. The later package correction rejects the
independently demonstrated citation-prefix counterexample as well. The five
checkout rules now all have missing-rule controls and fresh-checkout clean-index
checks; package metadata guards include missing-file and version-field controls.
Final local checks of this refinement are recorded by the coordinator.

## Coordinator verification-composition amendment — 2026-10-01

V1-08 retains its frozen verification obligation. The parallel plan above
anticipated one final aggregate after all edits. Actual source review identified
workflow/packaging defects while the exact 447 aggregate was already running.
That aggregate completed with exit 1: all 20 registered checkers ran, 17 passed,
and three failed on stale citations and a documentary wildcard. The coordinator
retains that failure and accepts only its passing components for unchanged
consumed inputs. All three failed checks, including the full topology regression,
pass at 250e5932 after documentary repairs. Changed guards and current prose
receive separate checks. This explicitly replaces the single-HEAD scheduling
plan with component composition; neither the original nor a final-HEAD aggregate
is claimed to pass. Any later Lean/model/fixture change
would invalidate the corresponding transfer and require its affected checks.
The independent transfer review and exact Git difference inventory document
this decision. Final topology and design-regression checks cover newly added
tracked text and the changed CI workflow, respectively.

The coordinator also approves the nonsemantic REQ-C4 client-matrix amendment:
expand its documentary wildcard in the identity column into the three existing
invalid-range aliases. The exact frozen requirement and Lean client are unchanged;
the amendment makes the already-required consumer identities mechanically readable.

## Final disposition

The requirement text in the original second column remains unchanged. The
planned evidence cells are replaced by actual evidence; their original text
remains in Git history at b4842333ecae5cad9d23bc4b23fa08c294ab6cfd. Exact
evidence and qualified source transfer are recorded in V1_COORDINATOR_ACCEPTANCE,
V1_VERIFICATION_INDEX and V1_AUDIT_DISPOSITION. Publication is outside this
contract. The external delivery receipt binds the final commit and actual output
files and records checks performed after this documentation closure; a bundle
without its passing instance receipt is not the accepted delivery.
