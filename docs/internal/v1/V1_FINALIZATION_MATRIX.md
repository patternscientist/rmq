# V1 finalization contract — 2026-10-01

Base and workflow governance: `ee44f04a561f2194b3713f071c26b6faf9ba7fab`.
Candidate branch: `codex/v1-finalization`. Intended version: `1.0.0-rc.1`.
The deliverable is a locally verified release candidate; publication is a separate owner action.

This matrix freezes the requirements before coordinator edits. Evidence is added
as it is obtained. Historical reports remain historical. A clean build or agreement
between reviewers alone does not discharge a requirement.

| ID | Requirement and actual consumer | Planned evidence | State |
| --- | --- | --- | --- |
| V1-01 | Reconcile LIFE1 formal/native scope across audited, repaired, squash and main objects; disposition all four inherited P3s against actual execution paths. | Exact blob inventory, report/source review, current-scope disposition. | OPEN |
| V1-02 | Synchronize all 18 registered current-fact paths and additional linked reader/source/manuscript paths; distinguish 210, 427, 837572 and lifecycle executions. | Complete source inventory, scoped edits, strict claim scan, reviewed prose. | OPEN |
| V1-03 | Short README, worked half-open leftmost example, theorem/source tour and verified smoke/full commands with observed durations. | Claude draft and coordinator source review; V1 guide; recorded command results. | OPEN |
| V1-04 | Consolidate live rank/select duplicate proofs, remove unused private erase lemma and improve two trace-decomposition proof sites without changing computational definitions or theorem contracts. | V1-PROOF matrix, source/types/consumer review and Lean checks. | OPEN |
| V1-05 | Checked universal clients for packed and classic theorems, complete eventual storage, supplied-store reuse, tie and invalid examples. | V1-CLIENT matrix, single headline import, successful examples build. | OPEN |
| V1-06 | Align candidate version and citation metadata; reconcile paper pin with actual source relationship. | Version checks, paper checker, declaration inventory and explicit pin relationship. | OPEN |
| V1-07 | Produce clean Git-derived source archive containing claim packet, manuscript, pinned toolchain and hash manifest; verify unpacked contents and documented path without publishing. | Packaging command, independent hash check, unpacked smoke verification. | OPEN |
| V1-08 | Verify frozen integrated candidate, including build, trust/hygiene, strict design/claim checks, relevant aggregate/mutation/native operational checks with exact identities and logs. | Final gate and scoped operational logs; no relabeled historical results. | OPEN |
| V1-09 | Obtain fresh blind audit of exact candidate, repair findings and record their disposition with separate audit target identity. | Frozen audit brief/report, coordinator reconstruction and follow-up coverage. | OPEN |
| V1-10 | Deliver local candidate and release decision clearly, with all remaining limitations; preserve original dirty checkout. | Clean candidate, final matrix, digestion and concise user report. | OPEN |

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

| ID | Requirement and actual consumer | Planned evidence | State |
| --- | --- | --- | --- |
| REVIEW-NATIVE-CHECKOUT | Preserve the two LF-frozen native contract/matrix files and the three historical CRLF fixture/startup representations across Git checkout settings, without weakening raw hash comparisons. | Fresh checkout fixtures with core.autocrlf true/false; exact hashes and actual native rerun. | OPEN |

The first current native attempt passed the 16-case lifecycle validator but
failed before compilation because Git converted the frozen contract to CRLF.
Its Git blob still matched the frozen hash. The failed receipt remains evidence;
the repair changes checkout attributes, not any historical file or predicate.
