# BV-1 coordinator route disposition

Disposition: APPROVE_ROUTE_AND_CONTINUE. Full target remains INCOMPLETE; no capstone, public milestone, integration or final-audit acceptance is recorded.

Reviewed exact evidence commit 645a0502b9da9ad6444edbe44759e1c2c5661f25, source commit 581deebcacfded874d17da7db1e9132a1eefa184, on codex/bv-1-fully-charged-rank-select. The working tree was clean at review entry. REPORT.md is 10111 bytes with SHA256 49ACB1E42574C6CF8EE611305268DFE061E64323B1ED201F9D9C401EFEE0B7B1; the frozen matrix SHA256 is 80BD59A314FD33D37076802954444DA24F65C87A2A91DE23BC668B6AF9CCEB24. The later evidence commit changes process/report receipts, not the four reviewed Lean modules. Exact source hashes for the reader, experiment and validator match the recorded execution evidence.

The coordinator read all four Bitvector modules, the operation contract, frozen requirements, validator and crossing/selector runners. A separate read-only proof auditor independently reviewed the same construction before reading the worker's review and reached the same route recommendation. Canonical rmq-coordinator preflight passed. The returning worker's latest actual runtime evidence includes rmq-proof-sprint and a successful canonical skill preflight.

## Reconstruction and route choice

Normalization.lean:63-88 proves position-preserving rank/select transport, and :114-138 derives the numeric packet from the raw word value and exact length. SelectExperiment.lean:62-79 allocates one raw input, two target-specific directory collections and shared tables. Its :81-112 descriptor reader charges four actual loads, then runs the existing regularLocateBlock and spanBlock; only segment zero is complemented. No logical-store callback is passed into the executable Block.

AllocationFacts.lean:30-88 proves the exact selected-array bit decomposition and bounds the two directory portions separately. It does not prove the final n+o(n) capacity: metadata, rank/access data, padding, code and scratch still need the same-allocation join. The evidence is sufficient to select this route for implementation without changing the frozen target.

The explicit next proof order is canonical regular layout and exact slice recovery; charged descriptor installation and CanonicalGenericReaderCorrect; generic supplied-store normalization/controller refinement; access and both-bit rank programs; all-prefix primitive safety and complete space/cost composition; exact-type consumers and final adversarial validation. Independent leaves may run in parallel on pinned signatures. Existing shape-specific SelectProof cannot be used as if a new reader alone removed its CartesianShape/MetadataMatches premises.

## Load-bearing obligations retained

- Descriptor stride is the first word's length. Prove regularity and exact flattened-slice recovery for every actual canonical table/chunk/sentinel builder. The noncanonical array #[[], [true]] shows why erasure and a maximum-width bound alone are insufficient. Cover empty, short-first and trailing-empty cases.
- genericReaderReceipts in ReaderInterface.lean:49-62 uses canonical geometry. Its canonical correctness proposition at :79-81 remains coherent. Arbitrary-memory results must follow actual replies and early faults: empty memory faults at the first load, rather than producing a canonical four-load prefix.
- Prove equal raw chunking for both target builders and transport the whole supplied-store controller. Leave flag-rank and shared-table replies unchanged; derive every result from charged physical replies.
- Preserve strict span/packet widths, the eight-chunk condition, bounded encoded operands/addresses, safe arithmetic and fixed program uniformity.
- Complete actual allocation accounting for all three operations and both values. Do not use sibling allocation facts or include duplicate raw input.
- The successful crossing control is a false-target reader-component control. It proves an actual second load was executed and backed; it does not establish complemented true-target or whole-select crossing reachability. Long/sparse exception controls and the universal proof remain open.

## Independent checks executed

On Windows, with pinned Lean 4.22 and one job, the coordinator reran scripts/packed_bitvector_axioms.lean, the production mixed-true selector, and the physical crossing component. All completed with exit zero and no timeout. Reader normalization axioms were only propext/Quot.sound; the mixed case returned packet 7 in 1969 instructions with 118 reads; the crossing case executed one second load and returned packet 1. Full structured receipts are in bv1-route-review/*.json. These are focused phase checks, not a replay of all 18 fixtures or final gate certification.

The committed-range whitespace check passed. No source, report or worker branch was modified by this review. I did not run the aggregate, prove the missing universal reader, verify final safety/space claims, or accept any of the 30 full-target rows. The author retains all open obligations.

## Continuation and failure-mode feedback

Resume the same task and branch. This phase review is now discharged; no further route-review stop is required for routine proof choices, helper completion, checkpoint commits or cold builds. Keep working until the original capstone and all assigned/inherited rows close, or report a precise obstruction or necessary scope/model change. PRE's separate contract-before-builder gate does not apply to this bitvector implementation.

Preserve initial frozen requirement rows byte-for-byte and append current evidence/discharge records rather than rewriting the historical OPEN matrix. Correct current phase prose so this completed coordinator review does not remain listed as pending.

No new proof defect or process policy amendment is justified by this checkpoint. The already-known stride, canonical-vs-arbitrary-memory, generic-controller and coverage boundaries remain explicit obligations and require persistent controls at final closure. The continuation clarifies the phase boundary to prevent helper or report completion from becoming an unintended terminal endpoint.

