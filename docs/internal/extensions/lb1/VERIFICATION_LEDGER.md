# LB-1 verification ownership and command ledger

Earlier rows preserve planning/development history; the final exact-source section below records current local outcomes. A planned command is not a pass. All commands run from
the LB-1 worktree at C:/Users/poin/.codex/worktrees/2270/RMQ. The source and
governance base is 0e6a00f654abc64f8b68988fa9675b9a839dca2f; the contract
checkpoint is 0bbbe8ca4a937bc9782b2f7c5cc5419faa1a75a2. Later proof work is dirty
development content until a candidate commit is named here or in the report.

| Role / command | Coverage and distinct failure mode | Tree and timing / outcome |
| --- | --- | --- |
| Development: project_skill_preflight with exact governance, required rmq-proof-sprint, actual three-skill runtime catalog | Canonical checkout, governance ancestry and required role presence | Clean base; PASS, startup-preflight.txt |
| Development: variable_payload_build -Module RMQ.Core.EncodingVariableLowerBound -DeadlineSeconds 600 | REQ-LB-COUNT and generic semantic controls; elaborates finite cardinality and derived lower bound | Dirty owned generic source; 15-module closure, leaf 18.991s, exit 0; build-20260912T071953550.jsonl |
| Development: variable_payload_build -Module RMQ.Core.WordRAM.Packed.AllocationLowerBound -DeadlineSeconds 1800 | REQ-LB-PQ1/MODEL and all recovered-memory machine fields; resolves actual direct imports and checks adapter proofs | Dirty adapter; one sequential task-local build, in progress. Cold baseline closure has 249 modules. Per-module source/dependency hashes, elapsed seconds, 1800s deadline, exit and outputs in build-20260912T072455472.jsonl. No unchanged timeout retry |
| Development then final-required: variable_payload_build -Module RMQ.Validation.VariablePayloadLowerBound | REQ-LB-CONSUMER; literal independent field types and same-object composed consumer | Pending adapter success; exclusive one-build slot, 1800s/module cold margin. Direct consumers do not widen to an implicit full Lake build |
| Development: variable_payload_contract_check.ps1 | Frozen row byte integrity: exact raw Git blob, strict UTF-8, 29 expected IDs; seven controls use production comparator | Contract checkpoint versus dirty matrix: PASS, no changed rows. FROZEN_ROW_EVIDENCE.md. Added prose outside frozen rows may change whole-file hash |
| Development: variable_payload_replay -RegistryOnly and -DiagnosticOnly | Exact ordered registry, missing-case/selector controls; error must occur inside the named declaration, excluding an adjacent declaration | V1/V2 archived; V3 has 63 proof/control cases and six runtime cases. Local registry and two diagnostic-boundary controls pass; full semantics pending |
| Development: variable_payload_replay -SelectorBoundaryOnly | Real subprocess behavior for omitted, valid, empty, whitespace, malformed and unknown selection | V1, V2 and V3 each passed six expected/executed boundaries with 60s child deadlines. V3 selected all 63 on omission and exactly one valid focused case; evidence/selector-controls-v3.json |
| Development: variable_payload_replay -DeadlineOnly | Owned descendant is actually spawned and is absent after timeout; exit/stderr and job result retained | Windows first 10s probe INCONCLUSIVE before PID creation; revised 30s probe PASS. Historical evidence in process-controls-development.json. Physical POSIX execution is uncovered |
| Final-required: variable_payload_replay full registry | Inventory, all typed consumers, bounded startup, known selector, runtime registry, 63 exact source mutations/controls, exact diagnostic surfaces, source/olean restoration and clean state | Pending clean frozen candidate. Uses one -j1 child at a time and 600s per child; closest producer/consumer/runtime measurements will be recorded before full launch. Resource-limit results are INCONCLUSIVE |
| Final-required: variable_payload_axioms.lean via the owned Lean launcher | Exact public/generic/composed theorem trust inventory; supplements independent expected-type consumers | Pending checked validation and frozen content. Narrow import only; timeout chosen from consumer startup measurement |
| Final-required: trust token scans over RMQ and lakefile.toml, including native_decide and Lean.ofReduceBool scan | Source escape hatches, Mathlib import and executable proof trust changes | Pending frozen content; match inventory must classify existing occurrences instead of counting them as new proof assumptions |
| Final-required: git diff --check and git diff --check exact-base..HEAD | Working edits and committed range whitespace are distinct checks | Working checks so far PASS; final committed-range check pending |
| Final-required: design_decision_check.ps1 -Strict -Base exact-base | Design-sensitive paths require accompanying decision evidence; strict no-base is not accepted | Early dirty development checks PASS; task-specific DD/WDD appendices added. Recheck after final edits/commit |
| Conditional now required by planned family/digest appendices: claim_drift_scan.ps1 -Strict | Public claim wording remains aligned with exact model/certificate and candidate status | Early development PASS; final run pending public appendices, with full output redirected to evidence |
| Coordinator-owned final-required: full lake build and aggregate gate | Broad integration/public-capstone certification on frozen content | NOT RUN. Requires the host-wide coordinator slot. No competing full build is launched. Lane replay ownership must be agreed before an aggregate that would repeat it |
| Final-required: fresh blind exact-commit audit | Independent reconstruction from the frozen contract, source and evidence, without the worker verdict | Pending frozen candidate. Development route and source risk reviews are not substitutes |

## Checked source update before candidate freeze

The cold adapter closure finished: 251 modules in the plan, 250 rebuilt and all
exit 0, totaling 4541.824 child seconds. The first adapter elaboration took
7.658 seconds and had two unused-binder warnings; an explicit-binder cleanup
preserved every field type. Its warm recheck took 9.714 seconds, no output,
exit 0, evidence/build-20260912T084142579.jsonl.

Validation initially reported one unfinished definitional equality in the
same-shape bit fixture (35.757 seconds). Adding final rfl preserved the type;
the next check passed in 32.69 seconds with no output, 252-module closure and
one rebuilt source. Evidence: build-20260912T084243070.jsonl (failed discovery)
and build-20260912T084355841.jsonl (repaired pass).

The separate generic consumer passed in 6.921 seconds. Inventory discovery
failed in 29.686 seconds on outdated syntax for its parent-category fixture;
the corrected declaration passed in 13.23 seconds, checking actual 4/16/33
fields, two accepted controls and eleven rejected predicate calls. The repair
did not alter the compared inventories or weaken the parent condition. Both
the original and repaired JSON evidence remain available.

Before broad final certification, fresh-source `--run` startup listed all six
runtime IDs in 39.092 seconds, and `--case R04-ZERO-LENGTH` executed exactly that
case in 46.26 seconds. The 600-second deadline includes observed source
elaboration and host-load margin. The full registry was not run during this
development probe. Its final replay will independently verify startup/selection
on the committed candidate before any mutation. These are frontend-plus-runtime
measurements and are separate from the model's primitive instruction counts.

The narrow axiom inventory then passed in 50.867 seconds. Exact output-name
comparison found all 20 required declarations; the union of assumptions is
propext, Classical.choice and Quot.sound, with no unexpected name. Full scans
over RMQ/lakefile for trust escape tokens/Mathlib and over RMQ for native
reduction escapes found no hits. These results concern the checked unchanged
proof sources; exact raw diagnostic output and the name/assumption summary are
in the evidence folder. Public-dependency mutation evidence remains separate.

Source edits invalidate transitive Lean consumers and semantic replay that read
those sources. Registry/verdict edits invalidate their exact replay evidence.
Report-only additions do not invalidate unchanged kernel elaboration, but do
require the corresponding claim/design and committed-range checks. Historical
observations may guide deadlines and cache reuse; they do not certify changed
code. Exactly one agent holds the narrow Lean slot at a time, and any transfer
is explicit. No final aggregate has been duplicated or inferred from a narrow
build.

Aggregate ownership was checked against scripts/gate.ps1: the gate derives
lean_exe targets from lakefile.toml and therefore builds the new validation
target. It does not invoke variable_payload_replay or the lane-specific
inventory/axiom scripts. The 63-case lane replay consequently has distinct
coverage and must be run explicitly; its execution is not inferred from the
aggregate. Existing aggregate replays retain coordinator ownership.

## Final exact-source local outcomes, 2026-09-12

Implementation/audit source:5033ce54da233fc7a3df319d50ab09a2ebee523a. All work ran with one Lean owner; no full Lake build or aggregate was run here. The user assigned those broad commands to the coordinator. The final source-to-delivery comparison preserves all implementation and existing checker paths; only evidence and report/public-process text is added after local checks.

| Check | Exact local outcome and durable evidence |
| --- | --- |
| Fresh baseline compilation and metadata | Generic and packed producers, actual 4/16/33 inventory, all 49 literal validation consumers, separate generic consumer: all exit0 before baseline artifacts were saved; evidence/replay-v3-5033/baseline-*.json. |
| Full version 3 replay | All63 ordered cases,61 expected REJECT and 2 expected ACCEPT; all 6 runtime cases;134 raw stages; source/artifact restoration and clean state. evidence/replay-v3-5033/summary.json. Final terminal exit0 at 2026-09-12 11:08:36 UTC. |
| Independent saved-evidence reconciliation | Exact stage order, own-declaration semantic diagnostics including S03 P/Q, no resource/import substitute, six runtime IDs, raw/summary equality,677 current source/configuration files: EVIDENCE_CONSISTENT. Twelve raw byte matches and 665 CRLF/LF-only differences are distinguished. evidence/final-verification/final-replay-verification.json. |
| Five focused entry points | RegistryOnly 5.992s, SelectorBoundaryOnly 42.78s, DiagnosticOnly 6.803s, DeadlineOnly 36.294s, RuntimeOnly 375.182s: all exit0. Expected/executed modes identical; source unchanged and clean. Nested child records retained in evidence/focused-modes-5033. |
| Owned timeout | Windows child3892 was created, the 30-second owned timeout terminated it, and the no-survivor check passed. Deterministic ownership-plan controls also passed. Physical POSIX execution is UNOBSERVED on this host. |
| Additional selector branches | Replay CLI/environment conflict7.14s; runtime conflict42.904s; malformed runtime ID inside a valid case: channel36.94s. Each rejects at the intended branch before any case-pass marker. evidence/selector-extra-5033/summary.json. |
| Trust inventory and source scans | All20 ordered declarations: only propext, Classical.choice and Quot.sound. Both required full RMQ source scans have no hits. Source unchanged/clean; evidence/trust-5033/summary.json and axiom-inventory.json. |
| Frozen acceptance rows | Exact5033 checker:29 unchanged whole rows and 7 corruption controls pass; evidence/frozen-rows-5033/evidence.json. |
| Exact-source public/process policy | Strict claim scan including process records:2026 hits,0 strict failures. Strict design check with exact governance base:185 changed files, no failure. evidence/final-verification/source-5033-policy.json and its raw logs. |
| Report-containing tree | Results are recorded in evidence/report-checks.json after the actual report and appendices exist; committed-range and source-equivalence checks are separately reported in the task handoff. |
| Coordinator broad certification | Full lake build and aggregate gate NOT RUN here; user assigned execution/result delivery to the coordinator. |

Focused RuntimeOnly certifies the separately required entry point and its selector path; it does not repeat the 63-case mutation campaign. The additional selector probes cover both simultaneous CLI/environment channels and malformed IDs within a valid runtime channel, which differ from malformed-channel parsing. The20-name trust rerun covers the repaired validation source. The separate verifier's two startup/portability failures are preserved; they are not semantic campaign failures. POSIX physical timeout execution remains UNOBSERVED.
