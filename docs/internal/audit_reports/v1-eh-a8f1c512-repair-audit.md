Status: **CANDIDATE_COMPLETE** — this bounded read-only audit is complete. Coordinator acceptance remains required. This report does **not** accept V1 or adjudicate the pending full60/auxiliary runs.

Audited checkout: `C:/Users/poin/.codex/worktrees/v1-evidence-hardening/RMQ`, branch `codex/v1-evidence-hardening`.

- Original source: `7e3a1d086d81eee924036afc3f84b1447ac503cb`
- Repaired source: `a8f1c512e9a5d3d57abae6cd9b988978246af768`
- Governance: `ee44f04a561f2194b3713f071c26b6faf9ba7fab`
- HEAD remained the repaired source; status showed no changes. No files were written, builds launched, campaigns rerun, or checkouts changed.

**Prioritized findings**

No P0, P1, or P2 defect was found in the assigned consumer/context repair.

**P3 — the no-receipt description overstates the common stdout guard.** `docs/internal/extensions/lifecycle1/repair-r4/FAILURE_CONTROL_REGISTRY.json:207` says every W control emits no success marker. K1-W and K2-W require nonzero exit, absent durable output, and their named durable-write diagnostic (`:1744`, `:1773`), but neither supplies `stdoutAbsent`. Only LV-W supplies the explicit PASS-file and PASS-line guards (`:1824`, `:1827`). `repair-r3/failure_controls.ps1:585` makes the stdout check vacuously true without declared needles.

The precise counterexample to that description is a K1-W/K2-W process record satisfying the existing exit/absence/stderr checks while containing an additional success-looking stdout line: the declared stdout predicate does not reject it. This is documentation polish, not a demonstrated regression in the preserved fault cases. Minimal repair: describe all three as failed durable writes with no receipt, and identify LV-W’s additional PASS-artifact/line guards.

**Evidence boundary requiring careful wording:** the WinPS focused receipt is not evidence of 52 WinPS subprocesses. Its accurate composition is **30 predicates executed in the verified host, 13 selected-shell children, and nine disclosed PowerShell-7-only consumer/registry children**. The runtime-contract control checks WinPS’s exact rejection. This supports the repaired attribution claim; it does not establish WinPS support for the nine consumer semantics. A literal requirement that those nine execute successfully under WinPS remains unsupported.

**Per-ID reconstruction**

| Acceptance ID | Source-based conclusion |
|---|---|
| **EH-PATHS** | Supported. The production parent creates `fixtureRoot`, `childShell`, and `hostShell` from its fixture and selected invocation before launch (`repair-r3/failure_controls.ps1:430`). K2’s spec uses that selected executable (`:469`), and the actual child launches it (`:529`). DP’s toolchain comes from the pinned registry (`:439`; registry `:201`); its historical-summary path comes from the copied RESULTS input before child execution/removal (`:477`). The production consumer receives this context at `:626`, independently of child `pinChecks`. |
| **EH-FINAL** | Supported. `repair-r4/predicates.ps1:181` requires both identity fields. Captured identities use distinct 64-hex file and 40-hex Git formats (`:193`). Verified requires a well-formed equal final identity; changed requires a well-formed different identity; unreadable-final requires null (`:203`). Uncaptured rows require null final identities and allowed producer statuses (`:218`). These are record-consistency checks, not cryptographic attestation. |
| **EH-STAGES** | Supported. Identity-kind indices are validated against the full base roster (`predicates.ps1:123`), then projected through an ordered stage subsequence (`:137`). The real K2 setup stage has 11 rows and no captures, while base Git index16 remains valid metadata (`FAILURE_CONTROL_REGISTRY.json:88`). The producer fails loading the missing helper before capturing invocation/Git state (`repair-r2/run_check.ps1:49`) and still emits the 11 source rows (`:91`). |
| **EH-SHELLS** | Supported with the explicit boundary above. Host/runtime validation occurs at `evidence_hardening_controls.ps1:19`; the selected-shell runtime-contract check and nine disclosed pwsh exceptions occur at `:185`. Receipt records disclose their actual execution shell (`focused-*-result.json:289`). |
| **EH-ERRORS** | Supported. Six RC and four FC post-root mutations require the appropriate named StageError discriminator, durable failure, and exact result cardinality (`evidence_hardening_controls.ps1:312`, `:343`, `:355`, `:378`). Missing-file patterns identify the relevant file; drift cases require the specific registry/helper error. The legitimate SourceVariant rejection remains pre-root (`:386`). |
| **EH-ROSTER** | Supported. Parsed before/after `controls` arrays and `harnessKeys` are exactly equal, including order and all fault/expectation fields. There remain 60 controls: 57 receipt-bearing cases and K1-W/K2-W/LV-W. The latter now have `pinCoverageApplicable=false`, `pinsVerified=null`, and explicit inapplicability (`failure_controls.ps1:596`), while their core failure/absence guards remain required. |
| **EH-RECEIPTS** | Both committed focused receipts have the exact ordered 52 IDs, all expected outcomes, and matching source pins. Original12 receipts remain intact. Full60 and auxiliary completion evidence is pending this report’s coordinator review. |
| **INV-CATEGORY-SEPARATION** | Supported within scope. The delta changes no Lean source, toolchain, lake configuration, or owned-process helper. Focused output explicitly identifies host/runtime fixture evidence and excludes theorem, payload-bit, model-tick, runtime-performance, and historical-campaign implications (`evidence_hardening_controls.ps1:406`). Historical-verifier documentation now anchors observations to its original checkpoint. |
| **REPLAY-EXACT-REGISTRY** | Supported by exact mappings, not counts. Production verifies IDs, order, and normalized registry bytes before selection (`failure_controls.ps1:79`). The repaired normalized registry SHA-256 is `6b4734e9cbd36955636452f9b3b93089062481de52b2cf1e9bdd37e50d17db5d`, matching the declared pin at `:45`. |
| **REPLAY-SELECTOR-NONVACUITY** | Supported by intact selectors, exact named negative outcomes, and preserved original positive/challenged pairs. Focused selector/registry checks require exact stream and exit results (`evidence_hardening_controls.ps1:176`). Original12 summaries retain R01_FULL_REGISTRY through R12_WRONG_SUPPLIED_SHELL and explicitly report zero semantic cases executed (`registry-controls-*-summary.json:654`). |
| **REPLAY-SUBPROCESS-DEADLINE** | Preserved. Focused children use finite 30/45/180-second bounds, output limits, owned trees, and cleanup assertions (`evidence_hardening_controls.ps1:47`). The evidence root must be fresh beneath `.lake` (`:24`). Production full60 children retain their declared finite deadlines, launch/ownership checks, and manifest/Git restoration in `finally` (`failure_controls.ps1:529`, `:554`, `:648`). Auxiliary export/HR children retain finite bounds (`aux_controls.ps1:207`, `:239`). |

The exact preserved production IDs are:

`RC-P, RC-C, RC-Q, RC-S, RC-M, FC-P, FC-C, FC-Q, FC-S, FC-M, K1-P, K1-C, K1-Q, K1-S, K1-M, K1-X, K2-P, K2-C, K2-Q, K2-S, K2-M, DC-P, DC-C, DC-Q, DC-S, DC-M, LV-P, LV-C, LV-Q, LV-S, LV-M, IC-P, IC-C, IC-Q, IC-S, IC-M, DP-P, DP-C, DP-Q, DP-S, DP-M, HS-P, HS-C, HS-Q, HS-S, HS-M, HS-R, K1-F, K2-F, K1-T, K2-T, K1-W, K2-W, LV-W, IC-U, LV-E, IC-L, HS-L, K2-G, HS-G`.

**Producer and predicate checks**

All nine producer rosters were traced. RC and FC preserve uncaptured rows after partial setup (`repair-r1/run_controls.ps1:170`; `finalizer_control.ps1:443`). K1/K2 preserve absent/not-captured distinctions; their `appeared` state legitimately carries null final identity (`repair-r1/run_check.ps1:55`; `repair-r2/run_check.ps1:91`). DC, LV, IC, and HS likewise emit their declared ordered rows and independent final reads. DP’s actual toolchain/historical inputs and final reads agree with the repaired context (`lifecycle-native-p0/repair-r1/dependency_controls.ps1:14`, `:41`, `:100`).

Read-only in-memory probes against the pinned production predicate established:

- All **19 declared roster/stage shapes** accept well-formed records, including K2’s 0-of-11 setup stage and DP’s 0-of-1 setup stage.
- The original unrelated K2 shell paths reject at index13; legitimate slash/case aliases pass.
- K2’s same-suffix/wrong-root driver and DP’s wrong toolchain/input/history roots reject.
- Missing trusted context and actual out-of-base identity index17 reject.
- Git null/64-hex final identities reject.
- An 18-case status/final-value matrix accepts only the intended verified, changed, and unreadable-final relations.
- Null/null not-captured, absent-verified, and appeared records remain accepted where the declared stage allows uncaptured rows.

Two initial audit-probe construction mistakes—PowerShell singleton-array unwrapping and multiplication/comma precedence—were corrected in memory and rerun. They were not production failures.

**Focused receipt identities**

Both receipts record 52/52 passing controls, final verdict `pass`, null StageError, and no integrity errors.

| Receipt | Raw checkpoint bytes / SHA-256 | Git blob bytes / SHA-256 |
|---|---|---|
| `focused-pwsh-result.json` | 26,128 / `7df7250de0bf68484ae473810aec5f4cd864a4f42b41ce7ecefc0d32625970f2` | 25,574 / `a0030c621b528d09a71f2f9ffd839367308448579cbe0ed5dd0a73dd33e95b52` |
| `focused-winps-result.json` | 36,715 / `d66e9ac129d59178487509dbf5bd346cfaa7bb0a1b3c59078866ac5c9c7ecc64` | 36,159 / `d96ec1fe21f7e52230a9a895e4f7815d448fa17a942d19c99d8efa069cde7241` |

Runtime records identify pwsh `7.6.5` and Windows PowerShell `5.1.26100.9444`. Every repository source pin in both focused receipts matches the raw worktree bytes; CRLF→LF normalization reproduces the pinned Git source. Mixed line endings explain apparent raw/Git hash differences.

The preserved original12 summaries likewise match their source pins and retain all named expected outcomes. Their raw SHA-256 values are:

- pwsh: `5b1668075b5715ce0bc3c553e7fcd45f2f3e25733afd706247b202bd05c8cade`
- WinPS: `4e309624928507cc7a2a5a35e7c9a9b46a24a250da4885630b79010e274b74b0`

These focused and registry receipts do not establish a full historical semantic/native campaign.

**Remaining completion evidence**

The coordinator must evaluate completed full60 receipts for both child-shell profiles against the exact repaired source and registry, including all 60 selected/executed IDs, the **57 receipt checks plus three no-receipt guards**, actual process identity, finalization, and restoration. The full60 runner itself requires PowerShell7 even when its children use WinPS.

The expanded auxiliary roster contains **46 cases** (`aux_controls.ps1:38`); its completed required-runtime receipts, exact source binding, and finalization remain to be evaluated. The WinPS auxiliary host allowance does not make its explicitly hard-pinned pwsh helper children WinPS executions.

Integration, aggregate/native verification, and archive verification remain coordinator responsibilities. This audit neither accepts nor fails unfinished runs.

**Verification actually performed**

- Explicit-no-role skill preflight: PASS, using the actual nonempty runtime catalog `rmq-proof-sprint,rmq-audit-prompt,rmq-coordinator`.
- Pinned `git show`, `git diff`, source inventory, exact registry comparison, producer/consumer tracing, receipt parsing, and raw/Git hash comparison.
- PowerShell AST parsing: zero errors in all four changed scripts; registry JSON parsing passed.
- `git diff --check 7e3a1d086d81eee924036afc3f84b1447ac503cb a8f1c512e9a5d3d57abae6cd9b988978246af768`: PASS.
- Required hygiene and `native_decide|Lean\.ofReduceBool` scans: no matches; `rg` exit1 denotes no matches.
- `lake build`, auxiliary/full60/focused campaigns, aggregate/native gates: **NOT_RUN**, as required by this read-only assignment.

Git status emitted a permission warning about the user-level ignore file; pinned reads and verification commands completed.

**Proof digestion**

The conceptual change is that the evidence consumer now derives expected dynamic identities from trusted parent inputs and checks the relationship between entry identity, final identity, and status. In plain English, a plausible filename or “verified” label is no longer enough.

Live assumptions remain the declared parent/registry trust boundary, the specified Windows path semantics and tool installation, and finite fixture coverage. No Lean theorem or performance result follows from these checks.

The skeptical next question is: **Do the completed production replays, bound to this exact repaired source, demonstrate all 57 receipt-bearing cases and all three distinct no-receipt guards without overstating their shell or campaign coverage?**