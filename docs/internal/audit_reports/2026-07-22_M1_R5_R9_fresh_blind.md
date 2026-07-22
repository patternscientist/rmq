# M1-R5-R9 fresh-blind audit: exact frozen positive policy fixture

Auditor: `M1-R5-R9-AUD1`

Mode: FRESH BLIND DELTA

Report branch: `codex/m1-r5-r9-fresh-blind-audit`

Authorized report path: `docs/internal/audit_reports/2026-07-22_M1_R5_R9_fresh_blind.md`

## Findings

- **P0:** none.
- **P1:** none.
- **P2:** none.
- **P3:** none.

No candidate defect was found. The positive-fixture repair is exactly additive, the inherited machine/policy surface remains intact, and the exact candidate is compatible with the audited current governance without a conflict.

## Recommendation

`ACCEPTED`

This recommendation applies only to isolated candidate `977a4df8b5d9e908fe66d012dd242006790ebaf3`. It means the candidate is sound and can be integrated with no judgment-bearing conflict against the exact audited main/governance commit. It does not merge the branch, record coordinator acceptance, close M1, publish, push, or retire any branch.

## Scope and immutable identities

| Role | Commit | Tree | Ordered parent(s) | Independent result |
|---|---|---|---|---|
| report base | `373026670bc12faa1ec764475f8233c79caf8330` | `c2d42585428743f6fb8730bf1c716ae3b669cf51` | candidate `977a4df8...`, governance `b07fcc5...` | exact; report checkout began clean |
| candidate | `977a4df8b5d9e908fe66d012dd242006790ebaf3` | `c2d42585428743f6fb8730bf1c716ae3b669cf51` | private base `c9375cf...` | exact one-commit candidate |
| candidate/private base | `c9375cf83a55c122b27c56a73c6027f36faea643` | `0d9d94d5a4f7955f468a8352d627f97c4637ea6a` | rejected R8 `d679628...`, governance `b07fcc5...` | ordered parents exact; both candidate ancestors |
| immutable R8 source fixture | `d6796285a3b9d79ebc78422695d196f26449e771` | `530db5efe4dde07e5bb2753c28105de3a840596b` | `3bf7b6c...` | exact raw-row comparison source |
| audited main/governance | `b07fcc5470349f7cdc261f82ee6d8c320c65923e` | `4cd0ee1ff7af3cd373a62dd0c187cca2a04b63bb` | `f44a09b...` | `refs/heads/main` at integration check; candidate descendant |

The candidate branch, private-base branch, and report-base branch resolved to the exact commits above. `git rev-list --count c9375cf...977a4df` returned `1`. Recursive diff and raw-object comparison found exactly four changed candidate paths:

1. `scripts/claim_drift_policy_regression.ps1`
2. `docs/internal/M1_REVIEWER_NATIVE_ADEQUACY_ACCEPTANCE_MATRIX.md`
3. `docs/DIGESTION_LOG.md`
4. `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`

Every other path therefore has its exact base blob. Report base and candidate intentionally share the candidate tree.

The mandated explicit no-role preflight passed against governance `b07fcc5470349f7cdc261f82ee6d8c320c65923e` with runtime catalog `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`. No coordinator, proof-sprint, or prompt-authoring role skill was used as an audit-worker substitute.

## Evidence tiers and bundles

The bundle labels below keep the 91-row disposition compact. Process logs and ledgers are never promoted above tier 5.

| Bundle | Tier | Independent evidence |
|---|---:|---|
| **B1 — exact graph/raw objects** | 4 | Git parent/tree/range/scope checks; one strict UTF-8 decoder over raw Git blobs; matrix row/cell/order/byte checks; blob IDs, SHA-256, byte lengths; exact append and three-edit reconstruction |
| **B2 — Lean/model proposition reconstruction** | 1–2, with freshness from tier 4 identity | Exact theorem types and proof bodies over the explicit payload/store/trace; load-bearing consumer expansion; exact inherited source/checker blob identity; focused production registry self-test. No fresh broad re-elaboration was claimed. |
| **B3 — production policy boundary** | 3–4 | Production strict scanner through committed `-OnlyCase` fixtures; historical/retired/quoted/policy/path/held-out/negated bypasses; bounded controls; absolute-path control; selector failure; restoration and clean state |
| **B4 — platform/process controls** | 3–4 | Fresh exact-candidate Windows and native Ubuntu clones; selector, deadline, portability, topology ownership, CRLF/dirty channels, scalar-tool resolution, PID/survivor checks, exact HEAD/tree, and final clean state |
| **B5 — governance/current surfaces** | 3–5 | strict claim scan; exact 18-path current-surface inventory; strict design certification; raw append/preservation checks; decision/digestion audited against lower-tier evidence |
| **B6 — integration compatibility** | 4 | exact main/governance ancestry and read-only `git merge-tree --write-tree`; governance-path blob preservation; no branch mutation |
| **B7 — hygiene/final state** | 4 | forbidden-token and native-decision scans; `git diff --check`; exact HEAD/tree and tracked/index/untracked cleanliness checks |

## Strict raw-blob and matrix reconstruction

Raw bytes came directly from `git cat-file blob <ref>:<path>` into Python `bytes`; the identical `raw.decode('utf-8', 'strict')` operation was used for R8, base, and candidate. Raw bytes never passed through PowerShell text conversion. Lines retained terminators with `splitlines(keepends=True)`. The cell scanner treats a pipe as a delimiter exactly when it is preceded by an even-length backslash run; code spans receive no exemption. Only the ten frozen acceptance-table sections, from the frozen contract through the R9 repair table, were parsed.

Results:

- candidate: exactly 91 rows, 91 unique stable IDs, prompted order, and eight cells per row;
- first 87 candidate rows: exact raw-row byte matches to R8, concatenated SHA-256 `df4fbfa6980c529440588e6143efd1bce81d0c97ba9fe5aa6cd0d1eeb922544f`;
- inherited `computation\|work` escape: present and byte-preserved;
- R9 block: candidate lines 191–286, exactly 96 inserted lines, 14,306 bytes, SHA-256 `919b45b330ecb4da15745a5ef8f6cbb73c74b52be6dab794f87fe0355edd1e05`;
- the four R9 requirement rows are candidate lines 200–203 in the required order; their raw SHA-256/length pairs are `7b593f...`/2,779, `5b34ad...`/2,247, `dbaed4...`/1,435, and `93e6e0...`/1,806;
- no BOM, CRLF, lone CR, malformed UTF-8, normalization, duplicate/invented ID, or non-eight-cell row was found.

### Exact blob identities and digests

| Path | Base Git blob / SHA-256 / bytes | Candidate Git blob / SHA-256 / bytes | Shape |
|---|---|---|---|
| acceptance matrix | `8b89a3ccc00dcaa0386667da42359ce1d3bbe6cc` / `23968542f3c0a7d66e35436bb8021eac9d8db538e2fe152bc9667e28e034ee03` / 198,175 | `21b42ee8babefe6d96234a92c3f3e12b34cb1451` / `031941b1f448a74d72baf2792c248f19283bfc35868fe1328165072dc6738282` / 212,481 | isolated 14,306-byte insertion |
| digestion | `53477a99774a875873e1acbfa81a2eaf812656ef` / `c1f0636f0b3d172a7e7c129e5ca32c7099783257128f0c570c1bf85c78f4c5b1` / 92,660 | `19bda36bf6b60a507d3903093e7be9f8ffb97e42` / `fe30e00e1da25f8b5874303633c19f2245a6c3687d74c93170fbddef073ccac7` / 96,534 | exact 3,874-byte append; suffix SHA-256 `b8bc7895...` |
| workflow decisions | `7d333b95c7c3fe00658a96e8f1252316227aac65` / `0cf9e6f74d7810c33f0ce4a2392962de7bb100847cb1861ade93e6678e64ce02` / 269,945 | `ed584fe77ee7aa9735862e4525655053f0c35351` / `efbde37a00acada510ae7bf9a7fdac7739d3a74e848c46d370d450439a7d989b` / 275,033 | exact 5,088-byte append; suffix SHA-256 `779ac982...` |
| production fixture registry | `468dadfb69d7d66011da85d0825230afa1252815` / `9a381947848dc3a16d93b56ba1f6424a2b2c855d39fb11e13272dd420bdaaa97` / 59,352 | `c5ad11dee66b52eb1c196f4ed222bdd4b041c302` / `aaa810aa08c0da4252ef40bb3b2e24810881dfc9dfdcd1df96e84524d9e77c48` / 59,799 | exactly one object, one ID, and accept count `37 -> 38` |

## Exact fixture and causal production-policy result

At the base, the exact frozen sentence occurred once in the frozen requirement row and zero times in the production fixture registry. The materially different broader positive remained at production object position 86. Base reconstruction found 119 object lines and 119 aligned ordered unique IDs: 82 reject, 37 accept, and 16 unchanged context IDs. The object-line concatenation SHA-256 was `3462db315fe7e23592107338b62c9fbcf35d6b8957c9c814369181ce8d8680bf`; expected-ID lines were `f3ccb00cd9ded2565682505ef4d7b4273024d1ca117a5456f990d2756af2c5cf`; context-ID lines were `3207b28bdfbc4c027731e3ae554d83beca2601b351172fde16119b1e842b50b9`.

The candidate adds the distinct exact object and aligned ID at position 87, immediately after the broader positive, using `docs/PAPER_MODEL_ADEQUACY.md`, expected accept, production term `forbidden-unqualified-no-event-silent-computation`, and the exact frozen sentence:

> No input-size-dependent or unbounded event-silent loop remains; bounded event-silent dispatch, decoding, arithmetic, branching, merging, trace assembly, and guards remain.

Removing that one target object line and one target ID line reproduces all 119 base lines byte-for-byte. The broader positive and named unqualified negative retain their exact base hashes. Reconstructing the entire candidate script from the base with only those two insertions and `37 -> 38` reproduces candidate SHA-256 `aaa810aa...`; therefore there is no classifier, policy, path, keyword, inherited verdict/object/ID/order, or context-registry drift.

Nineteen separate focused production final-verdict runs passed in 137.889s total. They covered the new exact positive, broader positive, named unqualified negative, all seven former same-line allowance words, three held-out zero-remaining variants, two policy-path variants, the negated-prefix bypass, and three bounded/input-size near misses. Per-case wall times were 6.349–8.426s. Every invocation first passed the exact 120-object registry, duplicate/missing/verdict-drift rejection, and positive deadline cleanup, then restored tracked state. The resulting registry is exactly 120 ordered unique fixtures: 82 reject and 38 accept, with 16 context cases unchanged.

`-AbsoluteWindowsOnly` passed three production path verdicts in 13.907s, including the absolute event-silent policy-path rejection and final restoration. An unknown `-OnlyCase` returned exit 1 in 1.350s with `unknown or non-unique` before semantic case execution. The detached candidate clone remained at the exact HEAD/tree with clean tracked/index/untracked state.

The policy JSON has one strict current-surface term for this category, with empty path/line allowances. Scanner lines 165–203 apply current-surface, path, line, and pair allowances before strict failure; the relevant category has none. The production executions demonstrate that policy words, policy paths, relative single-file inputs, and absolute inputs do not create a bypass, while accurate bounded/unbounded language remains accepted.

## Inherited machine/proof reconstruction

No Lean, checker, topology, gate, policy JSON/Markdown, scanner, skill/template, audit protocol, process-control, current public surface, or design-ledger path outside the four owned files changed from the exact base. The core proof/checker blobs were independently verified base-identical.

The load-bearing chain was expanded rather than inferred from names:

```text
actual supplied execution readWord(segment, index)
  -> direct structural theorem proves segment < 23
  -> safe-footprint agreement implies ordered dynamic-read agreement
  -> ordered dynamic-read agreement implies complete TraceResult equality
  -> current safe alias via orderedReadFootprint
  -> guarded list packet safe_logical_store_agreement
  -> literal listIntSuccinctRMQPaperMainTheorem
  -> independent M1ReviewerNativeExpectedPaperType checker
```

The exact anchors are `SuccinctFinalStoreParam.lean:2464-2533,2680-3101`, `SuccinctFinalModelAdequacy.lean:861-902`, `SuccinctRMQClassic.lean:968-1162`, `Headlines/RMQ.lean:76-232`, and `headline_axiom_check.lean:215-325`. The legacy supplied-store footprint theorem remains declared at `SuccinctFinalStoreParam.lean:2597-2613`, but exact-token/block inspection found it absent from the structural containment theorem, bridge, current safe alias, guarded constructor, paper theorem, and expected-type consumer.

Further independent source reconstruction established:

- exactly 22 physical sources, logical mapping `0..22`, shared BP physical region, and dead `23+` source behavior;
- one flattened physical store whose erasure is the counted public payload, with exact positional backing for successful reads;
- accepted component algebra `129 + 81 = 210`, same-trace non-synthetic weight = trace length = modeled cost, and the public same-execution `<= 210` bound;
- every emitted accepted event is a genuine `readWord`;
- an exact 24-field well-formed certificate, a 24-field required-facts projection, and explicit projection of every field;
- coherent `ValidRange` guards and pure `none` invalid behavior across canonical, supplied logical, and physical routes;
- returned-value, not merely record-log, dependency: changing an actually consumed `(21,3)` word changes the answer `some 0 -> none`, while the remaining cells agree;
- linear capacity, logarithmic reviewer width, physical/address/operand bounds, and stored/returned-word width facts;
- B7 interior cost evidence and S1/E1/A1 category separation without importing an S1 decoder or treating controller work/Lean wall time as charged events.

The production registry self-test passed in 2.197s, confirming exact ordered `F01-F24,Q01-Q11,P01-P05,C01`, 41 cases, 40 reject/1 accept, 24 fields, and omitted/duplicate `F21` rejection. The four-file comment reconstruction found only two historical comment substitutions: `RMQPaper.lean:9` changed `uniform 207` to `uniform <= 210`, and `ReviewerPhysical.lean:999` changed `live 0..20` to `live logical 0..22`; `SuccinctFinalRAM.lean` and `Headlines/RMQ.lean` were unchanged. Reversing only those phrases recovers the pre-repair source blobs, so no theorem/type/body/name/import or executable definition changed.

No fresh broad Lean build or full mutation/topology suite was run: exact non-owned proof/checker identity and proposition expansion exposed no unique contradiction, and the frozen contract reserves broad repetition. This report therefore distinguishes proposition-level/theorem evidence from the focused executable checks and does not relabel inherited receipts as fresh execution.

## Governance, current surfaces, ledgers, and integration

Strict claim drift completed in 19.248s with 1,439 hits and zero failures. The authoritative regex resolved to exactly the prompted 18 tracked current surfaces, and none changed from base to candidate. The event-silent policy term has no broad allowance. Strict design certification against `c9375cf...` passed in 2.047s, classifying four changed paths as zero code, one workflow, and three neutral.

Only after the source/fixture facts above were reconstructed were the R9 digestion and workflow-decision append inspected. They accurately describe the distinct additive fixture, preserved broader positive and negative control, rejected replacement/policy-weakening/disposable alternatives, focused checks, publication significance, live inherited assumptions, and downstream audit/integration status. Their reported worker timings remain tier-5 process claims and were not used as execution evidence. The new workflow entry creates no broad rule or allowance. Earlier protected workflow decisions and DD-20260722-001 are byte-preserved; the DD matches the independently reconstructed two-comment delta.

At integration check, local `refs/heads/main` and the exact accepted governance both resolved to `b07fcc5470349f7cdc261f82ee6d8c320c65923e`. It is an ancestor of the candidate. In a separate exact-candidate clone, `git merge-tree --write-tree b07fcc5... 977a4df...` exited 0 in 0.128s and returned candidate tree `c2d42585428743f6fb8730bf1c716ae3b669cf51`. There are zero conflicts, hence no mechanical or judgment-bearing conflict records to classify. Five non-ledger files changed by the governance commit have exactly the same blobs in governance and candidate; the workflow ledger preserves the governance bytes and appends later decisions. Integration is therefore a fast-forward-compatible operation that retains every newer audited governance item. No merge was performed.

## Platform and process controls

All required focused controls passed. No aggregate gate, full semantic replay, full policy campaign, full topology suite, or broad Lean build was run.

### Windows

Evidence clone: `C:\Users\poin\AppData\Local\Temp\RMQ-AUD1-win-977a4df-019f8b68-d`, detached at exact candidate/tree and clean before and after every completed control.

Identity: Microsoft Windows NT `10.0.26200.0`, build `10.0.26200.8875`; Windows PowerShell Desktop `5.1.26100.8875` at `C:\WINDOWS\System32\WindowsPowerShell\v1.0\powershell.exe`; Git `2.51.0.windows.1`. `pwsh` and an installed sandbox-user elan toolchain were absent, but the required Windows focused self-test paths use Windows PowerShell and exit before Lean; no required Windows control was blocked.

- M1 selector self-test, stage 120s/self 5s: exit 0 in 86.905s. It confirmed the exact 41-case/24-field registry, valid unique F21 selection, omitted/empty/whitespace/zero/unknown/missing/duplicate discrimination, direct safe-dependency route, deterministic kill-on-close plan, scalar application paths, CRLF/autocrlf clean and forced-false controls, and tracked=`Worktree`, untracked=`Status`, staged=`Index` dirty channels.
- M1 deadline self-test, stage 180s/self 5s: exit 0 in 92.650s; timeout classified at internal 5.108s; root PID `26092` terminated; child PID `29888` absent; independent `Get-Process` found both absent.
- M1 portability self-test, stage 180s/self 5s: exit 0 in 80.954s; the same portability/CRLF/dirty/selector controls passed; internal timeout 5.137s; root PID `8220` terminated; child PID `12716` absent; independent checks found both absent.
- topology portability self-test, stage 180s/self 5s: exit 0 in 78.096s; A01 selector, scalar path, clean/CRLF/dirty channels, legacy-current-safe reinsertion rejection, and deadline ownership=`kill-on-close-job` passed; child PID `17820` was absent after internal 5.064s. Production topology output does not expose its root PID; the independent child check and M1 root/child checks found no sleeper survivor.
- separate production exact-positive and inherited-negative cases exited 0 in 6.247s and 5.911s with ACCEPT and REJECT respectively, exact 120-registry validation, deadline cleanup, and restoration.

A final independent Windows sweep found PIDs `26092`, `29888`, `8220`, `12716`, and `17820` absent. HEAD remained `977a4df...`, tree `c2d4258...`; worktree diff, cached diff, and untracked set were empty.

### Native Ubuntu 24.04

Evidence clone: `/root/rmq-aud1-ubuntu-019f8b68` on native ext4 under the explicitly authorized WSL2 `Ubuntu-24.04` distro. It remained detached at exact candidate/tree and clean after every control.

Identity: Ubuntu `24.04.4 LTS`, x86_64 WSL2 kernel `6.6.114.1-microsoft-standard-WSL2`; scalar `/usr/bin/pwsh` `7.6.4`, `/usr/bin/git` `2.43.0`, `/usr/bin/setsid` util-linux `2.39.3`, login-shell `/root/.elan/bin/lean` `4.22.0` (`ba2cbbf...`), and `/root/.elan/bin/lake` `5.0.0-src+ba2cbbf`.

- M1 selector self-test, stage 120s/self 5s: exit 0 in 245.656s. It reproduced the exact registry/selector/safe-dependency checks, native scalar production plan, CRLF normalization, and tracked/untracked/index channels.
- M1 deadline self-test, stage 300s/self 10s: exit 0 in 306.614s, with the stage chosen after observing the selector startup. Internal timeout 10.137s; root PID `3284` terminated; child PID `3330` absent; independent `kill -0` found both absent.
- M1 portability self-test, stage 360s/self 10s: exit 0 in 314.081s, with margin raised from the observed deadline run. Internal timeout 10.164s; root PID `4975` terminated; child PID `5020` absent; independent checks found both absent.
- topology portability self-test, stage 360s/self 10s: exit 0 in 307.543s. Topology selector, legacy safe-dependency anti-bypass, CRLF and every dirty channel passed with actual ownership=`setsid-process-group`; child PID `6803` was absent after internal 10.108s. Production topology output does not expose its root PID; `pgrep -af deadline-sleeper` and `pgrep -af topology-sleeper` found no survivor, while the two M1 controls independently emitted and cleared their roots.

The deadline progression 120s -> 300s -> 360s was based on observed 245.656s then 306.614s startup/control wall times. No wrapper timed out, no unchanged command was retried, and only one heavy process ran at a time. Final Ubuntu HEAD/tree were exact, with empty worktree diff, cached diff, untracked set, and porcelain-v2 state apart from detached-branch headers.

## Acceptance-ID dispositions

`PASS` means the exact isolated requirement is satisfied by the cited independent evidence bundle. `PASS (local)` on a completion row means its candidate-local evidence is complete; coordinator acceptance and integrated M1 closure remain downstream. Each frozen ID appears exactly once in this table.

| Stable ID | Disposition | Independent evidence |
|---|---|---|
| `M1-01` | PASS | B2: exact 24-field certificate and typed required-facts projection over the same objects. |
| `M1-02` | PASS | B2: complete ordered-dynamic `TraceResult` route; safe result is derived. |
| `M1-03` | PASS | B2: guarded list/canonical/controller/supplied-store equality chain. |
| `M1-04` | PASS | B2: literal payload, physical words, store, validity, result, trace, and cost identity. |
| `M1-05` | PASS | B2: paper theorem literally consumes required facts and exact agreement; expected-type checker pins it. |
| `M1-06` | PASS | B2: common valid guard and pure invalid packet; no unconditional raw packet. |
| `M1-07` | PASS | B2: consumed-word mutation changes the returned value projection. |
| `M1-08` | PASS | B2/B5/B7: checker anchors, unchanged current surfaces, category-accurate strict scan, clean trust scan. |
| `M1-INV` | PASS | B2/B3/B4: all expanded invariant rows below pass. |
| `INV-STORE-IDENTITY` | PASS | B2: counted payload erases from the exact physical words/store executed. |
| `INV-VALUE-DEPENDENCY` | PASS | B2: concrete value-projection dependency, not aggregate-record inequality. |
| `INV-SEMANTIC-NONVACUITY` | PASS | B2: predicates expand to evaluator/store/trace facts and a decisive consumed read. |
| `INV-TRACE-EXECUTION` | PASS | B2: trace and ordered footprint are projections of the same execution. |
| `INV-STORE-AGREEMENT` | PASS | B2: ordered dynamic agreement yields complete result equality. |
| `INV-READ-BACKING` | PASS | B2: successful reads have exact in-bounds cells in the counted store. |
| `INV-WORD-WIDTH` | PASS | B2: stored and returned words share the modeled reviewer width. |
| `INV-ADDRESS-WIDTH` | PASS | B2: physical, footprint, and operand address classes are covered. |
| `INV-ALL-SIZE` | PASS | B2: no readiness/compatibility size dispatch enters the guarded public route. |
| `INV-PROOF-SEPARATION` | PASS | B2/B5: proof fields establish properties but do not supply answers/routing. |
| `INV-NO-SYNTHETIC` | PASS | B2: accepted events are genuine reads and same-trace weight/cost is pinned. |
| `INV-CATEGORY-SEPARATION` | PASS | B2/B5: payload, proof, modeled ticks, execution, Lean runtime, and wall time remain distinct. |
| `INV-PUBLIC-COMPOSITION` | PASS | B2: guarded packet, literal paper theorem, and independent checker compose. |
| `INV-GLOBAL-PHYSICAL-MACHINE` | PASS | B2: one flattened physical store and execution back the public statement. |
| `INV-WIDTH-SCALING` | PASS | B2: logarithmic width and linear capacity propositions remain live. |
| `INV-CERTIFICATE-ANTI-BYPASS` | PASS | B2: 24 projections and checker/registry anchors prevent field or consumer bypass. |
| `INV-MUTATION-REPRODUCIBILITY` | PASS | B1/B2/B3/B4: committed registries, exact selectors, production verdicts, and clean restoration are replayable. |
| `M1R2-FIELD-CONSUMER` | PASS | B2: every required field is projected explicitly at its exact type/object. |
| `M1R2-SAFE-PRIMARY` | PASS | B2: ordered dynamic theorem is primary; safe theorem factors through it. |
| `M1R2-MATRIX-SCHEMA` | PASS | B1: strict acceptance-section parser gives exact ordered eight-cell rows. |
| `M1R2-PUBLIC-WORDING` | PASS | B2/B5: current public wording matches exact dynamic/safe/category boundaries. |
| `M1R2-COMMITTED-HYGIENE` | PASS | B1/B7: exact committed blobs and clean trust/hygiene scans. |
| `M1R3-PUBLIC-TYPE-PIN` | PASS | B2: independent theorem-value expected type is present and exact. |
| `M1R3-REPLAYABLE-MUTATIONS` | PASS | B2/B4: committed mutation registry/topology wiring and focused replay controls. |
| `M1R3-EXPECTED-ACCEPT-CONTROL` | PASS | B2/B3: expected-accept discrimination remains committed; exact new positive executes. |
| `M1R3-GATE-TOPOLOGY` | PASS | B2/B4: A01/A02 anchors and production topology ownership controls remain intact. |
| `M1R3-COMMITTED-HYGIENE` | PASS | B1/B7: committed exact-tree and clean-state evidence. |
| `M1R4-EXACT-REGISTRY` | PASS | B2: production self-test confirms the exact 41-case/24-field registry. |
| `M1R4-SELECTOR-NONVACUITY` | PASS | B3/B4: valid unique selectors run; omitted/empty/unknown/missing/duplicate cases discriminate. |
| `M1R4-MUTATION-FIDELITY` | PASS | B2/B3: production checker/policy surfaces are used, not copied detectors. |
| `M1R4-SUBPROCESS-DEADLINE` | PASS | B3/B4: positive timeout classification, owned-tree cleanup, and no survivor. |
| `M1R4-DESIGN-LOG` | PASS | B5: protected decisions and enforcement sources agree; logs remain tier 5. |
| `M1R4-GATE-TOPOLOGY` | PASS | B2/B4: checker/gate/topology anchors and focused ownership paths are intact. |
| `M1R4-COMMITTED-HYGIENE` | PASS | B1/B7: exact objects, clean working/index/untracked state, and trust scans. |
| `REQ-M1R5-CURRENT-BASE-FORWARD-PORT` | PASS | B1/B5: exact governed parents/trees and non-owned blob identity. |
| `REQ-M1R5-COST-210-DERIVATION` | PASS | B2: accepted component algebra and same-trace `210`/`<= 210` propositions. |
| `REQ-M1R5-SEGMENT23-REGISTRY` | PASS | B2: 22 physical sources, logical `0..22`, and direct `< 23` containment. |
| `REQ-M1R5-SCOPE-S1-SEPARATION` | PASS | B2/B5: structured M1 store route remains separate from S1/E1/A1 and controller charging. |
| `REQ-M1R5-CURRENT-FRONTIER-PRESERVATION` | PASS | B1/B5: all non-owned/current-surface blobs and governance are preserved. |
| `REQ-M1R5-PUBLIC-EXPECTED-TYPE-CONSUMER` | PASS | B2: independent expected-type definition consumes the literal theorem value. |
| `REPLAY-EXACT-REGISTRY` | PASS | B2: exact production registry self-test passed. |
| `REPLAY-SELECTOR-NONVACUITY` | PASS | B3/B4: selector boundary controls are non-vacuous and reject unknown/nonunique input. |
| `REPLAY-SUBPROCESS-DEADLINE` | PASS | B3/B4: timeout path terminates owned root/child state. |
| `COMPLETE-M1R5-COMMITTED-EVIDENCE` | PASS (local) | B1–B7: exact candidate-local proposition, registry, platform, governance, and clean-tree evidence. |
| `REQ-M1R5R1-DIRECT-SEGMENT23-CONTAINMENT` | PASS | B2: direct source/program topology proves each supplied read segment `< 23`. |
| `REQ-M1R5R1-LEGACY-SAFE-NONDEPENDENCY` | PASS | B2: load-bearing blocks exclude the legacy theorem and use ordered-read equality. |
| `REQ-M1R5R1-BOUND-EMPTY-DISTINCTION` | PASS | B2/B3: bounded work accepts; zero-remaining claims reject; invalid guards stay pure. |
| `REQ-M1R5R1-CROSS-PLATFORM-PROCESS-TREE` | PASS | B4: Windows job and Ubuntu process-group ownership are exercised. |
| `REQ-M1R5R1-CLEAN-BASELINE` | PASS | B3/B4: CRLF/tracked/untracked/index channels and restoration are checked. |
| `REQ-M1R5R1-CATEGORY-WORDING` | PASS | B2/B3/B5: bounded silent work is stated without claiming full instruction charging. |
| `REQ-M1R5R1-CLAIM-POLICY-REGRESSION` | PASS | B3: exact production negative/positive and bypass boundaries execute. |
| `REQ-M1R5R1-EVIDENCE-TRUTH` | PASS | B1–B5: lower-tier reconstruction agrees with the candidate append; worker receipts are not promoted. |
| `REQ-M1R5R1-EXACT-TREE-ECONOMICS` | PASS | B1/B7: focused checks only; prohibited unchanged broad suites were not duplicated. |
| `COMPLETE-M1R5R1-COMMITTED-EVIDENCE` | PASS (local) | B1–B7: inherited repair obligations independently reconstructed at the exact candidate. |
| `REQ-M1R5R2-NORMALIZATION-SAFE-STATE` | PASS | B4: native/default-conversion clean baselines and normalization-safe observer. |
| `REQ-M1R5R2-CRLF-CLEAN-FIXTURE` | PASS | B4: CRLF clean control and all three dirty channels discriminate. |
| `REQ-M1R5R2-REPLAY-UNBLOCKED` | PASS | B3/B4: selector/deadline/portability/topology reach intended verdict stages. |
| `COMPLETE-M1R5R2-COMMITTED-EVIDENCE` | PASS (local) | B1/B4/B7: exact committed process-control artifacts and fresh platform evidence. |
| `REQ-M1R5R3-OPEN-ROW-NONCOMPLETION` | PASS | B1/B5: local evidence is separated from coordinator acceptance; no blank/Open cell is treated as failure or self-acceptance. |
| `REQ-M1R5R3-POST-COMMIT-EVIDENCE-DURABILITY` | PASS | B1–B4: committed selectors/fixtures and exact post-commit replay evidence. |
| `REQ-M1R5R3-ONE-COMMIT-PARENT` | PASS | B1/B7: candidate parent and range count are exact; tree is clean. |
| `COMPLETE-M1R5R3-COMMITTED-EVIDENCE` | PASS (local) | B1–B7: durability and exact candidate-local evidence survive independent reconstruction. |
| `REQ-M1R5R4-CURRENT-LEAN-SOURCE-COMMENT-COVERAGE` | PASS | B2: exact four-file raw comparison proves only the two comment substitutions. |
| `REQ-M1R5R4-CLAIM-POLICY-ALLOWANCE-BYPASS` | PASS | B3: former words, held-outs, path forms, negated prefix, exact positive, and bounded near misses all classify causally. |
| `REQ-M1R5R4-NATIVE-UBUNTU-EVIDENCE` | PASS | B4: genuine Ubuntu 24.04 native-filesystem execution with scalar tools and process-group ownership. |
| `REQ-M1R5R4-ONE-COMMIT-PARENT` | PASS | B1/B7: exact inherited repair ancestry and clean state are preserved. |
| `COMPLETE-M1R5R4-COMMITTED-EVIDENCE` | PASS (local) | B1–B7: source comments, production policy, native process controls, ancestry, and hygiene close locally. |
| `REQ-M1R5R5-CURRENT-GOVERNANCE-PRESERVATION` | PASS | B1/B5/B6: exact governance ancestor, protected bytes, and zero changed current surfaces. |
| `REQ-M1R5R5-IMMUTABLE-CANDIDATE-HANDOFF` | PASS | B1/B7: immutable candidate identity/tree/range and clean handoff state. |
| `COMPLETE-M1R5R5-COMMITTED-EVIDENCE` | PASS (local) | B1/B5–B7: governed immutable handoff is independently reproducible. |
| `REQ-M1R5R6-STRICT-DESIGN-SCOPE-CLOSURE` | PASS | B2/B5: DD/WDD enforcement matches the exact comment/policy scope; strict design passes. |
| `REQ-M1R5R6-UNTRUSTED-DIRTY-SALVAGE` | PASS | B4: tracked, untracked, index, and normalization mutations reject and restore. |
| `REQ-M1R5R6-ONE-COMMIT-PARENT` | PASS | B1/B7: exact parent/range/four-path/clean state. |
| `COMPLETE-M1R5R6-COMMITTED-EVIDENCE` | PASS (local) | B1–B7: design/write scope and platform-sensitive evidence close locally. |
| `REQ-M1R5R8-MARKDOWN-EIGHT-CELL-INTEGRITY` | PASS | B1: strict decoder preserves all 87 inherited rows including the escaped category delimiter. |
| `REQ-M1R5R8-CURRENT-GOVERNANCE-PRESERVATION` | PASS | B1/B5/B6: protected governance/decision bytes and non-owned blobs are exact. |
| `REQ-M1R5R8-ONE-COMMIT-PARENT` | PASS | B1/B7: R8/candidate ancestry and exact candidate one-commit range are reconstructed. |
| `COMPLETE-M1R5R8-COMMITTED-EVIDENCE` | PASS (local) | B1/B5/B7: inherited matrix repair remains durable and exact. |
| `REQ-M1R5R9-EXACT-POSITIVE-REPLAY-FIXTURE` | PASS | Verbatim requirement: reconstruct the frozen requirement from the exact R8 matrix and establish that the exact sentence is absent outside the matrix/audit evidence while the materially different `m1r5-bounded-event-silent-distinction-accepted` fixture remains. Preserve that existing fixture byte-for-byte. Add exactly one new distinct fixture ID, `m1r5r9-exact-frozen-bounded-event-silent-distinction-accepted`, immediately after it. The new object uses `docs/PAPER_MODEL_ADEQUACY.md`, `reject = $false`, term ID `forbidden-unqualified-no-event-silent-computation`, and the exact sentence above. Insert the same ID at the corresponding position in `$expectedFixtureIds`, update only `$expectedAcceptCount` from 37 to 38, and retain 82 rejects plus 16 context cases. The registry must contain exactly 120 ordered unique fixtures; duplicate, missing, and verdict-drift controls must remain effective. The new exact fixture and the existing named unqualified reject control must both execute through the production final verdict with their expected outcomes, restoration, and clean state. B1/B3 close every clause. |
| `REQ-M1R5R9-CURRENT-GOVERNANCE-PRESERVATION` | PASS | Verbatim requirement: preserve exact ancestry to both private-base parents and current governance, including WDD-20260722-003/004/005/006/007/008/009, DD-20260722-001, `ARCH-CONTRACT-NO-ASSUMED-CAPSTONE`, `STRICT-DESIGN-CHECK-WRITE-SCOPE-CLOSURE`, `FROZEN-ACCEPTANCE-ROW-BYTE-INTEGRITY`, and `NAMED-REGRESSION-REALITY`. Add WDD-20260722-010 documenting why the exact positive fixture is required, why replacing the broader existing fixture or weakening the production policy was rejected, the exact R8 negative fixture/audit evidence, consequences, focused verification, and publication-facing significance. This ledger entry records the workflow-sensitive fixture mutation; it creates no broader allowance or new process rule. Every non-owned path must have the exact base blob. B1/B5/B6 close every clause. |
| `REQ-M1R5R9-ONE-COMMIT-PARENT` | PASS | Verbatim requirement: final `HEAD^` is exactly `c9375cf83a55c122b27c56a73c6027f36faea643`; the range count is one; exactly the four owned paths change; final tracked, untracked, and index state is clean; no owned process survives. B1/B4/B7 close every clause. |
| `COMPLETE-M1R5R9-COMMITTED-EVIDENCE` | PASS (local) | Verbatim requirement: one exact-parent commit contains the exact 120-fixture registry and focused production verdicts, complete 91-ID/eight-cell matrix, truthful R9 digestion/WDD entry, strict inherited-row receipts, exact range/blob checks, and no open local residual. Coordinator acceptance and fresh-blind audit remain downstream. B1–B7 close the candidate-local clauses; this report supplies the downstream fresh-blind audit but does not record coordinator acceptance. |

## Stale and rejected objections

- **The broader positive was already enough.** Rejected: it is materially different from the exact frozen sentence. The exact sentence was absent from the base production registry and now has its own committed selector without replacing the broader control.
- **The classifier or allowance had to change.** Rejected: byte reconstruction proves no policy/scanner change; the exact sentence already accepts. Former allowance words and policy paths still reject the false zero-remaining category.
- **A disposable file or transcript closes the requirement.** Rejected: the new object and selector are committed in the production registry, aligned with the exact expected-ID list and counts.
- **The legacy supplied-store theorem remains load-bearing.** Rejected by expanded proof bodies and exact-token scans of every downstream load-bearing block.
- **The `210` bound is detached or synthetic.** Rejected by same-trace weight/length/cost propositions and genuine-read-only event evidence.
- **The matrix can be checked by rendered/count-only comparison.** Rejected: strict raw rows, UTF-8, delimiter parity, exact order, and byte identity were checked.
- **Candidate or branch names, worker timings, logs, or clean state prove success.** Rejected as methodology. They were treated as hypotheses; evidence came from exact objects, source propositions, production executions, and fresh platform runs.

## Commands, durations, and verification economics

| Command/check | Wall time | Result and unique risk covered |
|---|---:|---|
| `powershell -ExecutionPolicy Bypass -File scripts\project_skill_preflight.ps1 -GovernanceRef b07fcc... -AllowNoRequiredSkills -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"` | 5.7s lead; 7.3–7.9s detached leaves | PASS; governance/runtime-role mismatch |
| `git cat-file -p`, `rev-list --count`, `merge-base --is-ancestor`, recursive `diff-tree` | 1.661–5.5s | exact parents/count/tree/four-path scope |
| raw `git cat-file blob` strict-decoder/assertion program | 0.451s matrix; 3.066s digest; 0.300s fixture; 0.200s reconstruction | malformed/normalized rows, inherited-byte drift, fixture/order/count drift |
| `powershell ... claim_drift_scan.ps1 -Strict` | 19.248s | 1,439 hits, zero strict failures |
| `powershell ... design_decision_check.ps1 -Strict -Base c9375cf...` | 2.047s | 0 code, 1 workflow, 3 neutral; unauthorized design/write scope |
| 19 focused `claim_drift_policy_regression.ps1 -OnlyCase <id>` invocations | 137.889s | exact positive/negative and causal category/bypass boundary |
| `claim_drift_policy_regression.ps1 -AbsoluteWindowsOnly` | 13.907s | absolute/single-file normalization and policy-path bypass |
| unknown `-OnlyCase m1r5r9-does-not-exist` | 1.350s | expected exit 1; selector vacuity/nonuniqueness |
| `m1_certificate_mutation_regression.ps1 -RegistrySelfTestOnly` | 2.197s | exact 41 IDs, 24 fields, 40/1 verdicts, F21 omission/duplication |
| theorem/body/comment raw reconstruction | focused static inspection | same-object chain, legacy nondependency, exact 210/source/width/guard/value facts, source-neutral comment repair |
| Windows `m1_certificate_mutation_regression.ps1 -SelectorSelfTestOnly -StageDeadlineSeconds 120 -SelfTestDeadlineSeconds 5` | 86.905s | registry/selector/direct-chain/CRLF/dirty channels; exit 0 |
| Windows same script `-DeadlineSelfTestOnly -StageDeadlineSeconds 180 -SelfTestDeadlineSeconds 5` | 92.650s | timeout; root `26092`/child `29888` absent; exit 0 |
| Windows same script `-PortabilitySelfTestOnly -StageDeadlineSeconds 180 -SelfTestDeadlineSeconds 5` | 80.954s | portability; root `8220`/child `12716` absent; exit 0 |
| Windows `paper_topology_lint_regression.ps1 -PortabilitySelfTestOnly -StageDeadlineSeconds 180 -SelfTestDeadlineSeconds 5` | 78.096s | kill-on-close topology; child `17820` absent; exit 0 |
| Ubuntu native M1 `-SelectorSelfTestOnly -StageDeadlineSeconds 120 -SelfTestDeadlineSeconds 5` | 245.656s | scalar tools, registry/selector/CRLF/dirty controls; exit 0 |
| Ubuntu native M1 `-DeadlineSelfTestOnly -StageDeadlineSeconds 300 -SelfTestDeadlineSeconds 10` | 306.614s | setsid timeout; root `3284`/child `3330` absent; exit 0 |
| Ubuntu native M1 `-PortabilitySelfTestOnly -StageDeadlineSeconds 360 -SelfTestDeadlineSeconds 10` | 314.081s | setsid portability; root `4975`/child `5020` absent; exit 0 |
| Ubuntu native topology `-PortabilitySelfTestOnly -StageDeadlineSeconds 360 -SelfTestDeadlineSeconds 10` | 307.543s | actual setsid process-group; child `6803` and all sleepers absent; exit 0 |
| `git merge-tree --write-tree b07fcc... 977a4df...` | 0.128s | exit 0, candidate tree, zero integration conflicts |
| hygiene scans for forbidden trust tokens and native decision shortcuts | 2.439s lead; 0.139s detached | zero matches |
| `git diff --check c9375cf...977a4df` | 1.007s detached | PASS; candidate whitespace/patch corruption |
| final report-tree strict claim/design/staged-diff checks | 9.7–12.8s / 1.6–2.0s across precommit passes / focused Git check | 1,444 claim hits with 0 failures; report path classified neutral; staged diff check PASS. Exact committed-tree repeats are recorded in the handoff. |

The full 41-case semantic replay, full 120-case policy campaign, full topology suite, aggregate gate, broad Lean build, startup smoke, exact F21 compile, and unrelated platform suites were deliberately skipped. The candidate changes no Lean/model/topology implementation and makes an exactly reconstructed additive policy-fixture mutation. Focused source, registry, causal policy, selector/deadline/portability, and platform checks cover the changed and platform-sensitive risks without duplicating unchanged broad suites.

## Proof digestion and status

Conceptually, this candidate adds no theorem, classifier language, policy allowance, public claim, platform architecture, or machine behavior. It turns an already-accurate frozen sentence into a durable, uniquely selectable production expected-accept fixture while retaining the broader accurate positive and the false unqualified negative.

In plain English: the repository already knew the exact sentence was truthful, but the replay suite did not contain that exact wording. It now does, and the stronger false claim still fails.

Live assumptions are limited to the inherited explicit model: structured pre-execution stores rather than S1 serialization, event-cost rather than fully charged controller/runtime cost, Lean/Std plus `omega`, the checked all-size half-open leftmost RMQ contract, and the exact local main/governance identity recorded above. Platform observations are executions on the named host/distro, not universal performance claims.

Local rung status: the isolated R9 repair is audit-accepted. Integrated-node status: M1 remains open until the coordinator independently audits this report, integrates under then-current governance, and records acceptance. No integration action occurred here.

Time economics: cheap identity/raw/policy checks preceded execution; the audit used focused cases and self-tests only. The most expensive work was the required platform/process reconstruction, not a duplicated aggregate build. This preserves the frozen one-heavy-process-per-tree and no-repeat economics.

A skeptical graduate student should next ask whether the coordinator can reproduce the strict 91-row/120-fixture predicates and fast-forward integration from the exact report commit without losing a governance byte.

Best next action: coordinator audits this exact report commit, rechecks then-current main/governance, and integrates the candidate/report only if that identity remains compatible.
