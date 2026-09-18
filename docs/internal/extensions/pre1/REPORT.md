Status: CANDIDATE_COMPLETE
I found no assigned or inherited acceptance criterion unmet; coordinator acceptance is still required.
Phase: FINAL_CANDIDATE

Aggregate slot request: please schedule the host-wide `scripts/gate.ps1`
aggregate on the frozen final candidate commit (the commit adding
WDD-20260913-PRE1-025 on top of `02aa9455e9c7b57ca57b8a2b05d1f8da0d1a21dd`; its
SHA is in the task response),
followed by the fresh blind exact-commit audit. The builder checker
`PRE1-BUILDER-REPLAY` needs up to 10800 s (measured full replay 4573.59 s).

# PRE-1 final candidate report

| Item | Value |
| --- | --- |
| Handle and title | PRE-1, `(PRE-1) Prove efficient packed preprocessing` |
| Branch and worktree | `codex/pre-1-packed-preprocessing`, `C:/Users/poin/.codex/worktrees/2fb8/RMQ` |
| Base | contract commit `c1c970b8bfbae03163633365e512d487ae1c98f2` (governance base `0e6a00f654abc64f8b68988fa9675b9a839dca2f`) |
| Candidate | the commit adding WDD-20260913-PRE1-025 on top of the report commit `02aa945` (which is on top of `babfbef`); Lean sources identical to `cb2ba2cf9f6b0bcd2a6d1dca490c2dccd51cab3a` |
| Changed paths (`c1c970b..babfbef`) | 100 files: `RMQ/Core/WordRAM/Construction/{Program,Calculus,Safety,Structured,Compiler,Loop,ArrayRun,HeaderUse,Capstone}.lean`, `Builder/` (10), `Spec/` (12), `Proof/` (42); `RMQ/Validation/{Preprocessing,PreprocessingContract}.lean`; `scripts/preprocessing_{builder_check,contract_check,spec_check,stage_check}.lean`, `scripts/preprocessing_{builder_firewall,builder_gate,builder_replay,contract_gate}.ps1`, `scripts/gate.ps1` (two roster entries); `lakefile.toml` (one stanza); `docs/internal/extensions/pre1/` (10), the Stage 0 audit report copy, DESIGN_DECISIONS.md, WORKFLOW_DESIGN_DECISIONS.md, `docs/FAMILY_SUMMARY.md`, `docs/DIGESTION_LOG.md` |
| Matrix | `docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md`, section "Final candidate review" (31 rows) |
| Commands | BUILDER_STAGE_LOG.md sections "Replay extension" and "Final candidate checks" |

## F.1 Main checked statements

| Declaration | Checked type (abbreviated only where noted) |
| --- | --- |
| `PackedConstruction.Proof.efficientBuild_eq_buildMemory` | `∀ xs : List Int, efficientBuild xs = PackedWordRAM.buildMemory xs` |
| `PackedConstruction.Proof.efficientBuildWord_eq_buildMemory` | `∀ xs : List Int, InputFits (wordWidth xs.length) xs → efficientBuildWord (wordWidth xs.length) xs = buildMemory xs` |
| `PackedConstruction.constructionAndQueryCapstone_holds` | `ConstructionAndQueryCapstone` (23 fields, each restated at full type in `RMQ/Validation/PreprocessingContract.lean`); axioms `[propext, Classical.choice, Quot.sound]` |
| `BuilderRunFacts builderProgram (comparisonInputState xs) xs` (field `comparisonRun`, every `xs`) | halting; `steps ≤ 1000000000 * n + 1000000000`; fuel insensitivity; ten-category partition; output cells equal `buildMemory xs` with per-cell last-write provenance; `outBase - extent₀ ≤ 3200000 * n + 3200000`; peak and every-prefix extent bounds; registers `≥ 400` zero; initial and final fit and `Run.Safe (wordWidth n)`; no input writes; input and keys retained; write replay; clean tail; read and supplied-store agreement; array-backed reflection |
| `wordRun` | the same facts for `builderProgramWord` on `wordInputState (wordWidth n) xs` under `InputFits (wordWidth n) xs` |
| `programStatic`, `programStaticWord` | every instruction: operands fit `wordWidth n`, registers below 400, branch and jump targets below the program length, no `jumpRegister` |
| `queryOnEmitted`, `queryOnEmittedWord` | `PackedQueryOn (efficientBuild xs) xs` (22 PQ1 facts on the emitted cells); word version under `InputFits` |
| `jointCapacity`, `jointResidualLittleO` (`n = xs.length`) | `((buildMemory xs).length + (queryProgramWords + programWords builderProgram + programWords builderProgramWord) + (queryScratchWords + 400)) * wordWidth n ≤ 2 * n + constructionCompleteRho n`; `LittleOLinear constructionCompleteRho` |

## F.2 Command outcomes on the candidate

| Check | Outcome |
| --- | --- |
| Full builder replay (52 cases, capstone baseline, validator stage; `cb2ba2c`) | PASS, 541 stages, 54 self-tests, all restorations EXACT, 4573.59 s (R-7) |
| Contract replay (`cb2ba2c`) | PASS 18/18, registry hash unchanged, 289.32 s (R-8) |
| `lake build`; capstone and validator targets | exit 0 (R-11a, R-11b) |
| Typed consumers (capstone, builder, contract, stage) | all PASS markers, 0 errors (R-11c..R-11f) |
| `lake exe rmq_preprocessing_validate` | `PRE1-VALIDATE PASS cases=11 mode=full`, 271.72 s (R-11g); negatives rejected in R-7 |
| Axiom inventories | 259 S7/S8 names and 24 validator names, 1,721 stage inventories: all within {propext, Classical.choice, Quot.sound} |
| Trust scans | only the docstring word `sorry` at `PreprocessingContract.lean:12`; no `native_decide`/`Lean.ofReduceBool` (R-12) |
| `git diff --check` from `c1c970b` and `0e6a00f` | exit 0 (R-13) |
| `design_decision_check.ps1 -Strict` from `c1c970b` and `0e6a00f` | exit 0; four single commits fail alone (`75a6301`, `6ccfb5c`, `fa8e34e`, `02aa945`), each repaired by the next commit (R-13, R-15) |
| `claim_drift_scan.ps1 -Strict` | exit 0, 0 strict failures (R-11h; rerun on the report commit, see task response) |
| `claim_drift_scan.ps1 -SelfTest` | exit 1, pre-existing parser finding outside this lane's scope (R-11i, WDD-20260913-PRE1-021) |

## F.3 Unexecuted checks and limits

- Not executed: `scripts/gate.ps1` (coordinator); the two gate checkers in
  isolation after the builder checker's deadline change (parser checks only;
  the checker wraps the replay run in R-7); the POSIX process-ownership branch;
  `constant_sync_check.ps1` (no governed constant restated).
- Ruling Q3: the query is joined through the list equality and a lifted
  simulation on the detached emitted list; no offset-relocated in-place query
  execution is claimed.
- The literals are crude upper bounds; no tightness or optimality is claimed.
- The validator reaches `n = 129`; the `n = 1116` dense edge and the select
  flag thresholds (`superIsLong` possible from `n = 5489`, sparse exceptions not
  below `n = 200000`) are beyond the reference allocation's runtime.
- Deferred to the coordinator by the brief: the `RMQ.lean` import of the
  capstone and consumer, the Headlines alias and claim vocabulary, the axiom
  script entry, paper and campaign integration.

## F.4 Proof digestion

What changed conceptually: the packed allocation the accepted query reads is
now produced inside the same counted machine discipline. One source template,
instantiated with a key-oracle leaf and a word leaf, compiles to two closed
programs; a compositional calculus for structured blocks, a static pointer
flow for ownership and per-phase frame lemmas turn stage specifications into
facts about the single actual run, and the capstone carries the accepted PQ1
facts over the proved list equality.

In plain English: for every input list, running one fixed program for at most
a billion steps per element (plus a billion) leaves exactly the cells the query
expects, using at most about three million temporary cells per element, never
touching the input, never overflowing a word, and with each output cell traced
to the store that wrote it; the query then answers correctly on those cells.

Live assumptions: unit-cost primitive operations of the frozen construction
machine at `wordWidth n` bits (including multiplication, division and shifts);
the comparison oracle for arbitrary integers; `InputFits` for the word model;
the accepted PQ1 query theorem.

Named downstream consumers: the coordinator's aggregate gate
(`PRE1-CONTRACT-GATE`, `PRE1-BUILDER-REPLAY`), the fresh blind audit, then the
coordinator's `RMQ.lean` integration and headline alias.

A skeptical graduate student would ask: how far the constants are from the
real per-element cost; whether the temporary space bound (words, not bits) is
the right target next to the `2n + o(n)` output; whether the static pointer
flow could hide a write below the extent in a phase whose flow fact was
checked only on the compiled source; why the query is not executed in place at
the builder's output base; and what the select-flag thresholds would show if a
faster reference allocation existed.

## F.5 Lane history

Stage 0 landed the audited contract amendments and the operational foundations
(`5f325ddb856b9095d1ad2aacc0bc69eda571d447`); the continuation audit PRE-1-A1C
returned CONTINUATION_PASS_WITH_CONDITIONS and the coordinator accepted
conditions C1-C3. S1 is complete as specification (`b3570ac`, `22c0c20`); C1
landed as `361fe82`; S2 as `160593f` and `6a826849c20abc0bf97f2580d80922438d36c47c`;
S3 as `f565adcde1682978999dead41db96d307e79ce1b`; the S4 checkpoint as
`0192fdd8a05b1bb47c65e5027923e51b116e656b`; S4 as
`4340632e623016921dbf1c66a3b6b10e6a088b4e`; S5 as
`e3e71dea6b5e99768938963d30a9dd31a3e85d84`; S6 as
`5af951da24381c45bda585b04ea9b4b43695ba9f`; C2 as
`6df96d6033ad2a7bbb868f5d89814fb3c2ebdcc0`; C3 as
`75a6301f5db7d3d6e893cbb2a1a73e1ed5522a13` with its design record
`46af19c76153822bc9cc32ea4490785ea4b6df81`. The coordinator authorized S7 and
S8 under rulings R-S7-1..R-S7-4. The S7 checkpoint
`5dff46edf0d4d7a01a775afeddb8a3259249e9d4` landed the arrays, the metadata
bank, the metadata words, the dense words and the tail-stage theorem from the
geometry bank to `buildMemory xs`, without the program constants, because
CONTRACT.md V3-6's fuel body `builderBudget n = C * n + D` cannot be checked by
the kernel at any admissible `D` (section S7.3 of the checkpoint report). The
coordinator ruled (R-S7-5..R-S7-9, record `PRE1_S7_V36_RULING.md`): the fuel body
becomes `builderBudget n = D + C * n` (amendment V3-6a, recorded in
`48e590c` together with the stage-consumer marker gating and the builder gate
deadline note). The R-S7-7 leaf restructure landed as `6ccfb5c` (records
`dc00e43`). The program constants, both exactness theorems, the V3-1..V3-6
consumer pins and the V3-7 (i)/(ii) and V3-1 replay cases landed as
`48702c20a5708b6ea1efcd05a51faa0790a15ac1`. On that commit the full builder
replay passed 34/34 (1535.87 s) and the contract replay 18/18 (263.2 s), so
V3-7 case (i) passes and S8 may start (R-S7-1). The records commit `1676952`
raised the builder gate deadline to 3600 s on that measurement and recorded a
`claim_drift_scan.ps1 -SelfTest` failure whose cause lies outside this lane's
write scope (section S7R). On top of it, stage S8 proves the capstone
`constructionAndQueryCapstone_holds` in `RMQ/Core/WordRAM/Construction/Capstone.lean`
with its typed consumer `RMQ/Validation/PreprocessingContract.lean`
(`45abca5d82224f43b3eb6e53bb9348c6ec07b924`). The replay extension adds the validator executable and its lakefile stanza, the static
program facts as two capstone fields, the safety definition pins and eighteen
registry cases (C3 foundations, capstone consumer, quadratic control, program
host import, `Cw`/`Dw` numerals, accept control), each surface observed before
registration (`cb2ba2cf9f6b0bcd2a6d1dca490c2dccd51cab3a`). On that commit the
full builder replay passed 52/52 with the capstone baseline and the validator
stage (4573.59 s) and the contract replay 18/18 (289.32 s); the records commit
`fa8e34eec0b56f01710906cd67b5913d1d132667` raised the builder gate deadline to
10800 s and appended the family and digestion entries, and
`babfbefe9e1b047480921bdad31de4e4e77624c5` added their design record. The final
checks, the row-by-row review and this report follow; the coordinator's
aggregate gate and blind audit are next.

# PRE-1 replay extension report

| Item | Value |
| --- | --- |
| Parent | `45abca5d82224f43b3eb6e53bb9348c6ec07b924` (S8 capstone) |
| Commit | the replay extension commit on top of `45abca5`; its SHA is reported in the task response |
| Changed paths | new `RMQ/Validation/Preprocessing.lean`, `RMQ/Core/WordRAM/Construction/Proof/Static.lean`; `Capstone.lean` (import, fields `programStatic`, `programStaticWord`); `Proof/RunFacts.lean` (the `noInputWrites` proof by `omega`); `RMQ/Validation/PreprocessingContract.lean` (two projections, axiom inventory, witness); `lakefile.toml` (`rmq_preprocessing_validate` stanza only); `scripts/preprocessing_builder_check.lean` (safety definition pins); `scripts/preprocessing_builder_replay.ps1` (profiles, validator stage, 52 IDs, registry pin); `builder_cases.json` (B35-B52); DESIGN_DECISIONS.md (DD-20260913-PRE1-019); WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-023); BUILDER_REPLAY_DESIGN.md; BUILDER_STAGE_LOG.md (R-V1..R-V3, R-1..R-6); ACCEPTANCE_MATRIX.md (replay extension appendix); REPORT.md |
| Commands | BUILDER_STAGE_LOG.md section "Replay extension" |

## RE.1 Declarations and checks (checked types)

| Declaration or check | Status | Checked statement |
| --- | --- | --- |
| `Structured.Block.compile_targets` | PROVED | `∀ block base, base + block.size < 2 ^ 32 → ∀ i ∈ block.compileAt base, (∀ c t, i.primitive = .branchZero c t → t.val ≤ base + block.size) ∧ (∀ t, i.primitive = .jump t → t.val ≤ base + block.size) ∧ (∀ src, i.primitive ≠ .jumpRegister src)` |
| `Proof.builderProgram_static`, `Proof.builderProgramWord_static` | PROVED | `∀ n, ∀ i ∈ builderProgram, i.primitive.OperandsFit (wordWidth n) ∧ i.primitive.RegistersBelow 400 ∧ (∀ c t, i.primitive = .branchZero c t → t.val < builderProgram.length) ∧ (∀ t, i.primitive = .jump t → t.val < builderProgram.length) ∧ (∀ src, i.primitive ≠ .jumpRegister src)` (same for `builderProgramWord`); axioms `[propext, Quot.sound]` |
| `constructionAndQueryCapstone_holds` | PROVED | `ConstructionAndQueryCapstone`, now 23 fields (the two static fields appended) |
| `safety_safeAt_arms`, `safety_run_safe_definition`, `safety_fits_definition` (builder consumer) | CHECKED (`Iff.rfl`) | the thirteen `Prim.SafeAt` arms, `Run.Safe W program r ↔ ∀ t ∈ r.transitions, Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W`, and the five `State.Fits` conjuncts |
| `rmq_preprocessing_validate` | EXECUTED (R-V3) | eleven fixtures in both models, `PRE1-VALIDATE PASS cases=11 mode=full`; four negative controls fail with their pinned messages |
| Registry B35-B52 | OBSERVED (R-1, R-3) | every rejection at exactly its registered stage and line set, restoration EXACT; B44 and B52 PASS |

## RE.2 Limits and residuals

- The validator's largest fixture is `n = 129`; the `n = 1116` dense edge is
  not executed (the reference allocation did not finish in ten minutes).
- The static fields are facts about the instruction lists; the executed run's
  safety remains the per-transition `Run.Safe` field.
- The surfaces were observed by focused runs; the full 52-case replay on the
  committed tree is still due.

# PRE-1 stage S8 capstone report

| Item | Value |
| --- | --- |
| Parent | `1676952db02ff133c7c3a236ac610bb3c827c0b6` (S7 records) |
| Commit | the S8 capstone commit on top of `1676952`; its SHA is reported in the task response |
| Changed paths | new `RMQ/Core/WordRAM/Construction/Proof/{Flow,FlowFacts,Frames,Ownership,RunFacts,Query,Lift}.lean`, `RMQ/Core/WordRAM/Construction/Capstone.lean`, `RMQ/Validation/PreprocessingContract.lean`; DESIGN_DECISIONS.md (DD-20260913-PRE1-018); BUILDER_STAGE_LOG.md (S8-1..S8-10); ACCEPTANCE_MATRIX.md (S8 appendix); REPORT.md |
| Commands | BUILDER_STAGE_LOG.md section "Stage S8" |

## S8.1 Declarations (checked types; the consumer restates every field at full type)

| Declaration | Status | Checked statement |
| --- | --- | --- |
| `Proof.EvalG.ptrFlow_sound` | PROVED | for every `P`, `e0`, evaluation `EvalG P b s s' k` and lists `I I'` with `ptrFlow b I = some I'`, `PtrsAbove e0 I s` and `e0 ≤ s.extent`: `EvalG (fun u op => P u op ∧ StoreAbove e0 u op) b s s' k`, `s'.status = .running → PtrsAbove e0 I' s'`, `e0 ≤ s'.extent` |
| `Proof.flow_builderSource_key`, `Proof.flow_builderSource_word` | PROVED | `ptrFlow (builderSource keyLeaf) [] = some [10, 3, 224, 108, 119, 220, 102, 101, 100, 136, 135, 118, 117, 116, 115, 164, 163, 162, 161, 160, 159]` (same for `wordLeaf`) |
| `Proof.wo_builderBody_key`, `Proof.wo_builderBody_word` | PROVED (per phase, V3-9) | `(builderBody leaf).WritesOnly (fun r => r ≠ 1)` |
| `Proof.rb_builderBody_key`, `Proof.rb_builderBody_word` | PROVED | `(builderBody leaf).RegsBelow 400` |
| `Proof.builderRun_full` | PROVED | `builderRun_spec`'s conclusions plus `Run.Safe W prog ⟨sF, ts⟩` and `∀ t ∈ ts, ∀ e, t.write? = some e → s.extent ≤ e.1`, under the same premises, a defined flow of the source, `size + 1 < 2 ^ W` and `s.Fits W` |
| `Proof.run_last_write` | PROVED | `(run p f s).final.memory a = some v → s.memory a = none → ∃ k t, transitions[k]? = some t ∧ t.write? = some (a, v) ∧ ∀ k' t', k < k' → transitions[k']? = some t' → ∀ e, t'.write? = some e → e.1 ≠ a` |
| `Proof.comparisonRunFacts` | PROVED | `∀ xs : List Int, BuilderRunFacts builderProgram (comparisonInputState xs) xs` (20 fields, DD-20260913-PRE1-018) |
| `Proof.wordRunFacts` | PROVED | `∀ xs : List Int, InputFits (wordWidth xs.length) xs → BuilderRunFacts builderProgramWord (wordInputState (wordWidth xs.length) xs) xs` |
| `Proof.builderProgram_headerUse`, `Proof.builderProgramWord_headerUse` | PROVED | `HeaderUse builderProgram`; `HeaderUse builderProgramWord` |
| `packedQueryOn_efficientBuild`, `packedQueryOn_efficientBuildWord` | PROVED | `∀ xs, PackedQueryOn (efficientBuild xs) xs`; under `InputFits`, `PackedQueryOn (efficientBuildWord (wordWidth n) xs) xs` (22 fields each) |
| `construction_complete_capacity`, `constructionCompleteRho_littleO` | PROVED | `((buildMemory xs).length + (queryProgramWords + programWords builderProgram + programWords builderProgramWord) + (queryScratchWords + 400)) * wordWidth n ≤ 2n + constructionCompleteRho n`; `LittleOLinear constructionCompleteRho` |
| `Conservative.queryProgram_fits32`, `Conservative.translated_run` | PROVED | `∀ i ∈ queryProgram, i.Fits 32`; `∀ memory fuel s, (run translatedQueryProgram fuel (state memory s)).final = state memory (PackedWordRAM.run memory queryProgram fuel s).final ∧ steps agree` |
| `constructionAndQueryCapstone_holds` | PROVED | `ConstructionAndQueryCapstone`; axioms `[propext, Classical.choice, Quot.sound]` |

## S8.2 Limits and residuals

- The query join is ruling Q3 (a)-(c); no offset-relocated in-place query
  execution is claimed.
- Literals are crude (`C = D = 1000000000`, `Cw = Dw = 3200000`, 400
  registers); no tightness or optimality.
- The workspace bound covers the temporary region below the output base,
  including the pad block's probe cell; the output itself is counted
  separately, and every prefix extent is bounded by their sum.
- Not yet done: replay cases on the capstone consumer, `Cw`/`Dw` numeral cases,
  C3 foundation cases, validator executable, lakefile stanza, gate reach
  check, full replays on the final tree, family and digestion entries, final
  checks.

# PRE-1 stage S7 records report (replays, scans, gate deadline)

| Item | Value |
| --- | --- |
| Parent | `48702c20a5708b6ea1efcd05a51faa0790a15ac1` (S7 completion) |
| Commit | the records commit on top of `48702c2`; its SHA is reported in the task response |
| Changed paths | `scripts/preprocessing_builder_gate.ps1` (default deadline 3600 s, note), WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-021), BUILDER_STAGE_LOG.md (C7-11..C7-15), ACCEPTANCE_MATRIX.md (two rows), REPORT.md |

## S7R.1 Results on `48702c2`

| Check | Outcome |
| --- | --- |
| Full builder replay (mutex) | PASS, executed 34 = registry 34, 355 stages, 51 self-tests, all restorations EXACT, 1535.87 s |
| Contract replay (mutex) | PASS, executed 18 = registry 18, 198 stages, 28 self-tests, frozen registry hash unchanged, 263.2 s |
| `claim_drift_scan.ps1 -Strict` | exit 0, 1603 hits, 0 strict failures |
| `claim_drift_scan.ps1 -SelfTest` | exit 1: `exclusion removed nothing (11 hits with records, 1603 without)` |

## S7R.2 Claim-scan self-test finding (coordinator item)

The self-test reads the hit count from the first output line containing
`scan complete (N hits` anywhere. With `-IncludeProcessRecords`, one emitted
review hit quotes line 911 of
`docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md` (copied
unchanged at Stage 0 as required), and that line contains
a scanner summary of 11 hits and 0 strict failures. The actual records
run ends with a summary of 2047 hits (rest elided). A temporary copy of the scanner
with the parser anchored at `^CLAIM-DRIFT: scan complete` passes its self-test
(`exclusion removed 444 hits (2047 -> 1603)`); the copy was deleted. The scanner
is outside this lane's write scope and the report copy must stay unchanged, so
the fix is left to the coordinator.

# PRE-1 stage S7 completion report (program constants, exactness, V3 pins and cases)

| Item | Value |
| --- | --- |
| Parent | `dc00e4399de803537d995a7f65f2688e62b0c3f0` (leaf restructure records) |
| Commit | the constants commit on top of `dc00e43`; its SHA is reported in the task response |
| Changed paths | `RMQ/Core/WordRAM/Construction/Builder/Program.lean`; new `Proof/Constants.lean`, `Proof/Exact.lean`; `scripts/preprocessing_builder_firewall.ps1` (table entry), `builder_manifest.json` (re-hash); `scripts/preprocessing_builder_check.lean` (V3 section, imports appended to line 3); `scripts/preprocessing_stage_check.lean` (S7 completion section, `stageGuard36`, hidden `PackedWordRAM` names); `scripts/preprocessing_builder_replay.ps1`, `builder_cases.json` (34 cases); DESIGN_DECISIONS.md (DD-20260913-PRE1-017); WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-020); BUILDER_REPLAY_DESIGN.md; BUILDER_STAGE_LOG.md (C7-1..C7-10); ACCEPTANCE_MATRIX.md (S7 completion appendix); REPORT.md |
| Commands | BUILDER_STAGE_LOG.md section "Stage S7 completion" |

## S7C.1 Landed declarations (checked types)

| Declaration | Status | Checked statement |
| --- | --- | --- |
| `builderBody`, `builderSource`, `builderProgram`, `builderProgramWord`, `builderBudget`, `efficientBuild`, `efficientBuildWord` | DEFINED in `Builder/Program.lean` | V3-3 shapes (pinned by `rfl` in the builder consumer); `builderBudget n = 1000000000 + 1000000000 * n`; both extraction bodies exactly as in V3-6 |
| `Proof.builderBudget_eq_mul_add` | PROVED (`omega`) | `∀ n, builderBudget n = 1000000000 * n + 1000000000` |
| `Proof.builder_leaf_difference` | PROVED (traversal lemma, then `rfl`) | the V3-4 statement with `P = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433]` and the key/word leaf instructions at `P` |
| `Proof.filter_range_ne_eq_diffPositions` | PROVED | `∀ {α} [DecidableEq α] (L1 L2 : List α), L1.length = L2.length → (List.range L1.length).filter (fun i => decide (L1[i]? ≠ L2[i]?)) = diffPositionsFrom L1 L2 0` |
| `Proof.builderProgram_contract`, `Proof.builderProgramWord_contract` | PROVED | `ProgramContract builderProgram (fun _ => builderProgram) 2107 8079`; `ProgramContract builderProgramWord (fun _ => builderProgramWord) 2107 8089` |
| `Proof.bankcap_wordWidth`, `Proof.cap_wordWidth` | PROVED | `∀ n, 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ wordWidth n`; `∀ n, n + 1 + 64 * (400000 * (n + 1)) < 2 ^ wordWidth n` |
| `Proof.builderSource_spec`, `Proof.builderRun_spec` | PROVED | for `W ≥ 32`, a `KeySpec` leaf, a running state with all registers zero, `xs.length` in cell 0 and the two capacity premises: the source (and the compiled program with `halt 3`) reach a halted state with `outBase` in register 3, `extent = outBase + (buildMemory xs).length`, the cells from `outBase` equal to `buildMemory xs`, memory below the initial extent and the keys unchanged, within `4 + (25W + 40 + 39(5W + 20)) + 2100 * (400000 * (n + 1))` transitions |
| `Proof.budget_ge` | PROVED | `∀ n, 4 + (25 * wordWidth n + 40 + 39 * (5 * wordWidth n + 20)) + 2100 * (400000 * (n + 1)) ≤ builderBudget n` |
| `Proof.efficientBuild_eq_buildMemory` | PROVED | `∀ xs : List Int, efficientBuild xs = buildMemory xs` |
| `Proof.efficientBuildWord_eq_buildMemory` | PROVED | `∀ xs : List Int, InputFits (wordWidth xs.length) xs → efficientBuildWord (wordWidth xs.length) xs = buildMemory xs` |

Axioms: the two equality theorems and `builder_leaf_difference` depend on
`[propext, Classical.choice, Quot.sound]`; every inventory printed by both
consumers is within that set (C7-3, C7-5).

## S7C.2 Consumers and cases

- Builder consumer: V3-1 `run_cmd`, V3-2 `@` lines 370-371, V3-3 `rfl`
  shapes, V3-4 and V3-5 at literal numerals, the fuel body pin at line 410 and
  both V3-6 body pins; `PRE1-BUILDER-TYPED-CONSUMERS PASS` in 3.04 s (C7-4). It
  imports `Proof.Constants`, not the proof tower (DD-20260913-PRE1-017).
- Stage consumer: the fuel lemma at full type and every `Proof/Exact.lean`
  theorem; the production constants on the array-backed interpreter
  (`stageGuard36`); `PRE1-STAGE-TYPED-CONSUMERS PASS` in 177.96 s (C7-5).
- Registry: 34 cases. Focused B18 PASS with exact restoration (C7-9). The B16
  mutant was rejected at exactly consumer line 370 with a clean restoration
  compile, but that run failed the replay's repository-state check because
  documentation was edited during the case (C7-10, recorded deviation); B17
  has not run yet.
- Not run in this commit: the full builder replay (34 cases), the contract
  replay, `claim_drift_scan.ps1 -Strict` and `-SelfTest`, a measured builder
  gate run on 34 cases.

# PRE-1 R-S7-7 leaf restructure report

| Item | Value |
| --- | --- |
| Parent | `48e590c` (rulings records) |
| Commit | the leaf restructure commit on top of `48e590c`; its SHA is reported in the task response |
| Changed paths | `RMQ/Core/WordRAM/Construction/Proof/Leaf.lean` (imports `Builder.Cartesian`; `keyLeaf_spec`, `wordLeaf_spec` removed), `Proof/BPEmit.lean` (`cartesianBP_key`, `cartesianBP_word` removed), new `Proof/Leaves.lean`, `scripts/preprocessing_stage_check.lean` (imports `Proof.Leaves`), DESIGN_DECISIONS.md (DD-20260913-PRE1-016), BUILDER_STAGE_LOG.md (rows L-1..L-6), REPORT.md |
| Commands | BUILDER_STAGE_LOG.md section "R-S7-7 leaf restructure" |

Signature inventory of every moved declaration (namespace
`RMQ.SuccinctFinal.PackedConstruction.Proof`; the stage consumer restates each
at full type):

| Declaration | Before | After | Type (unchanged) | Axioms (unchanged) |
| --- | --- | --- | --- | --- |
| `keyLeaf_spec` | `Proof/Leaf.lean` | `Proof/Leaves.lean` | `∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int), KeySpec W xs (OracleInput xs) keyLeaf` | propext, Quot.sound |
| `wordLeaf_spec` | `Proof/Leaf.lean` | `Proof/Leaves.lean` | `∀ {W : Nat}, 32 ≤ W → ∀ (xs : List Int), KeySpec W xs (WordInput W xs) wordLeaf` | propext, Classical.choice, Quot.sound |
| `cartesianBP_key` | `Proof/BPEmit.lean` | `Proof/Leaves.lean` | the Cartesian BP theorem at `keyLeaf` (full type in `spec_cartesianBP_key`) | propext, Classical.choice, Quot.sound |
| `cartesianBP_word` | `Proof/BPEmit.lean` | `Proof/Leaves.lean` | the Cartesian BP theorem at `wordLeaf` (full type in `spec_cartesianBP_word`) | propext, Classical.choice, Quot.sound |

- The full-name `#check @` and `#print axioms` inventories before (parent
  build) and after (rebuilt tower) are identical up to line terminators
  (L-1, L-4); the four declarations report module
  `RMQ.Core.WordRAM.Construction.Proof.Leaves`, and the text of each is
  unchanged (L-5).
- The firewall table, `builder_manifest.json` and both registries name no
  proof module, so they are unchanged; the builder firewall passes (L-6).
- Deviation: scratch S8 draft checks overlapped the mutex-held tower build for
  about seven minutes (BUILDER_STAGE_LOG.md, note after L-6).
- Not run in this commit: full builder and contract replays (they follow the
  constants commit), `claim_drift_scan.ps1 -Strict` and `-SelfTest`.

# PRE-1 rulings R-S7-5..R-S7-9 records report (amendment V3-6a, stage-consumer marker, gate note)

| Item | Value |
| --- | --- |
| Parent | `5dff46edf0d4d7a01a775afeddb8a3259249e9d4` (S7 checkpoint) |
| Commit | the records commit on top of `5dff46e`; its SHA is reported in the task response |
| Ruling | `PRE1_S7_V36_RULING.md`, 4,240 bytes, SHA-256 B355736C0B77E805148E0169390AF20E2B12A7EDB47E797B5CA106D2648800A0 |
| Changed paths | CONTRACT.md (amendment note V3-6a under the V3-6 fuel sentence), AMENDMENTS.md (version 3 amendment entry), `scripts/preprocessing_stage_check.lean` (gated verdict marker), `scripts/preprocessing_builder_gate.ps1` (deadline note), DESIGN_DECISIONS.md (DD-20260913-PRE1-015), WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-018), BUILDER_STAGE_LOG.md (rows R7-1..R7-6), REPORT.md |

- Amendment V3-6a: `builderBudget n = D + C * n` with decimal numerals; every
  other V3-6 requirement stands; `builderBudget_eq_mul_add` is to be proved
  propositionally and restated in the stage consumer when the constants land.
- Stage consumer: the marker is printed only when all 291 declarations
  elaborate without `sorry` and all 35 fixture checks hold; both negative
  controls (a false fixture, a `sorry` restatement) suppress it and exit 1
  (R7-3, R7-4).
- V3-4 route (R-S7-6): `filter_range_ne_eq_diffPositions` turns the V3-4
  filter into one simultaneous traversal checked by `rfl`; on the draft
  constants `builder_leaf_difference` elaborates at its V3-4 type with standard
  axioms (R7-5). It lands with the constants.
- Builder gate: deadline unchanged at 1800 s, 2.79 x the projected 15-case run;
  a measured 15-case run is still due.
- Not run: full builder and contract replays, the leaf restructure and tower
  rebuild (mutex held by the OPT-1 gate), `claim_drift_scan.ps1 -Strict` and
  `-SelfTest`.

# PRE-1 stage S7 checkpoint report (arrays, metadata, dense words, tail stage; V3-6 obstruction)

| Item | Value |
| --- | --- |
| Parent | `46af19c76153822bc9cc32ea4490785ea4b6df81` (C3 record) |
| Commit | the S7 checkpoint commit on top of `46af19c`; its SHA is reported in the task response |
| Changed paths | new `RMQ/Core/WordRAM/Construction/Spec/Metadata.lean`, `Builder/Output.lean`, `Proof/MetaBounds.lean`, `Proof/MetaSteps.lean`, `Proof/MetaChain.lean`, `Proof/Output.lean`, `Proof/Tail.lean`; changed `Proof/Buffer.lean` (`bufferStage_kept`, `bufferStage_spec` derived, type unchanged), `scripts/preprocessing_builder_firewall.ps1` and `builder_manifest.json` (Output registered, 17 modules), `scripts/preprocessing_stage_check.lean` (S7 section), DESIGN_DECISIONS.md (DD-20260913-PRE1-014), WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-017), BUILDER_STAGE_LOG.md, ACCEPTANCE_MATRIX.md, BUILDER_PLAN.md (append-only notes), REPORT.md |
| Commands | BUILDER_STAGE_LOG.md section "Stage S7 checkpoint", rows S7-1..S7-21 |

## S7.1 Landed lemmas (checked types abbreviated; the stage consumer restates each at full type)

| Declaration | Status | Checked statement |
| --- | --- | --- |
| `Spec.metaWords_eq` | PROVED | `metaWords n lc c = metadataOf n lc (c * GenericSelect.localStride (2 * n))` for all `n lc c` |
| `Spec.pay_eq`, `Spec.cellCount_eq` | PROVED | `packedReviewerPayloadLength n lc (c * localStride (2n)) = mv_pay n lc c`; `packedReviewerCellCount … = mv_oldCount n lc c` |
| `Proof.metaVal_le` | PROVED | `∀ n lc c, mv_pay n lc c + 2 ≤ 400000 * (n + 1) → ∀ i < 108, metaVal n lc c i ≤ 3 * (400000 * (n + 1))` |
| `Proof.metaStep0` … `metaStep107`, `metaStep_all` | PROVED | each step stores `metaVal n lc c i` into register `229 + i` in `≤ 6` safe transitions, writing no other register, under `32 ≤ W`, `32 * (400000 * (n + 1)) < 2 ^ W` and the payload premise |
| `Proof.metaChain_spec` | PROVED | the first `k ≤ 108` steps establish `MetaUpTo n lc c k`, keep `MetaBase`, cost `≤ 6k` |
| `Proof.SafeEval.regs_fit` | PROVED | a safe evaluation from a state with all registers below `2 ^ W` ends in one |
| `Proof.metaEmit_spec` | PROVED | `metaEmitBlock` appends exactly `metaWords n lc c` in 348 transitions and sets register 3 to the old extent |
| `Proof.repack_spec` | PROVED | for `N` words of `W0 ≤ W` 0/1 cells at `buf`, `repackBlock` appends `hornerWords g W0 N` in `≤ N * (7 * W0 + 12) + 3` transitions |
| `Proof.outputWords_eq_buildMemory` | PROVED | `metaWords n (longCount (shape xs)) c ++ hornerWords (densePad cells) (wordWidth n) (mv_dcount …) = buildMemory xs` with `n = xs.length`, `c` the sparse-exception rank |
| `Proof.outputStage_spec` | PROVED | bank, words and dense words from the buffer: extent grows by exactly those words, register 3 holds `outBase`, cost `≤ 1000 + N * (7W + 12)` |
| `Proof.arraysBlock_spec` | PROVED | the twelve array bases in layout order, abstract counts, cost `≤ 5 * size + 2` |
| `Proof.bufferStage_kept` | PROVED | `bufferStage_spec` with frame `BufferKept` (registers 0-3, 9, 29-99, the array bases and `≥ 229` unchanged) |
| `Proof.tailStage_spec` | PROVED | arrays, buffer phase and output from the geometry bank: `extent = outBase + (buildMemory xs).length`, cells from `outBase` are `buildMemory xs`, `extent₀ ≤ outBase ≤ extent₀ + 8 * (400000 * (n + 1))`, memory below `extent₀` unchanged, cost `≤ 2100 * (400000 * (n + 1))`, under `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, `extent₀ + 64 * (400000 * (n + 1)) < 2 ^ W`, `wordWidth n ≤ W` |

All `#print axioms` inventories of the new declarations are within
{propext, Classical.choice, Quot.sound} (S7-19).

## S7.2 Drafted, not landed (scratch, pending the V3-6 ruling)

`builderBody`, `builderSource`, both program constants, `builderBudget`, both
extraction bodies exactly as V3-6; `header_spec`; `builderSource_spec` (the
whole source from the initial state); `builderRun_spec` (`RunsTo` to a halted
state with the output); `fringeOverhead_ge_two`, `two_n_four_lt_cellPow`,
`bankcap_wordWidth : 2 ^ 32 * (2n + 4) ^ 8 < 2 ^ wordWidth n` and
`cap_wordWidth : n + 1 + 64 * (400000 * (n + 1)) < 2 ^ wordWidth n` for every
`n` (R-S7-4, no size premise); size pins `(builderSource keyLeaf).size = 2106`
and the same for `wordLeaf` by `rfl`; `efficientBuild_eq_buildMemory` and
`efficientBuildWord_eq_buildMemory` at the V3-6 statements. With
`builderBudget n = 1000000000 + 1000000000 * n` all of these elaborate and both
exactness theorems depend on `[propext, Classical.choice, Quot.sound]` (S7-16).

## S7.3 Obstruction requiring a coordinator ruling: CONTRACT.md V3-6 fuel body

- Statement in force: V3-6 fixes `builderBudget n = C * n + D` with decimal
  numerals, the extraction bodies matching on
  `(run builderProgram (builderBudget xs.length) (comparisonInputState xs)).final.status`,
  and consumer pins of both bodies by `rfl` at every `xs`.
- Finding: in Lean 4.22.0 the kernel, when it checks any definitional
  unfolding of such a body (the `rfl` pin, `unfold`/`delta` of the definition,
  or its generated equation lemma), reduces the match discriminant, and
  reducing the fuel `C * xs.length + D` peels the literal `D` one successor at a
  time. It stops with `(kernel) deep recursion detected` for `D = 100000` on a
  one-instruction program and for `D = 1000000000` on the builder template; it
  passes for `D ∈ {1000, 10000}` and for variable fuel (S7-14, S7-15).
- Why no admissible `D` avoids it: the proven work bound at `n = 0` is
  `4 + 25 * W + 40 + 39 * (5 * W + 20) + 2100 * 400000` with `W = wordWidth 0 = 112`,
  about `8.4 * 10^8`, so `builderBudget 0 = D` must be at least that. The
  executed harness takes 3553 transitions at `n = 0` and 7223 at `n = 1`
  (S7-21), but no stage cost theorem is tight enough to prove a `D` near
  that, and tightening every stage's constant term is not in scope.
- Evidence that the same function in the other order works: with
  `builderBudget n = D + C * n` (`C = D = 1000000000`) the V3-6-shaped `rfl`
  pins, the equation lemma, `delta` and both exactness theorems check
  (S7-15, S7-16).
- Requested ruling (one of): (a) amend V3-6 to `builderBudget n = D + C * n`
  with decimal numerals `D`, `C`, keeping every other V3-6 requirement,
  including the `rfl` pins; (b) another fuel body the coordinator prefers,
  which I will test against the same kernel checks before landing.

## S7.4 Other findings and limits

- V3-4/V3-5 feasibility on the draft constants: `builderProgram.length = 2107`
  and `programWords` (8079 key, 8089 word) check by `rfl`; the leaf positions
  are `P = [411, 412, 413, 414, 415, 429, 430, 431, 432, 433]` and the leaf
  contents at `P` check by `rfl`; the V3-4 filter statement itself did not
  check by `decide` (heartbeats) or `decide +kernel` (over 280 s): indexing is
  quadratic. Planned: a general lemma turning the filter into one simultaneous
  traversal of both lists, then `rfl` on that traversal.
- Leaf restructure (planned, needs the mutex): `Proof/Leaf.lean` imports
  `Builder/Program.lean`, so landing the constants would rebuild the whole
  proof tower and every V3-7 mutation of `Builder/Program.lean` would rebuild
  it in the replay producer stage. The plan moves `keyLeaf_spec`,
  `wordLeaf_spec`, `cartesianBP_key` and `cartesianBP_word` into a new module
  after the tower; that rebuild exceeds five minutes.
- Process deviation: scratch command S7-6 ran 623 s without
  `Global\RMQHeavyVerification` while another gate held it; it was stopped
  without a result. Later scratch runs were bounded by `timeout ≤ 295`.
- Not run on this commit: full builder replay (15 cases), full contract replay
  (18 cases), `claim_drift_scan.ps1 -Strict` and `-SelfTest`, the aggregate
  gate. The stage consumer marker is still unconditional. The builder gate's
  deadline note still cites the 13-case measurement.
- Checks run: `git diff --check`, `scripts/design_decision_check.ps1 -Strict`
  against `c1c970b8bfbae03163633365e512d487ae1c98f2` and per commit against
  `46af19c`, the builder firewall (17 modules), the stage consumer
  (1786 inventories) and the trust scans (S7-18..S7-20).

# PRE-1 condition C3 report (manifest re-hash mechanism, nested guard deadline, verdict-gated markers)

| Item | Value |
| --- | --- |
| Parent | `6df96d6033ad2a7bbb868f5d89814fb3c2ebdcc0` (C2) |
| Commit | the C3 commit on top of `6df96d6`; its SHA is reported in the task response |
| Changed paths | `scripts/preprocessing_builder_replay.ps1` (optional `manifest: rehash` field, validation, three registry self-tests, re-hash and restoration in `Invoke-Case`, IDs, registry pin `e9e4445629ef93db4ed8bbc115f7f42008037032723dc02a0560a3b991cff208`), `docs/internal/extensions/pre1/builder_cases.json` (B15), `scripts/preprocessing_builder_firewall.ps1` (`-ContractGuardDeadlineSeconds`, owned bounded child), `scripts/preprocessing_builder_check.lean` and `scripts/preprocessing_contract_check.lean` (verdict-gated markers), BUILDER_REPLAY_DESIGN.md, BUILDER_STAGE_LOG.md, ACCEPTANCE_MATRIX.md, REPORT.md, WORKFLOW_DESIGN_DECISIONS.md (WDD-20260913-PRE1-015); no Lean module under `RMQ/` changed |
| Commands | BUILDER_STAGE_LOG.md section "Condition C3 before S7", rows C3-1..C3-9 |

## C3.1 Outcome

- Re-hash mechanism: B15 (`runArray_abstract` without its final-state
  conjunct) passes the firewall with exactly one manifest digest replaced,
  builds, and fails the consumer with failing line set exactly {335}; source
  and manifest bytes are restored and the restored stages pass (C3-6).
- P3-7: a 1 s guard deadline yields `contract guard inconclusive: timeout=True`;
  the default passes on pwsh 7 and Windows PowerShell 5.1; B03's pinned message
  is unchanged (C3-4, C3-7).
- P3-1: rejected cases B13, B15 and C01 print no marker and keep their exact
  failing line sets; accept controls B12 and C14 print it (C3-6..C3-8). The
  gating check is name-based (`collectAxioms` of `consumerWitness`), because
  the command-state message log does not accumulate (C3-1) and a sorry-dependent
  `#eval` term would add an error line.

## C3.2 Limits

- Not yet run on this commit: the full 15-case builder replay and the full
  18-case contract replay (each longer than five minutes; the mutex was held by
  another process, C3-9). Focused runs cover B03, B12, B13, B15, C01 and C14.
- Still due under C3: V3-7 case (i) (needs the S7 constants) and the
  consumer-reaching cases for the other foundation declarations before the S8
  candidate is frozen.
- The stage consumer still prints its marker unconditionally; its exit code is
  the verdict.
- The builder gate's deadline note still cites the 13-case measurement.
- Checks: `git diff --check`, the strict design check against `c1c970b` and
  the builder firewall pass on the C3 commit; its per-commit design check
  FAILS (the two consumer Lean files are code and the commit had no
  DESIGN_DECISIONS.md entry; row C3-10). The follow-up commit adds
  DD-20260913-PRE1-013 and WDD-20260913-PRE1-016 without rewriting the C3
  commit. The claim-drift strict scan is scheduled before the final candidate.

# PRE-1 condition C2 report (consumer-reaching `headerFirst` case)

| Item | Value |
| --- | --- |
| Parent | `5af951da24381c45bda585b04ea9b4b43695ba9f` (S6) |
| Commit | the C2 commit on top of `5af951d`; its SHA is reported in the task response |
| Changed paths | `docs/internal/extensions/pre1/builder_cases.json` (B14 appended), `scripts/preprocessing_builder_replay.ps1` (`ExpectedIds`, registry pin `ac8d76e70f636445ec9f431379c42150545fa5cdc35fa513369392065a382182`), `docs/internal/extensions/pre1/BUILDER_REPLAY_DESIGN.md` (B14 row), BUILDER_STAGE_LOG.md, ACCEPTANCE_MATRIX.md, REPORT.md, `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (WDD-20260913-PRE1-014); no Lean source changed |
| Case | `B14_HEADERFIRST_CONSUMER`: `headerFirst : True`, run-level fields without defaults, constructor supplying them from `hhead`; expected reject at consumer, surface `preprocessing_builder_check.lean:20:` |
| Commands | BUILDER_STAGE_LOG.md section "Condition C2", rows C2-1..C2-5 |

## C2.1 Outcome

- Focused replay (C2-3): firewall 0, producer 0, consumer 1 with failing line
  set exactly {20} (`preprocessing_builder_check.lean:20:55: error: type mismatch`),
  byte-identical restoration and passing restored stages. This reproduces the
  outcome of the audit's probe P-7.
- Registry self-tests (pwsh 7 and Windows PowerShell 5.1), the selector probe
  and the nine selector boundary fixtures pass with 14 registered cases.

## C2.2 Limits

- The registered mutation bytes differ from the audit probe's (P-7 SHA-256
  `e6f2af3e...ad84` over a CRLF copy whose exact `after` text the report does
  not give); the registered text follows the shape the audit specifies.
- No full 14-case replay has run on this commit; the full replay is scheduled
  with C3 under `Global\RMQHeavyVerification` (it exceeds five minutes). The
  builder gate's deadline note still cites the 13-case measurement.
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check (outcomes in the task response). The
  claim-drift strict scan is scheduled before the final candidate.

# PRE-1 S6 report (microtables, header patch, paddings, bit buffer)

| Item | Value |
| --- | --- |
| Parent | `e3e71dea6b5e99768938963d30a9dd31a3e85d84` (S5) |
| Commit | the S6 commit on top of `e3e71de`; its SHA is reported in the task response |
| Builder program text (inside the firewall) | new `Builder/Micro.lean` (registers 200-217; `fringeDecodeActs`, `fringeStepBlock`, `fringeEntryBlock`, `selectDecodeActs`, `selectStepBlock`, `selectEntryBlock`, `microtablesBlock`) and new `Builder/Finish.lean` (registers 220-228; `headerReserveBlock`, `headerPatchStepBlock`, `headerPatchBlock`, `zerosBlock`, `padBlock`, `bufferBlock`); registered in the firewall table (Micro imports `Builder.Access`; Finish imports `Builder.Micro` and `Builder.Cartesian`) and hashed in the manifest (16 modules) |
| Specification (outside) | `Spec/Micro.lean` |
| Proofs (outside) | `Proof/Micro.lean`, `Proof/Finish.lean`, `Proof/Buffer.lean` |
| Consumer | `scripts/preprocessing_stage_check.lean`: 1202 axiom inventories (1124 with axioms, 78 without), union {propext, Classical.choice, Quot.sound}; 13 source pins; 5 predicate pins; 33 full-type restatements; 25 `#guard` fixtures on the compiled source (microtables at 5 sizes, the whole buffer for 20 inputs) |
| Decisions | DD-20260913-PRE1-012, WDD-20260913-PRE1-013 |
| Commands | BUILDER_STAGE_LOG.md section "S6 microtables, header patch, paddings, buffer theorem", rows S6-1..S6-21 |

## S6.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `selectPos_step`, `selectPos_final`, `fringeBest_step`, `excessOffset_succ` | PROVED | the branch-free select update keeps `if k < rankPrefix false (bpFringeChunkPattern c v) t then bpChunkSelectPos c false v k else c`, which is `bpChunkSelectPos c false v k` at `t = c`; the keep-left fringe update keeps `bpFringeScanArgMin f a (min t b - a)` and its value; the offset excess moves by `2 * bit - 1` without underflow (`spec_selectPos_step`, `spec_selectPos_final`, `spec_fringeBest_step`, `spec_excessOffset_succ`) |
| `selectTable_spec` | PROVED | from `regs 64 = c`, `regs 67 = bpChunkSelectRowCount c`, `regs 68 = bpChunkSelectEntryWidth c`, `rows + c + 1 < 2 ^ W` and `s.extent + rows * width < 2 ^ W`: `emitTable 67 68 selectEntryBlock` appends `(tableBits (bpChunkSelectEntries c false) (bpChunkSelectEntryWidth c)).map bitToNat`, cost `≤ rows * (14c + 9 + 7 width + 7) + 3`, registers outside 200-219 and 10-16 unchanged (`spec_selectTable_spec`). This is the plan's `selectChunk_spec` |
| `fringeTable_spec` | PROVED | from `regs 64 = c`, `regs 65 = bpFringeChunkRowCount c`, `regs 66 = bpFringeChunkEntryWidth c`, `rows + 16 * (c + 1) ^ 3 < 2 ^ W` and `s.extent + rows * width < 2 ^ W`: appends `(tableBits (bpFringeChunkEntries c) (bpFringeChunkEntryWidth c)).map bitToNat`, cost `≤ rows * (25c + 42 + 7 width + 7) + 3` (`spec_fringeTable_spec`). This is the plan's `fringe_spec` |
| `microtables_spec` | PROVED | both tables in payload order from one state, frame outside 200-219 and 10-16 (`spec_microtables_spec`) |
| `headerReserve_spec` | PROVED | from `regs 75 = oldW ≥ 1` and `s.extent + oldW + 1 < 2 ^ W`: appends `oldW` zero cells, `regs 220 = s.extent`, `regs 119 = s.extent + oldW`, cost `≤ 5 oldW + 2`, registers outside {10, 12, 119, 220, 226} unchanged (`spec_headerReserve_spec`) |
| `headerPatch_spec` | PROVED | from `regs 220 = buf`, `regs 75 = oldW`, `regs 177 = lc < 2 ^ W` and `buf + oldW ≤ extent < 2 ^ W`: memory at `a` becomes `some (lc / 2 ^ (a - buf) % 2)` for `buf ≤ a < buf + oldW` and is unchanged elsewhere, extent unchanged, cost `≤ 8 oldW + 4` (`spec_headerPatch_spec`). With `headerReserve_spec`, the plan's `header_spec` |
| `pad_spec` | PROVED | from `regs 220 = buf`, `extent = buf + L`, `regs 75 = oldW ≥ 1`, `regs 76 = W' ≥ 1`, `oldW ≤ L` and `buf + L + oldW + W' + 2 < 2 ^ W`, with `D = denseBitsOf oldW W' L = (((L - 1) / oldW + 1) * oldW + W' - 1) / W' * W'`: `L ≤ D ≤ L + oldW + W'` and the block appends `D - L - [L < D] + 1` zero cells, cost `≤ 5 (D - L) + 18` (`spec_pad_spec`, `spec_denseBitsOf_def`). This is the plan's `padding_spec` (both layers at once) |
| `bufferCells_getD`, `bufferCells_length` | PROVED | cell `i` of `(densePad (wordWidth n) (packedReviewerPaddedBits shape)).map bitToNat` is `longCount shape / 2 ^ i % 2` for `i < oldW` and `((packedReviewerPayloadBits shape).map bitToNat).getD (i - oldW) 0` otherwise; the length is `denseBitsOf oldW (wordWidth n) (oldW + packedReviewerPayloadLength n lc sc)` (`spec_bufferCells_getD`, `spec_bufferCells_length`) |
| `bufferStage_spec` | PROVED | for every `W ≥ 32`, `xs`, `Inp` with `InpBelow Inp s.extent`, leaf with `KeySpec W xs Inp leaf`, and running `s` with `Inp s`, `regs 0 = 0`, `GeoBase n s.regs ∧ GeoUpTo n 39 s.regs` (`n = xs.length`), `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, access bases in 159-164 ordered `P0 + n + 1 ≤ R0`, `R0 + 2n / ws + 1 ≤ L0`, `L0 + sup ≤ C0`, `C0 + sup + 1 ≤ F0`, `F0 + loc ≤ G0`, `G0 + loc + 1 ≤ s.extent`, interior bases in 115-118, 135, 136 ordered `A0 + bc + 1 ≤ A1`, `A1 + bc ≤ A2`, `A2 + bc ≤ A3`, `A3 + bc ≤ Bm`, `Bm + LC * bc ≤ Gb`, `Gb + GLC * mc ≤ s.extent`, and `s.extent + 32 * (400000 * (n + 1)) < 2 ^ W`: `∃ s' k, SafeEval W (stackArraysBlock; stackPassBlock leaf; bufferBlock) s s' k ∧ k ≤ 2000 * (400000 * (n + 1)) ∧ s'.status = .running ∧ s'.regs 220 = base ∧ ArrayAt s' base T.length (T.getD · 0) ∧ s'.extent ≤ base + T.length + 1 ∧` memory below `s.extent` outside both layouts unchanged `∧ s'.regs 177 = longCount (shape xs) ∧ s'.regs 178 = rankPrefix true (sparseExceptionFlagBits bpCode false) loc ∧` registers outside 4-28 and 100-228 unchanged `∧ s'.keys = s.keys`, where `base = s.extent + 3 * (n + 1)` and `T = (densePad (wordWidth n) (packedReviewerPaddedBits (shape xs))).map bitToNat` (`spec_bufferStage_spec`). This is the plan's `bufferStage_spec` (cells conjunct) and `buffer_cost` (cost conjunct); the plan's `outBase - bufBase = denseCount * W` is replaced by `base + T.length ≤ extent ≤ base + T.length + 1` (S6.3) |

Reading: for every input and leaf, the charged stack pass followed by the
buffer phase, run safely at any width meeting the capacity premises, leaves at
the base in register 220 exactly the dense bit buffer of the reference (header
bits of the long count, payload, both zero paddings), in a literal linear
number of transitions, with at most one extra zero cell after it.

## S6.2 Evidence beyond elaboration

- Fixtures before the proofs: both microtables for `n ∈ {0, 1, 5, 127, 128,
  32767, 32768}` (`c = 1, 2, 3`; re-run S6-17); the whole buffer for eleven
  sizes and three literal inputs after the BP base fix (S6-5). The first
  buffer run (S6-4) exposed that `bufferBlock` did not set register 119.
- Long count 1 (`n = 13395`, S6-12): header cells, BP cells, trailing zeros,
  register 177 and the extent bound. The `L = D` edge (`n = 1116`, S6-14):
  checks pass and the extent is `D + 1`.
- Consumer `#guard` fixtures: microtables at 5 sizes, whole buffer for 20
  inputs (dense reference buffer and extent bound).
- Mutation S6-15 (header bit `x / 2` instead of `x % 2`, on a scratch copy)
  rejected; its unmutated control elaborated. S6-16 re-checked the S5
  mutation with names resolved: rejected, control elaborated.

## S6.3 Limits and deviations

- The plan's `outBase - bufBase = denseCount * W` is false for this program
  text: when the serialized length `L` equals `D` the probe cell stays after
  the buffer. Counterexample: `xs = (range 1116).map (fun i => (i * 37 + 11) % 13 - 6)`,
  long count 0, `L = D = 73920`, `extent - base = 73921` (S6-14); sixteen
  `(n, lc)` pairs with `n < 20000`, `lc ≤ 3`, `sc = 0` have `L = D` (S6-11).
  The theorem states exactness on the first `D` cells and the `+ 1` bound
  (DD-20260913-PRE1-012).
- `bufferStage_spec` fixes the layout: access and interior arrays below the
  stack arrays, then the buffer. S7 must reserve them in that order.
  `cartesianBP_spec` (S3) is not a segment of the final program; its component
  theorems are reused.
- The consumer buffer fixtures all have long count 0 and sparse count 0. The
  long-count and `L = D` runs need `--tstack` and stay scratch evidence; the
  full reference buffer at `n = 1116` did not finish in 285 s (S6-13). No
  executable input sets a sparse-exception flag (S5-18).
- The capacity premises are about the declared width; S8 discharges them at
  `wordWidth n`.
- Process: the untracked `Proof/Buffer.lean` carried two temporary `sorry`
  placeholders during one build (S6-7 run 1); they were replaced before the
  next build, no commit contains them, and the consumer's axiom union is
  standard. The S5-17 mutation file declared its block in a namespace its
  theorem did not open; S6-16 re-ran it soundly.
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is scheduled before the
  final candidate (documentation changes are under `docs/internal/**`).

# PRE-1 S5 report (access half)

| Item | Value |
| --- | --- |
| Parent | `4340632e623016921dbf1c66a3b6b10e6a088b4e` (S4 completion) |
| Commit | the S5 commit on top of `4340632`; its SHA is reported in the task response |
| Builder program text (inside the firewall) | new `Builder/Access.lean` (registers 159-189; `posActs`, `monusActs`, `posStepBlock`, `posPassBlock`, `longFlagBlock`, `longFlagsBlock`, `sparseFlagBlock`, `sparseFlagsBlock`, fourteen entry blocks, `longRelativeBodyBlock`, `sparseRelativeBodyBlock`, `accessHalfBlock`); registered in the firewall table (imports `Builder.Interior`) and hashed in the manifest (14 modules) |
| Specification (outside) | `Spec/Access.lean` |
| Proofs (outside) | `Proof/PosPass.lean`, `Proof/AccessFlags.lean`, `Proof/AccessEntries.lean`, `Proof/AccessRelative.lean`, `Proof/AccessTables.lean`, `Proof/AccessHalf.lean` |
| Consumer | `scripts/preprocessing_stage_check.lean`: 1032 axiom inventories (970 with axioms, 62 without), union {propext, Classical.choice, Quot.sound}; 26 source pins; 42 full-type restatements; 20 access-half `#guard` fixtures on the compiled source |
| Decisions | DD-20260913-PRE1-011, WDD-20260913-PRE1-012 |
| Commands | BUILDER_STAGE_LOG.md section "S5 access half", rows S5-1..S5-19 |

## S5.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `select_at_close`, `position_at_close` | PROVED | `b[p]? = some false → select false b (rankPrefix false b p) = some p`, hence `position b false (rankPrefix false b p) = p` (`spec_select_at_close`, `spec_position_at_close`) |
| `posPass_spec` | PROVED | from the BP cells at `B`, `P0 + n + 1 ≤ R0`, `R0 + 2n / ws + 1 ≤ B`, `B + 2n ≤ s.extent < 2 ^ W`: `posPassBlock` stores `position bpCode false k` at `P0 + k` for `k ≤ n` and `rankPrefix false bpCode (j * ws)` at `R0 + j` for `j ≤ 2n / ws`, memory outside `[P0, R0 + 2n / ws]` unchanged, cost `≤ (2n + 1) * 20 + 7` (`spec_posPass_spec`) |
| `longFlags_spec`, `sparseFlags_spec` | PROVED | from the positions: `flagNat (superIsLong bpCode false k)` at `L0 + k` (`k < sup`) with `rankPrefix true (longSuperFlagBits bpCode false) k` at `C0 + k` (`k ≤ sup`), and `flagNat (localIsSparseException bpCode false g)` at `F0 + g` (`g < loc`) with `rankPrefix true (sparseExceptionFlagBits bpCode false) g` at `G0 + g` (`g ≤ loc`); the final counts in registers 177 and 178; costs `≤ sup * 39 + 6` and `≤ loc * 64 + 6` (`spec_longFlags_spec`, `spec_sparseFlags_spec`) |
| entry lemmas | PROVED | each entry block leaves the reference entry in register 16 under `EntryOK`: rank samples, `superEntry` and `localEntry` fields (with the liveness zeros), flag-rank samples, zeros, raw flags, and `if base + o < end then position (base + o) - basePos else 0` (`spec_flagEntry_spec` .. `spec_localOffsetEntry_spec`, `spec_relOffsetEntry_spec`) |
| `relLoop_spec`, `longRelative_spec`, `sparseRelative_spec` | PROVED | the two relative loops append `(tableBits (longSuperRelativeEntries bpCode false) (longSuperRelativeWidth bpCode)).map bitToNat` and `(tableBits (sparseExceptionRelativeEntries bpCode false) (sparseExceptionRelativeWidth bpCode)).map bitToNat`, cost `≤ sup * 25 + 3 + 34 * bits` and `≤ loc * 29 + 3 + 34 * bits` (`spec_longRelative_spec`, `spec_sparseRelative_spec`) |
| `accessTable_generic` | PROVED | `emitTable count w entry` from an `AccessReady` state with `regs count = N`, `regs w = wv ≥ 1` and an entry computing `f slot` appends `(tableBits es wv).map bitToNat` for `(range N).map f = es`, keeping the access frame, cost `≤ (J + 14) * bits + 3` (`spec_accessTable_generic`) |
| `accessPasses_spec` | PROVED | from the bank, the bank capacity and the layout: the three passes reach an `AccessReady` state `t` with `t.extent = s.extent`, memory outside `[P0, G0 + loc]` unchanged, and the two counts (`spec_accessPasses_spec`) |
| `accessHalf_spec` | PROVED | from `GeoBase n s.regs ∧ GeoUpTo n 39 s.regs`, `2 ^ 32 * (2n + 4) ^ 8 < 2 ^ W`, the BP cells at `B`, `P0 + n + 1 ≤ R0`, `R0 + 2n / ws + 1 ≤ L0`, `L0 + sup ≤ C0`, `C0 + sup + 1 ≤ F0`, `F0 + loc ≤ G0`, `G0 + loc + 1 ≤ B`, `B + 2n ≤ s.extent` and `s.extent + 16 * (400000 * (n + 1)) < 2 ^ W`: `∃ t s' k, SafeEval W accessHalfBlock s s' k ∧ k ≤ 200 * (400000 * (n + 1)) ∧ s'.status = .running ∧ t.extent = s.extent ∧` memory of `t` outside `[P0, G0 + loc]` equal to `s` `∧ Emits t s' ((concreteBPNativeSuccinctRMQCanonicalReviewerLiveAccessPayload shape).map bitToNat) ∧ s'.regs 177 = rankPrefix true (longSuperFlagBits bpCode false) sup ∧ s'.regs 178 = rankPrefix true (sparseExceptionFlagBits bpCode false) loc ∧` frame `AccessHalfFrame` `∧ s'.keys = s.keys` (`spec_accessHalf_spec`). This is the plan's `accessSegment_eq` (Emits conjunct) and `access_cost` (cost conjunct) |
| `lc_eq_longCount`, `sc_eq_sparseCount` | PROVED | `rankPrefix true (longSuperFlagBits bpCode false) sup = longCount shape`; `rankPrefix true (sparseExceptionFlagBits bpCode false) loc * localStride (2n) = packedReviewerSparseCount shape` (`spec_lc_eq_longCount`, `spec_sc_eq_sparseCount`) |

Reading: for every shape, the charged access half, run safely at any width
meeting the two capacity premises, fills its six arrays in place from one scan
of the BP code and then appends exactly the live access payload of the
reference, in a literal linear number of transitions, leaving the two header
counts in registers.

## S5.2 Evidence beyond elaboration

- Fixtures before the proofs (row S5-2): all eighteen segments for 17 sizes and
  three literal inputs; crafted threshold inputs (row S5-4): first-super span
  exactly `superLongSpan` (long count 0) and one more (long count 1), checked
  on the BP cells and sources 11-14.
- Consumer `#guard` fixtures: 20 inputs against all eighteen segments.
- Mutation S5-17 (flag comparison reversed, on a scratch copy) rejected.

## S5.3 Limits and deviations

- No executable input sets a sparse-exception flag: the local stride is 1 for
  every `n < 2 ^ 96` (row S5-18), so the sparse flags, their rank tables and the
  sparse relative table are exercised executably only in their all-false form.
  The theorems are general.
- The long-super threshold inputs run about 75 s each with `--tstack` and stay
  scratch evidence (WDD-20260913-PRE1-012).
- The array order is assumed; S6 reserves the arrays and places the access
  segments after the BP code. `accessHalf_spec` carries the bank capacity
  premise in addition to the extent premise; both are discharged at
  `wordWidth n` in S8.
- `sc` is `localStride * regs 178`, formed in S7; the S5 theorem states the
  count over the full sparse flag vector, as the reference length lemma does.
- The sparse flag and its loop were developed in scratch copies with a
  temporary placeholder (row S5-8); no repository file contained one, and the
  consumer's axiom union is standard.
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is scheduled before the
  final candidate (documentation changes are under `docs/internal/**`).

# PRE-1 S4 completion report (sparse memos, sparse tables, close segment)

| Item | Value |
| --- | --- |
| Parent | `0192fdd8a05b1bb47c65e5027923e51b116e656b` (S4 checkpoint) |
| Commit | `4340632e623016921dbf1c66a3b6b10e6a088b4e` |
| Builder program text (inside the firewall) | `Builder/Interior.lean` (`betterActs`, `memoCellBlock`, `memoLevelsBlock`, `localMemoBlock`, `macroScanBlock`, `globalMemoBlock`, `localEntryBlock`, `globalEntryBlock`, `interiorCloseBlock`), `Builder/Registers.lean` (registers 135-158); manifest re-hashed, firewall table unchanged (13 modules) |
| Specification (outside) | `Spec/SparseMemo.lean` |
| Proofs (outside) | `Proof/SparseMemo.lean`, `Proof/SparseTables.lean`, `Proof/InteriorClose.lean` |
| Consumer | `scripts/preprocessing_stage_check.lean`: 790 axiom inventories (744 with axioms, 46 without), union {propext, Classical.choice, Quot.sound}; 24 close-segment `#guard` fixtures on the compiled source |
| Decisions | DD-20260913-PRE1-010, WDD-20260913-PRE1-011 |
| Commands | BUILDER_STAGE_LOG.md section "S4 completion", rows S4-16..S4-34 |

## S4F.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `argPos_excess_eq_min` | PROVED | `b * bs + bs ≤ 2n → bpExcessAt shape (bpBlockArgMinPrefixPos shape bs b) = bpBlockMinExcess shape bs b` (`spec_argPos_excess_eq_min`) |
| `better_eq_min` | PROVED | for covered `x`, `y`: `bpBetterArgMinBlock shape bs x y = if bpBlockMinExcess shape bs y < bpBlockMinExcess shape bs x then y else x` |
| `memoLevels_spec` | PROVED | generic doubling: from row 0 of a memo with `N`-cell rows at `Bm` and a value function `V` with `V (l + 1) i = bpBetterArgMinBlock (V l i) (V l (i + 2 ^ l))` on covered indices, rows `l < Lv` hold `V l i` at `Bm + l * N + i` for every `i` with `(i + 2 ^ l) * S ≤ bc`; memory outside rows `1 .. Lv - 1` unchanged; cost `≤ Lv * (26 * N + 11) + 4` (`spec_memoLevels`) |
| `localMemo_spec` | PROVED | `∀ l b, l < LC → b + 2 ^ l ≤ bc → s'.memory (Bm + l * bc + b) = some (bpRangeArgMinBlock shape bs b (2 ^ l))`, cost `≤ bc * 6 + 3 + (LC * (26 * bc + 11) + 4)` (`spec_localMemo`) |
| `globalMemo_spec` | PROVED | `∀ l m, l < GLC → (m + 2 ^ l) * M ≤ bc → s'.memory (Gb + l * mc + m) = some (bpRangeArgMinBlock shape bs (m * M) (2 ^ l * M))`, cost `≤ mc * (15 * M + 16) + 3 + (GLC * (26 * mc + 11) + 4)` (`spec_globalMemo`) |
| `localSparseTable_spec`, `globalSparseTable_spec` | PROVED | `emitTable 62 58 localEntryBlock` appends `(tableBits (bpLocalSparseOffsetEntries shape bs bc M mc LC) LC).map bitToNat`; `emitTable 63 60 globalEntryBlock` appends `(tableBits (bpGlobalSparseBlockEntries shape bs bc M mc GLC) BAW).map bitToNat` (`spec_localSparseTable`, `spec_globalSparseTable`) |
| `interiorCloseLayout_spec` | PROVED | for any layout meeting the size-only premises: the eight `tableBits` segments in payload order, work confined to the arrays (`spec_interiorCloseLayout`) |
| `closeSegment_spec` | PROVED | at the canonical layout, from `GeoBase n s.regs ∧ GeoUpTo n 39 s.regs`, the BP cells at `B`, `A0 + bc + 1 ≤ A1`, `A1 + bc ≤ A2`, `A2 + bc ≤ A3`, `A3 + bc ≤ Bm`, `Bm + LC * bc ≤ Gb`, `Gb + GLC * mc ≤ B`, `B + 2n ≤ s.extent` and `s.extent + 16 * (400000 * (n + 1)) < 2 ^ W`: `∃ t s' k, SafeEval W interiorCloseBlock s s' k ∧ k ≤ 1600 * (400000 * (n + 1)) ∧ s'.status = .running ∧ t.extent = s.extent ∧` memory of `t` outside `[A0, Gb + GLC * mc)` equal to `s` `∧ Emits t s' ((canonicalRelativeRmmInteriorDirectory shape).payload.map bitToNat) ∧` frame `CloseFrame` `∧ s'.keys = s.keys` (`spec_closeSegment`). This is the plan's `closeSegment_eq` (Emits conjunct) and `close_cost` (cost conjunct) |

Reading: for every shape, the charged interior close, run safely at any width
meeting the capacity premise, confines its work to the reserved arrays and then
appends exactly the stored interior directory payload, in a literal linear
number of transitions.

## S4F.2 Evidence beyond elaboration

- Fixtures before the proofs of this part (row S4-18): all eight segments for
  `n` in {0, 1, 2, 3, 4, 5, 6, 8, 12, 16, 24}, 7, 9, 15, 17, 31, 33, 63, 65,
  127, 129 and three literal inputs.
- Consumer `#guard` fixtures: 24 inputs against all eight segments.
- Mutation S4-32 (key comparison swapped in the block selection, on a scratch
  copy) rejected.

## S4F.3 Limits and deviations

- The array order is assumed; S6 reserves the arrays and places the close
  segment after the header and access segments.
- The capacity premise is about the declared width; S8 discharges it at
  `wordWidth n`.
- Process deviation (row S4-20): `lake build ...Proof.SummaryTables` ran
  409.31 s without `Global\RMQHeavyVerification`. Mitigation is in WDD-20260913-PRE1-011:
  the chain is rebuilt module by module after builder edits, and longer
  commands use a mutex wrapper.
- The canonical theorem was developed in a scratch copy outside the repository
  with a temporary placeholder (row S4-27); the repository file never
  contained one, and the consumer's axiom union is standard.
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is scheduled before the
  final candidate (documentation changes are under `docs/internal/**`).

# PRE-1 S4 checkpoint report (block statistics and the four summary tables)

| Item | Value |
| --- | --- |
| Parent | `f565adcde1682978999dead41db96d307e79ce1b` (S3) |
| Commit | the S4 checkpoint commit on top of `f565adc`; its SHA is reported in the task response |
| Builder program text (inside the firewall) | `Builder/Interior.lean` (`maxActs`, `sampleBodyBlock`, `blockBodyBlock`, `blockStatsBlock`, `baselineEntryBlock`, `relativeEntryBlock`, `argOffsetEntryBlock`, `summaryTablesBlock`), `Builder/Registers.lean` (registers 115-134); manifest re-hashed, imports and firewall table unchanged (13 modules) |
| Specification (outside) | `Spec/BlockStats.lean` |
| Proofs (outside) | `Proof/BlockStats.lean`, `Proof/SummaryTables.lean`; `Proof/Emit.lean`: `emitTable_spec` entry premise strengthened (it also receives `s.extent ≤ u.extent`); `Proof/Interior.lean` adjusted |
| Consumer | `scripts/preprocessing_stage_check.lean`: 695 axiom inventories (653 with axioms, 42 without), union {propext, Classical.choice, Quot.sound}; S4 `#guard` fixtures for 17 inputs on the compiled source (`runArray`) |
| Decisions | DD-20260913-PRE1-009, WDD-20260913-PRE1-010 |
| Commands | BUILDER_STAGE_LOG.md section "S4 interior close, checkpoint", rows S4-1..S4-15 |

## S4C.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `bpBlockArgMinPrefixPosFrom_eq_argAcc` | PROVED | `bpBlockArgMinPrefixPosFrom shape pos steps best = argAcc shape pos steps best`, where `argAcc shape pos (k + 1) best = argStep shape (pos + k) (argAcc shape pos k best)` and `argStep` is pinned (`spec_argStep_def`) |
| `natListMinFrom_append_singleton`, `natListMax_append_singleton` | PROVED | the reference minimum and maximum as left folds |
| `argAcc_ge` | PROVED | `start ≤ 2n → start ≤ argAcc shape start k start` |
| `sampleLoop_spec` | PROVED | from a block start `blk * bs` with `blk * bs + bs ≤ 2n`, the running excess, seed `2n`, maximum 0 and best `blk * bs`: `forSlots 123 124 134 sampleBodyBlock` leaves `bpBlockMinExcess`, `bpBlockMaxExcess`, `bpBlockArgMinPrefixPos shape bs blk` in registers 125-127 and `bpExcessAt shape (blk * bs + bs)` in 120, cost `≤ (bs + 1) * 28 + 3`, frame `SampleFrame`, memory, extent and keys unchanged (`spec_sampleLoop`) |
| `blockBody_spec` | PROVED | for `blk < bc`, `bc * bs ≤ 2n` and array bases `A0 + bc + 1 ≤ A1`, `A1 + bc ≤ A2`, `A2 + bc ≤ A3`, `A3 + bc ≤ B`: the memory after the block is the input memory with the start excess, minimum, maximum and argmin stored at `A0 + blk`, `A1 + blk`, `A2 + blk`, `A3 + blk`; register 120 advances to the next block start; cost `≤ (bs + 1) * 28 + 16` (`spec_blockBody`) |
| `blockStats_spec` | PROVED | for all `W ≥ 32`, shapes and running states with register 2 = 1, registers 115-119, 56, 32 and 38 holding `A0`-`A3`, `B`, `bs`, `bc` and `2n`, the BP cells as `Region s B (2n) (bpCell shape)`, `B + 2n ≤ s.extent`, `B + 4 (2n) + 4 < 2^W`, `s.extent < 2^W`, `bs + 1 < 2^W`, `bc * bs ≤ 2n` and the ordering: `∃ s' j, SafeEval W blockStatsBlock s s' j ∧ j ≤ bc * ((bs + 1) * 28 + 20) + 7 ∧ s'.status = .running ∧ (∀ b ≤ bc, s'.memory (A0 + b) = some (bpExcessAt shape (b * bs))) ∧ (∀ b < bc, s'.memory (A1 + b) = some (bpBlockMinExcess shape bs b))`, the same for the maximum at `A2` and the argmin at `A3`, memory outside `[A0, A3 + bc)` unchanged, frame `StatsFrame` outside 108, extent and keys unchanged (`spec_blockStats`) |
| `baselineEntry_spec`, `relativeEntry_spec`, `argOffsetEntry_spec` | PROVED | register 16 becomes `bpExcessAt shape (blockStartOf bs (slot * bps))`, `bpRelativeExcessEntry shape bs bps slot value` (under `baseline ≤ value + span`) and `bpBlockArgMinLocalOffset shape bs slot`, in at most 3, 8 and 4 steps (`spec_baselineEntry`, `spec_relativeEntry`, `spec_argOffsetEntry`) |
| `summaryTables_spec` | PROVED | with the statistics stored as `blockStats_spec` leaves them, registers 30, 56, 32, 57, 39, 61 holding `bps`, `bs`, `bc`, `ssc = bc / bps + 1`, `sw`, `rw`, `0 < bps`, `bc * bs ≤ 2n` and capacity premises: `∃ s' j, SafeEval W summaryTablesBlock s s' j ∧ j ≤ ssc * (7 * sw + 10) + bc * (21 * rw + 41) + 13 ∧ s'.status = .running ∧ Emits s s' ((tableBits (bpSuperblockBaselineEntries shape bs bps ssc) sw ++ tableBits (bpBlockRelativeMinExcessEntries shape bs bps bc) rw ++ tableBits (bpBlockRelativeMaxExcessEntries shape bs bps bc) rw ++ tableBits (bpBlockArgMinLocalOffsetEntries shape bs bc) rw).map bitToNat)`, frame `SummaryFrame`, key registers and keys unchanged (`spec_summaryTables`) |
| `emitTable_spec` (strengthened) | PROVED | as at S2, and the entry premise additionally receives `s.extent ≤ u.extent` (`spec_emitTable`) |

Reading: for every shape and every block layout with `bc * bs ≤ 2n`, the charged
statistics sweep stores the reference block statistics, and the charged table
fragment appends exactly the four reference summary tables in payload order.

## S4C.2 Evidence beyond elaboration

- Fixtures before the proofs (row S4-2): eleven inputs, the compiled source on
  `runArray` against the first four segments of `Spec.interiorSegments`.
- Consumer `#guard` fixtures (row S4-11): `n` in {0, 1, 2, 3, 12, 24}, the
  threshold sizes 7, 9, 15, 17, 31, 33, 63, 65, `[1, 1, 1, 1]`,
  `[4, -3, -3, 8]` and `crossBlockInput`.
- Mutation S4-14 (argmin comparison swapped, on a scratch copy of the sample
  theorem) rejected.

## S4C.3 Limits

- The layout is a parameter. The canonical instantiation (`blockSize = 2 base`,
  `blocksPerSuper = base`, `blockCount = n / base`, widths from the geometry
  bank) and the discharge of `bc * bs ≤ 2n`, the array ordering and the
  capacity premises belong to the close-segment composition.
- The fixtures reserve the arrays in a consumer harness, not in builder text.
  S6 fixes the reservation order.
- Remaining S4: memoized local and global sparse tables, level tables in store
  order, `closeSegment_eq`, `close_cost`.
- The mutation check ran on a scratch copy: the builder module sits upstream
  of the whole proof chain, so a producer mutation costs two full chain rebuilds.
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is scheduled before the
  final candidate (documentation changes are under `docs/internal/**`).

# PRE-1 S3 report (Cartesian stack pass and BP emission)

| Item | Value |
| --- | --- |
| Parent | `6a826849c20abc0bf97f2580d80922438d36c47c` (S2 complete) |
| Commit | the S3 commit on top of `6a82684`; its SHA is reported in the task response |
| Builder program text (inside the firewall) | `Builder/Cartesian.lean` (new: arrays, pop guard, pop loop, link, push, stack pass, BP unit, BP emission), `Builder/Program.lean` (new: `keyLeaf`, `wordLeaf` exactly as V3-3), `Builder/Registers.lean` (registers 100-114); firewall table and manifest updated (13 modules) |
| Specification (outside) | `Spec/Spine.lean` |
| Proofs (outside) | `Proof/Leaf.lean`, `Proof/Cartesian.lean`, `Proof/StackPass.lean`, `Proof/BPEmit.lean`; `Proof/Loops.lean` gains `forSlots_spec_pot` and `EvalG.loop_measure_pot` |
| Consumer | `scripts/preprocessing_stage_check.lean`: 607 axiom inventories, union {propext, Classical.choice, Quot.sound}; S3 `#guard` fixtures on the compiled source (`runArray`) in both models |
| Decisions | DD-20260913-PRE1-008, WDD-20260913-PRE1-009 |
| Commands | BUILDER_STAGE_LOG.md section "S3 Cartesian stack pass and BP emission", rows S3-1..S3-16 |

## S3.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `keyLeaf_def`, `wordLeaf_def` | PINNED | the V3-3 literal sequences by `rfl` |
| `keyLeaf_spec` | PROVED | `∀ {W}, 32 ≤ W → ∀ xs, KeySpec W xs (OracleInput xs) keyLeaf` (`spec_keyLeaf`), with `KeySpec` pinned by `Iff.rfl`: from every running `u` with `Inp u`, `u.regs 2 = 1`, `u.regs 4 < xs.length`, `u.regs 5 < xs.length`, `∃ u', SafeEval W leaf u u' 5 ∧ u'.status = .running ∧ u'.regs 6 = (if xs.getD (u.regs 4) 0 < xs.getD (u.regs 5) 0 then 1 else 0) ∧` frame outside 6, 7, 8 `∧` memory, extent, keys unchanged; `OracleInput xs u ↔ u.keys = fun i => xs[i]?` |
| `wordLeaf_spec` | PROVED | `∀ {W}, 32 ≤ W → ∀ xs, KeySpec W xs (WordInput W xs) wordLeaf` (`spec_wordLeaf`); `WordInput W xs u ↔ InputFits W xs ∧ xs.length + 1 ≤ u.extent ∧ ∀ k < xs.length, u.memory (k + 1) = some (encodeInt W (xs.getD k 0))` |
| `spineFrom_insertRight` | PROVED | `spineFrom (t.insertRight v) o = (spineFrom t o).takeWhile (fun e => !popsFor v e) ++ [(o + t.shape.size, ((spineFrom t o).find? (popsFor v)).elim (o + t.shape.size) (·.2.1), v)]` (`spec_spineFrom_insertRight`) |
| `insertPoint_eq_find` | PROVED | `(insertPoint t v).map (o + ·) = ((spineFrom t o).find? (popsFor v)).map (·.2.1)` |
| `spineFrom_sorted` | PROVED | `t.Valid → (spineFrom t o).Pairwise (fun a b => a.2.2 ≤ b.2.2)` |
| `openCounts_sum` | PROVED | `(openCounts T).sum = T.size` |
| `stackPass_spec` | PROVED | from a pass-start state with the arrays zeroed, after the pass the invariant `StackInv xs e0 sA xs.length` holds (stack = right spine of `buildTree xs`, leftmost indices at spine nodes, counts = `openCounts (buildTree xs).shape`), cost `≤ 50 * xs.length + 4` |
| `bpEmit_spec` | PROVED | from counts `C` with `C.length = n`, `C.sum = n` in the count region: `Emits sB s' (C.flatMap unitCells)`, cost `≤ 14 * n + 3` |
| `cartesianBP_key` | PROVED | `∀ {W}, 32 ≤ W → ∀ xs s, s.status = .running → s.regs 0 = 0 → s.regs 2 = 1 → s.regs 1 = xs.length → s.keys = (fun i => xs[i]?) → s.extent + 3 * (xs.length + 1) + 2 * xs.length + 2 < 2 ^ W → ∃ s' k, SafeEval W (.seq stackArraysBlock (.seq (stackPassBlock keyLeaf) bpEmitBlock)) s s' k ∧ k ≤ 79 * xs.length + 19 ∧ s'.status = .running ∧ s'.extent = s.extent + 3 * (xs.length + 1) + 2 * xs.length ∧ (∀ a < s.extent, s'.memory a = s.memory a) ∧ (∀ a < 2 * xs.length, s'.memory (s.extent + 3 * (xs.length + 1) + a) = some (((Cartesian.shape xs).bpCode.map bitToNat).getD a 0)) ∧` register frame outside 4-8, 10, 12, 100-114 `∧ s'.keys = s.keys` (`spec_cartesianBP_key`) |
| `cartesianBP_word` | PROVED | the same for `wordLeaf` with premise `WordInput W xs s` instead of the key bank (`spec_cartesianBP_word`) |

Reading: for every input list, the charged source fragment, run safely at any
width meeting the capacity premise, appends exactly the BP code of the
canonical Cartesian shape (ties leftmost) after its three arrays, in at most
`79 n + 19` transitions, in both input models.

## S3.2 Evidence beyond elaboration

- Fixtures before the proofs (row S3-2): the compiled source on `runArray`
  matched the reference BP code for ten inputs in both models.
- Consumer `#guard` fixtures in both models: `[]`, `[7]`, `[4, -3, -3, 8]`,
  `[1, 1, 1, 1]`, increasing, decreasing, two mixed lists and
  `crossBlockInput`.
- Producer mutation S3-14 (leaf operands swapped in the pop guard) rejected in
  `popGuard_spec`, restored byte-exact.

## S3.3 Limits

- Capacity premises are about the declared width (S8 discharges them at
  `wordWidth n`); the word-model premise `WordInput W xs s` must be carried from
  the input state through the header load, the constants and the geometry
  prelude (S7/S8 composition).
- The BP code is appended at the current extent; S6 inserts the header
  reservation in front of it.
- `stackStep_spec` is elaborated under `set_option maxHeartbeats 1600000`;
  `Proof.StackPass` builds in about 87 s.
- No registry case exists for S3 program text (C3 adds the re-hash mechanism).
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is scheduled before the
  final candidate (documentation changes are under `docs/internal/**`).

# PRE-1 S2 completion report (register-function specifications, loops, geometry prelude)

| Item | Value |
| --- | --- |
| Parent | `160593f1e73e74a7439ab485ba0265f6cd8c9170` (S2 checkpoint) |
| Commit | the S2 completion commit on top of `160593f`; its SHA is reported in the task response |
| Builder program text changed (inside the firewall) | `Builder/Registers.lean` (registers 26-28 and 38-76), `Builder/Emit.lean` (`forSlots`, `reserveArray`), `Builder/Geometry.lean` (`wordBitsBlock`, `minActs`, `geoStepBlock`, `geoChain`, `geometryPrelude`); manifest re-hashed, imports unchanged |
| Proofs added (outside the firewall) | `Proof/RegSpec.lean`, `Proof/Loops.lean`, `Proof/GeometryBank.lean`; costs added in `Proof/Geometry.lean`; `Proof/Stage2.lean` destructuring adjusted |
| Consumer | `scripts/preprocessing_stage_check.lean`: 498 axiom inventories, union {propext, Classical.choice, Quot.sound}; `#guard geoSmoke` for `n ∈ {0, 1, 7, 24, 1000}` |
| Decisions | DD-20260913-PRE1-007, WDD-20260913-PRE1-008 |
| Commands | BUILDER_STAGE_LOG.md rows S2-15..S2-32 |

## S2C.1 Checked exit statements (full types in the consumer)

| Theorem | Status | Checked statement (abridged; consumer projection named) |
| --- | --- | --- |
| `RegSpec.pure` | PROVED | `∀ {W}, 32 ≤ W → ∀ ops, RegSpec W (acts ops) (pureOKs W ops) (pureRegs ops) (fun _ => ops.length)` (`spec_RegSpec_pure`); `RegSpec` itself is pinned by `Iff.rfl` (`spec_RegSpec_def`) |
| `RegSpec.log2` | PROVED | `log2Block dst src` has register function `put (put (put r 20 (x / 2 ^ log2 x)) 21 0) dst (log2 x)` with `x = r src`, pre `r 2 = 1 ∧ r 9 = 2 ∧ x < 2 ^ W`, cost `5 * log2 x + 4`, for `dst ∉ {2, 9, 20, 21}` (`spec_RegSpec_log2`) |
| `forSlots_spec` | PROVED | for any invariant `Inv` established from `s` up to the loop registers `i`, `go` and advanced by the body (which keeps `i`, `cnt`, register 2): `∃ s' k, SafeEval W (forSlots i go cnt body) s s' k ∧ k ≤ s.regs cnt * (J + 4) + 3 ∧ s'.status = .running ∧ Inv (s.regs cnt) s' ∧ s'.regs i = s.regs cnt ∧ s'.regs cnt = s.regs cnt` (`spec_forSlots`) |
| `emitFlatMap_spec` | PROVED | if the body at slot `k` appends `g k` and keeps a caller frame `Keep`: `Emits s s' ((List.range (s.regs cnt)).flatMap g) ∧ Keep s'` with the same cost (`spec_emitFlatMap`) |
| `reserveArray_spec` | PROVED | `Emits s s' (List.replicate (s.regs cnt + 1) 0) ∧ s'.regs base = s.extent`, cost `5 * s.regs cnt + 4`, frame outside `base`, 10, 12, premises `regs 0 = 0`, `regs 2 = 1`, `s.extent + s.regs cnt + 1 < 2 ^ W` (`spec_reserveArray`) |
| `geometryPrelude_spec` | PROVED | `∀ {W n}, 32 ≤ W → 2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W → ∀ s, s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = n → ∃ s' k, SafeEval W geometryPrelude s s' k ∧ k ≤ 25 * W + 40 + 39 * (5 * W + 20) ∧ s'.status = .running ∧ GeoBase n s'.regs ∧ GeoUpTo n 39 s'.regs ∧ (∀ x, ¬ (20 ≤ x ∧ x ≤ 28) → ¬ (30 ≤ x ∧ x ≤ 76) → s'.regs x = s.regs x) ∧` memory, extent, keys, key registers unchanged (`spec_geometryPrelude`) |
| `geoChain_spec` | PROVED | the first `k ≤ 39` bank steps from any running `GeoBase n` state, cost `k * (5 * W + 20)`, frame outside 20-28 and `[38, 38 + k)` (`spec_geoChain`) |
| `interiorGeometry_spec` (strengthened) | PROVED | as at the checkpoint, now with `k ≤ 25 * W + 40` (`spec_interiorGeometry`) |
| bank identities | PINNED | `GeoUpTo n k r ↔ ∀ i < k, r (38 + i) = geoVal n i` and `GeoBase n r` by `Iff.rfl`; `spec_geoVal_pins` states 35 of the 39 values by `rfl` at independently written reference terms, among them `packedRankWordSize n`, `GenericSelect.superStride (2 * n)`, `packedSuperSlots n`, `packedSparseSlots n`, `packedRankBlockWidth n`, `packedLocalWidth n`, the rank slot counts, `bpFringeChunkRowCount`, `canonicalRelativeRmmInteriorRawPayloadOverhead n`, `bpFringeTableOverhead n`, `genericSparseExceptionBPCloseAccessOverhead n`, `packedReviewerCellWidth n` and `PackedWordRAM.wordWidth n` |

## S2C.2 Evidence beyond elaboration

- Executable: before any geometry proof, a scratch evaluation of the prelude by
  `evalF` matched all 77 registers against reference values for `n < 40` and
  eight larger sizes up to 100000 (row S2-19, run 3); the consumer keeps five
  sizes as `#guard` lines.
- Producer mutation S2-27: changing the budget constant of step 36 is rejected
  in `geoStep36`, restored byte-exact.

## S2C.3 Limits and deviations

- The capacity premise `2 ^ 32 * (2 * n + 4) ^ 8 < 2 ^ W` is not yet
  discharged at `W = wordWidth n` (S8). The intended argument is recorded in
  DD-20260913-PRE1-007 and is not machine-checked.
- The end-to-end sparse-level table theorems of the checkpoint still state no
  cost conjunct; the component and prelude costs exist.
- Not in the bank: metadata offsets, component word counts and all
  `lc`/`sc`-dependent quantities (S6/S7, partly by measured cursors).
- Process deviation (row S2-19, run 2): one scratch discovery command ran
  316.91 s without the heavy-verification mutex. It was expected to take
  seconds, and it crashed at the interpreter recursion limit. Scratch
  evaluations now carry an outer `timeout 280` (WDD-20260913-PRE1-008).
- Checks for this commit: `git diff --check`, strict design check against
  `c1c970b`, the per-commit design check and the builder firewall (outcomes in
  the task response). The claim-drift strict scan is not run on this commit
  (documentation changes are under `docs/internal/**`; the coordinator
  schedules the strict scan before the final candidate).

# PRE-1 S2 checkpoint report (emission calculus and first end-to-end table)

| Item | Value |
| --- | --- |
| Parent | `361fe822f126b88e43e351e56293217707e9916a` (C1) |
| Commit | the S2 checkpoint commit on top of `361fe82`; its SHA is reported in the task response |
| Authorization | coordinator disposition after PRE-1-A1C: S2 may begin once the C1 commit exists; S2 to S6 in plan order; C2 and C3 before S7 |
| Builder program text (inside the firewall) | `RMQ/Core/WordRAM/Construction/Builder/{Registers,Emit,Geometry,Interior}.lean`, registered in `scripts/preprocessing_builder_firewall.ps1` and `builder_manifest.json` (version 1, appended entries) |
| Proofs (outside the firewall) | `RMQ/Core/WordRAM/Construction/Proof/{Base,Emit,Interior,Geometry,Stage2}.lean`, namespace `RMQ.SuccinctFinal.PackedConstruction.Proof` |
| Consumer | `scripts/preprocessing_stage_check.lean` (standalone; not in the builder replay registry or `scripts/gate.ps1`) |
| Decisions | DD-20260913-PRE1-006, WDD-20260913-PRE1-007 |
| Commands | BUILDER_STAGE_LOG.md section "S2 Emission calculus checkpoint", rows S2-1..S2-14 |

## S2.1 Checked exit statements

All restated at full type in the stage consumer (projections `spec_*`) and
checked by `lake env lean scripts/preprocessing_stage_check.lean` (row S2-10,
11.92 s, exit 0). `Emits s₀ s vals` means `s.extent = s₀.extent + vals.length`
and every memory address in `[s₀.extent, s₀.extent + vals.length)` holds
`vals[a - s₀.extent]?` while every other address is unchanged (consumer
`spec_Emits_def`, by `Iff.rfl`).

| Theorem | Status | Checked statement (abridged only where marked) |
| --- | --- | --- |
| `emitBits_spec` | PROVED | `∀ {W}, 32 ≤ W → ∀ (w v : Operand), (v : Nat) ≠ 12 → ∀ s, s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs v < 2^W → s.regs w < 2^W → s.extent + s.regs w < 2^W → ∃ s' k, SafeEval W (emitBits w v) s s' k ∧ k ≤ 7 * s.regs w + 3 ∧ s'.status = .running ∧ Emits s s' ((natToBitsLE (s.regs w) (s.regs v)).map bitToNat) ∧ (∀ r, r ≠ 10 → r ≠ 11 → r ≠ 12 → r ≠ 13 → s'.regs r = s.regs r) ∧ s'.keyRegs = s.keyRegs ∧ s'.keys = s.keys` |
| `emitTable_spec` | PROVED | abridged: for any entry block that, from every running state agreeing with `s` outside its declared writes and registers 10-16 (memory below `s.extent`, keys and key registers equal, `regs 14 < regs count`), safely computes `regs 16 = f (regs 14) < 2^W` in at most `J` steps without changing memory, extent, keys, key registers or undeclared registers: `∃ s' k, SafeEval W (emitTable count w entry) s s' k ∧ k ≤ s.regs count * (J + 7 * s.regs w + 7) + 3 ∧ s'.status = .running ∧ Emits s s' ((flattenPayloadWords (((List.range (s.regs count)).map f).map (natToBitsLE (s.regs w)))).map bitToNat)` plus frame, key registers and keys preserved; premises `32 ≤ W`, `count` and `w` outside 10-16 and outside the entry's writes, the entry writes none of 2, 9, 14, constants in 2 and 9, `s.regs count + 1 < 2^W`, `s.regs w < 2^W`, `s.extent + s.regs count * s.regs w < 2^W` (full type: consumer `spec_emitTable`) |
| `log2Block_spec` | PROVED | abridged: `∀ {W}, 32 ≤ W → ∀ (dst src : Operand), dst ∉ {2, 9, 20, 21} → ∀ s, running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs src < 2^W → ∃ s' k, SafeEval W (log2Block dst src) s s' k ∧ k ≤ 5 * Nat.log2 (s.regs src) + 4 ∧ running ∧ s'.regs dst = Nat.log2 (s.regs src) ∧ s'.memory = s.memory ∧ s'.extent = s.extent ∧ (∀ r : Nat, r ≠ dst → r ≠ 20 → r ≠ 21 → s'.regs r = s.regs r)` plus key registers and keys preserved (full type: consumer `spec_log2Block`) |
| `interiorGeometry_spec` | PROVED | abridged: `∀ {W}, 32 ≤ W → ∀ s n, running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = n → (n+2)*(n+2)*((n+2)*(n+2)) < 2^W → ∃ s' k, SafeEval W interiorGeometryBlock s s' k ∧ running ∧` registers 30..37 hold `log2 n + 1`, its square, `n / (log2 n + 1)`, the macro sample count, the two `bpSparseLevelDomain` values and the two `bpSparseLevelWidth` values (literal terms in consumer `spec_interiorGeometry`), and memory, extent, keys, key registers and every register outside 20-25 and 30-37 are unchanged; no cost conjunct |
| `levelEntry_spec`, `levelTable_spec` | PROVED | the sparse-level entry block computes `bpSparseLevelCell d i` (cost `≤ 5 * log2 d + 7`; premises `2 ≤ d`, `i < d`, `d * (log2 d + 1) < 2^W`); the table block emits `flattenPayloadWords ((bpSparseLevelEntries d).map (natToBitsLE w))` as 0/1 cells (not restated in the consumer; reached through the two theorems below) |
| `localLevelTable_emits_payload` | PROVED | `∀ {W}, 32 ≤ W → ∀ (shape : CartesianShape) s, s.status = .running → s.regs 2 = 1 → s.regs 9 = 2 → s.regs 1 = shape.size → (shape.size+2)*(shape.size+2)*((shape.size+2)*(shape.size+2)) < 2^W → s.extent + bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize * bpSparseLevelWidth (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) < 2^W → ∃ s' k, SafeEval W (.seq interiorGeometryBlock (levelTableBlock 34 36)) s s' k ∧ s'.status = .running ∧ Emits s s' ((canonicalRelativeRmmInteriorLocalLevelTable shape).table.payload.map bitToNat)` |
| `globalLevelTable_emits_payload` | PROVED | the same statement with `macroSampleCount`, `levelTableBlock 35 37` and `canonicalRelativeRmmInteriorGlobalLevelTable` |

Reading of the end-to-end theorems: for every shape, the charged source
fragment, run safely at any width `W ≥ 32` meeting the capacity premises,
appends exactly the stored payload bits of the reference table structure,
because `Spec.FixedWidthNatTable.payload_eq_tableBits` (S1) pins every table
structure's payload to its entries.

## S2.2 Limits and open S2 items

- The end-to-end theorems state no cost bound (the component specifications
  `emitBits`, `emitTable`, `log2Block` and `levelEntry` do); composing costs
  into a work theorem is later work.
- Capacity premises (`32 ≤ W`, `(n+2)^4 < 2^W`, extent bounds) are about the
  declared width; relating them to `wordWidth xs.length = 32 + 8 *
  packedReviewerCellWidth xs.length` is stage S8 and is not proved here.
- Open S2 plan items: `emitFlatMap_spec`, `reserveArray_spec`, the remaining
  geometry bank, the helper blocks (power of two, ceiling division, minimum,
  monus, bit copy), and cost conjuncts in the end-to-end statements.
- The smoke checks run the executable structured evaluator `evalF` (sound for
  `Eval`) on the actual source fragment for `n ∈ {0, 5, 24}`; they are neither
  kernel evaluation nor the charged interpreter (ruling Q9).
- Producer mutation S2-13 is discovery evidence only; no registry case exists
  for S2 program text (C3 adds the per-mutation re-hash).
- Checks for this commit: `git diff --check`, `scripts/design_decision_check.ps1
  -Strict -Base c1c970b8bfbae03163633365e512d487ae1c98f2` and the per-commit
  design check (outcomes in the task response and the next stage-log section).
  The claim-drift strict scan is not run on this commit (its documentation
  changes are under `docs/internal/**`; the coordinator's rule schedules the
  strict scan before the final candidate).

# PRE-1 condition C1 report (contract version 3)

| Item | Value |
| --- | --- |
| Audit | PRE-1-A1C on `5f325dd`: CONTINUATION_PASS_WITH_CONDITIONS; report `2026-09-13_PRE1_contract_continuation.md` in the auditor's worktree, 84,923 bytes, SHA-256 2650BA3CC8CF8DDEB58E53DDC45121DFB127E0728B957A2FD540AD8B779B6A0A (verified; sections 2-4 read in full) |
| Coordinator disposition | C1 before S2, C2 before S7 instantiates `HeaderUse` at the constants, C3 before S7 (re-hash mechanism, V2-2 case (i)) and before the S8 freeze (foundation cases), P3-7 and P3-1 with C3; Q9a stands; P3-3 resolved for the contract names; S2 authorized after the C1 commit; claim-drift scan `-Strict` for docs/public text commits before the final candidate; heavy-verification mutex for commands over five minutes |
| Commit | the C1 commit on top of `22c0c20`; its SHA is reported in the task response |
| Changed paths | `docs/internal/extensions/pre1/{CONTRACT,AMENDMENTS,BUILDER_PLAN,BUILDER_STAGE_LOG,REPORT}.md`, `docs/internal/DESIGN_DECISIONS.md` (DD-20260913-PRE1-005), `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (WDD-20260913-PRE1-006); no Lean, script, registry or manifest change |

C1 items as frozen (CONTRACT.md V3-1..V3-10):

- (a) V3-1: `builderSource`, `builderBody`, `keyLeaf`, `wordLeaf`,
  `builderProgram`, `builderProgramWord`, `builderBudget`, `efficientBuild`,
  `efficientBuildWord` in `RMQ/Core/WordRAM/Construction/Builder/Program.lean`,
  namespace `RMQ.SuccinctFinal.PackedConstruction`; a consumer `run_cmd` over
  `Lean.Environment.getModuleIdxFor?`; a relocation case for `efficientBuild`
  through the C3 re-hash, rejected at the `run_cmd` line set.
- (b) V3-2: `example : List BInstr := @builderProgram` and `@builderProgramWord`.
- (c) V3-3: `builderProgram = (builderSource keyLeaf).compileAt 0 ++ [⟨.halt 3⟩]`,
  `builderProgramWord = (builderSource wordLeaf).compileAt 0 ++ [⟨.halt 3⟩]` by
  `rfl`; `keyLeaf` = loadKey 0 4, loadKey 1 5, compareKey 6 0 1, move 6 6, move 6 6;
  `wordLeaf` = add 7 4 2, load 7 7, add 8 5 2, load 8 8, comparison lt 6 7 8;
  leaf register interface fixed (i in 4, j in 5, result in 6, one in 2, scratch
  7/8 and key registers 0/1, halt value in 3).
- (d) V3-4: leaf-difference theorem with literal positions `P` and literal
  instruction lists `K`, `Wd` at those positions.
- (e) V3-5: both `ProgramContract` instances with numerals `L`, `B`, `B'`.
- (f) V3-6: exact extraction bodies (match on final status, `[]` when not
  halted); `efficientBuildWord` takes the encoding width explicitly because
  `wordWidth` is outside the builder firewall, and its pin and equality
  theorem are stated at `wordWidth xs.length`. Flagged for the coordinator as a
  refinement of the audit's C1(f) wording.
- (g) V3-7: case (i) optional-parameter mutations through the C3 re-hash,
  rejected at exactly the `@` line; case (ii) one consumer-numeral mutation per
  numeral with its exact line set.
- (h) V3-8: word-model qualification of V2-1 recorded as a limit.
- (i) V3-9: `tailNeverWritesR1` through `Block.compile_writesOnly` from a
  compositional `(builderBody leaf).WritesOnly (· ≠ 1)`; no list-wide kernel
  `decide`.

Checks for this commit: `git diff --check`, `scripts/design_decision_check.ps1
-Strict -Base c1c970b8bfbae03163633365e512d487ae1c98f2` and the per-commit
design check (outcomes in the task response and BUILDER_STAGE_LOG.md). The
claim-drift scan is not run on this commit: it changes only
`docs/internal/**`, and the coordinator's rule schedules the strict scan before
the final candidate.
# PRE-1 S1 report (machine-free specification checkpoint)

## S1.1 Identity

| Item | Value |
| --- | --- |
| Handle / title | PRE-1, `(PRE-1) Prove efficient packed preprocessing` |
| Branch / worktree | `codex/pre-1-packed-preprocessing`, `C:/Users/poin/.codex/worktrees/2fb8/RMQ` |
| Base (frozen contract evidence head) | `c1c970b8bfbae03163633365e512d487ae1c98f2` |
| Parent of this checkpoint | `5f325ddb856b9095d1ad2aacc0bc69eda571d447` (Stage 0) |
| Commits | S1 checkpoint `b3570acded8c01b80206a2cf972b2b49db119072` (exit theorems), then the S1 completion commit on top of it (envelopes); the latter's SHA is reported in the task response (a file cannot contain its own commit SHA) |
| Governing prompt | `PRE1_BUILDER_CONTINUATION.md`, 32,330 bytes, SHA-256 CBB3DC08421F42DBB53AFAD451F3C101925E71E9D328880D9EB229BEA803C76A (re-verified) |
| Preflight | `scripts/project_skill_preflight.ps1` (governance `0e6a00f`, required `rmq-proof-sprint`): PASS, 4.26 s |
| Toolchain / host | Lean 4.22.0 pinned `lake.exe`, `LEAN_NUM_THREADS=1`; Windows 11 Pro 10.0.26200, pwsh 7.6.6, shared host |

## S1.2 Changed paths (relative to `5f325dd`)

Added: `RMQ/Core/WordRAM/Construction/Spec/{OpenCounts,Dyck,ArgMinSplit,Positions,Plan,Envelope}.lean`,
`scripts/preprocessing_spec_check.lean`.
Appended (no existing text changed): `docs/internal/DESIGN_DECISIONS.md`
(DD-20260913-PRE1-003, DD-20260913-PRE1-004), `docs/internal/WORKFLOW_DESIGN_DECISIONS.md`
(WDD-20260913-PRE1-004, WDD-20260913-PRE1-005), `docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md`
("S1 evidence rows", "S1 envelope evidence rows"), `docs/internal/extensions/pre1/BUILDER_STAGE_LOG.md`
(section S1 and its continuation). Rewritten top of this report (the Stage 0 report below is kept).
Unchanged: every closure module, `HeaderUse.lean`, both firewalls and manifests,
both registries and runners, `scripts/preprocessing_builder_check.lean`,
`scripts/gate.ps1`, `lakefile.toml`, `RMQ.lean`, shared Packed modules.
The Spec modules are outside the builder firewall: they import reference
modules (Shape, Succinct, GenericSelect, SuccinctClose, Packed Allocation) and
no firewalled module imports them; the builder firewall still passes on 7
closure modules.

## S1.3 Exit theorems (checked types)

Namespace `RMQ.SuccinctFinal.PackedConstruction.Spec` (`Stack` below abbreviates
`StackCartesianTreeSpec`; `Cartesian.StackCartesianTree` is the reference tree).

1. `buildMemory_eq_plan` (Plan.lean), CLOSED:
   ```lean
   theorem buildMemory_eq_plan (xs : List Int) :
       let shape := SuccinctClassic.cartesianShape xs
       let n := xs.length
       let lc := longCount shape
       let sc := packedReviewerSparseCount shape
       let oldW := packedReviewerCellWidth n
       let W := wordWidth n
       let oldBits := packedReviewerCellCount n lc sc * oldW
       let count := GenericSelect.selectCeilDiv oldBits W
       let body :=
         natToBitsLE oldW lc ++ shape.bpCode ++ (accessSegments shape).flatten ++
           (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape ++
           List.replicate (oldBits - (oldW + packedReviewerPayloadLength n lc sc)) false
       buildMemory xs = metadataOf n lc sc ++
         (List.range count).map fun i =>
           bitsToNatLE (cellAt (body ++ List.replicate (count * W - oldBits) false) W i)
   ```
   with the named segments (each `tableBits entries width := flattenPayloadWords (entries.map (natToBitsLE width))`
   unless raw), pinned by `rfl` in the consumer:
   `accessSegments shape` = [final rank super `canonicalSuperRankEntries false b ws ws` @ `ws`;
   final rank block `canonicalBlockRankEntries false b ws ws` @ `machineWordBits (ws*ws)`;
   `baseOccurrences`/`baseWordIndices`/`ranksBefore`/`firstOffsets` of `superEntries b false` @ `superFieldWidth b`;
   the same four of `localEntries b false` @ `localFieldWidth b`;
   `canonicalSuperRankEntries true L wsL 1` @ `wsL` and `canonicalBlockRankEntries true L wsL 1` @ `wsL`
   with `L = longSuperFlagBits b false`, `wsL = machineWordBits L.length`; raw `L`;
   `longSuperRelativeEntries b false` @ `longSuperRelativeWidth b`;
   `canonicalSuperRankEntries true S wsS 1` @ `wsS`, `canonicalBlockRankEntries true S wsS 1` @ `wsS`
   with `S = sparseExceptionEffectiveFlagBits b false`, `wsS = machineWordBits S.length`; raw `S`;
   `sparseExceptionRelativeEntries b false` @ `sparseExceptionRelativeWidth b`], `b = shape.bpCode`,
   `ws = machineWordBits b.length`;
   `interiorSegments shape` = [`bpSuperblockBaselineEntries` @ `superWidth`, `bpBlockRelativeMinExcessEntries`,
   `bpBlockRelativeMaxExcessEntries`, `bpBlockArgMinLocalOffsetEntries` @ `relativeWidth`,
   `bpLocalSparseOffsetEntries` @ `offsetWidth`, `bpGlobalSparseBlockEntries` @ `blockAddressWidth`,
   `bpSparseLevelEntries (bpSparseLevelDomain macroSize)`, `bpSparseLevelEntries (bpSparseLevelDomain macroSampleCount)`
   @ their `bpSparseLevelWidth`], all over `RelativeRmm.canonicalLayout shape`;
   `fringeSegment` = `bpFringeChunkEntries c` @ `bpFringeChunkEntryWidth c`,
   `selectChunkSegment` = `bpChunkSelectEntries c false` @ `bpChunkSelectEntryWidth c`,
   `c = bpFringeChunkBits b.length`.
   Supporting: `FixedWidthNatTable.payload_eq_tableBits : ∀ {entries width} (table : FixedWidthNatTable entries width), table.payload = tableBits entries width`;
   `canonicalReviewerPayload_eq_plan : packedReviewerPayloadBits shape = shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape`;
   `metadata_eq_metadataOf : metadata shape = metadataOf shape.size (longCount shape) (packedReviewerSparseCount shape)` (rfl), restated under the plan's name `metadataOf_eq`;
   `metadataOf_length : (metadataOf n lc sc).length = 174`;
   `buildMemory_plan_body_length` (the body has length `packedReviewerCellCount n lc sc * oldW`);
   `planPayload_length : (shape.bpCode ++ ... ++ selectChunkSegment shape).length = packedReviewerPayloadLength shape.size (longCount shape) (packedReviewerSparseCount shape)`;
   `shapeMemory_eq_plan`, `shapeMemory_eq_plan_of_size`.
2. `bpCode_eq_openCounts_flatMap` (OpenCounts.lean), CLOSED:
   `∀ T : CartesianShape, T.bpCode = (openCounts T).flatMap (fun c => List.replicate c true ++ [false])`,
   with `openCounts .empty = []`, `openCounts (.node l r) = (openCounts l ++ [0]).modifyHead (· + 1) ++ openCounts r`.
3. Length law `openCounts_length`, CLOSED: `∀ T, (openCounts T).length = T.size`.
4. `Stack.openCounts_insertRight`, CLOSED:
   `∀ (t : StackCartesianTree) (value : Int), openCounts (t.insertRight value).shape = match Stack.insertPoint t value with | none => openCounts t.shape ++ [1] | some ld => (openCounts t.shape).modify ld (· + 1) ++ [0]`,
   where `insertPoint .empty _ = none` and `insertPoint (.node left pivot right) v = if v < pivot then some 0 else (insertPoint right v).map (fun k => left.shape.size + 1 + k)`
   (strict pop, equal keys descend right). Also `buildTree_append_singleton : buildTree (xs ++ [v]) = (buildTree xs).insertRight v` and
   `bpCode_shape_eq_openCounts_buildTree : (Cartesian.shape xs).bpCode = (openCounts (buildTree xs).shape).flatMap (...)`.
5. `bpCode_closes_le_opens` (Dyck.lean), CLOSED:
   `∀ (T : CartesianShape) (p : Nat), rankPrefix false T.bpCode p ≤ rankPrefix true T.bpCode p`
   (every `p`, including past the end). Also `bpExcessAt_succ_of_open : T.bpCode[p]? = some true → bpExcessAt T (p+1) = bpExcessAt T p + 1`,
   `bpExcessAt_succ_of_close : T.bpCode[p]? = some false → 1 ≤ bpExcessAt T p ∧ bpExcessAt T (p+1) = bpExcessAt T p - 1`,
   `bpExcessAt_add_closes`, `bpCode_rank_full : rankPrefix b T.bpCode T.bpCode.length = T.size`, `bpExcessAt_of_length_le`.
6. `bpRangeArgMinBlock_split` (ArgMinSplit.lean), CLOSED:
   `∀ (shape : CartesianShape) (blockSize start a b : Nat), 0 < b → bpRangeArgMinBlock shape blockSize start (a + b) = bpBetterArgMinBlock shape blockSize (bpRangeArgMinBlock shape blockSize start a) (bpRangeArgMinBlock shape blockSize (start + a) b)`.
   It is proved for the reference key `bpExcessAt shape (bpBlockArgMinPrefixPos shape blockSize block)` with its clamps, via
   `bpBetterArgMinBlock_assoc`. Instances: `bpRangeArgMinBlock_double` (every `c`, including 0),
   `bpRangeArgMinBlock_pow_succ : bpRangeArgMinBlock shape bs start (2^(l+1)) = better (… start (2^l)) (… (start + 2^l) (2^l))`,
   `bpRangeArgMinBlock_pow_succ_mul` (spans `2^(l+1) * m`, every `m`). The premise `0 < b` is necessary: at `b = 0` the right-hand side still compares block `start + a`.
7. `selectFrom_scan` (Positions.lean), CLOSED:
   `∀ (target : Bool) (bits : List Bool) (base occurrence : Nat), selectFrom target bits base occurrence = (occurrencePositionsFrom target bits base)[occurrence]?`.
   Array-fill form `positionFill_spec : positionFill target bits 0 0 arr k = if k < occurrenceCount bits target then position bits target k else arr k`;
   `position_of_occurrenceCount_le : occurrenceCount bits target ≤ k → position bits target k = bits.length`;
   `position_eq_fill_or_length : position bits target k = if k < occurrenceCount bits target then positionFill target bits 0 0 arr k else bits.length`.
8. `rankPrefix_running` (Positions.lean), CLOSED:
   `∀ (target : Bool) (bits : List Bool) (c p : Nat), p ≤ bits.length → (runningRanksFrom target bits c)[p]? = some (c + rankPrefix target bits p)`.
   Sampled form `rankSampleFill_spec : 0 < stride → rankSampleFill target stride bits 0 0 arr w = if w * stride ≤ bits.length then rankPrefix target bits (w * stride) else arr w`,
   and `rankSampleEntries_eq_fill`, `canonicalSuperRankEntries_eq_fill` (stride `blocksPerSuper * wordSize`),
   `canonicalBlockRankEntries_eq_fill` (word fill minus the saved super fill at `w / blocksPerSuper`), each under positive `wordSize`/`blocksPerSuper`.

9. Literal envelopes (Envelope.lean, plan S1 item 6), CLOSED:
   `planPayload_length_add_two_le : ∀ shape, (shape.bpCode ++ (accessSegments shape).flatten ++ (interiorSegments shape).flatten ++ fringeSegment shape ++ selectChunkSegment shape).length + 2 ≤ 400000 * (shape.size + 1)`;
   `tableBits_length : (tableBits entries width).length = entries.length * width`;
   `accessEntryCounts_le` (the ten access entry lists and both raw flag vectors, each `≤ 400000 * (shape.size + 1)`),
   `selectSlotCounts_le : superSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1) ∧ localSlotCount shape.bpCode false ≤ 400000 * (shape.size + 1)`,
   `interiorEntryCounts_le` (the eight interior entry lists), `microtableRowCounts_le` (fringe and select-chunk rows);
   `oldBits_le : packedReviewerCellCount n lc sc * packedReviewerCellWidth n ≤ packedReviewerPayloadLength n lc sc + 2 * packedReviewerCellWidth n`;
   `denseBits_le : selectCeilDiv bits W * W ≤ bits + W`; `wordWidth_le_linear : wordWidth n ≤ 192 * n + 576`;
   `planBuffer_le : ∀ xs, oldBits ≤ 400384 * xs.length + 401150 ∧ selectCeilDiv oldBits (wordWidth xs.length) * wordWidth xs.length ≤ 400576 * xs.length + 401726`;
   `buildMemory_length_le : ∀ xs, (buildMemory xs).length ≤ 400576 * xs.length + 401900`;
   `canonicalLayout_blockCount_le : blockCount ≤ shape.size`, `canonicalLayout_superSampleCount_le : superSampleCount ≤ shape.size + 1`,
   `canonicalLayout_macroSampleCount_le : macroSampleCount ≤ shape.size + 1`, `canonicalLayout_globalLevelCount_le : globalLevelCount ≤ shape.size + 2`,
   `canonicalLayout_levelCount_mul_blockCount_le : levelCount * blockCount ≤ 3 * shape.size`;
   `fringeRows_mul_scan_le : bpFringeChunkRowCount (bpFringeChunkBits (2 * n)) * (bpFringeChunkBits (2 * n) + 1) ≤ 256 * (n + 1)`,
   `selectRows_mul_scan_le : bpChunkSelectRowCount (bpFringeChunkBits (2 * n)) * (bpFringeChunkBits (2 * n) + 1) ≤ 64 * (n + 1)`;
   `log2_rounds_le : Nat.log2 x + 1 ≤ x + 1`. They are built on the checkout's existing literal overhead
   bounds (`packedReviewerCellBound_add_two_le_linearCapacity`), not on `LittleOLinear`. They are upper bounds only.

Source corrections honored: the emitted sparse flag leaf and the base of the
sparse flag-rank tables is `sparseExceptionEffectiveFlagBits` (a producer
mutation to `sparseFlagBits` is rejected); the interior segments are the
executed `canonicalRelativeRmm*` tables, not the legacy close tables bound in
`concreteBPNativeSuccinctRMQFlatPayloadSourcePayload`; degenerate layouts
(`n ∈ {0,1,2,3}`) are instances of the universal statements.

No counterexample to any planned statement was found. One planned formulation
was tightened: the plan's split law assumed `a, b ≥ 1`, and the proved law
needs only `0 < b`.

## S1.4 Typed consumer and checks

`scripts/preprocessing_spec_check.lean` (run standalone; separate from the
builder registry consumer, WDD-20260913-PRE1-004/005): 56 theorems (52 full-type projections and definition pins, 4 `decide` fixture theorems)
including `rfl` pins of `accessSegments`, `interiorSegments`, both microtable
segments and `metadataOf`; kernel `decide` on tiny pure lists (`[4,-3,-3,8]`
open counts `[2,0,1,1]` and BP `[T,T,F,F,T,F,T,F]`; `[1,1,1,1]` open counts
`[1,1,1,1]`; the plan lists `[]`, `[7]`, `crossBlockInput` with hand-derived open
counts `[]`, `[1]`, `[5,0,1,0,0,0,4,0,0,0,1,1]`; `insertPoint` strict pop and tie; `bpBetterArgMinBlock` tie keeps
the left block; position and rank fills on the BP of `[4,-3,-3,8]`); `#guard`
(Lean evaluator, not the kernel) comparing `buildMemory xs` with the plan for
`[]`, `[7]`, `[4,-3,-3,8]`, `crossBlockInput`; 112 `#print axioms`, union
{propext, Classical.choice, Quot.sound}; final line `PRE1-SPEC-TYPED-CONSUMERS PASS`.

| Check | Duration | Outcome |
| --- | --- | --- |
| Focused `lake build` of OpenCounts / Dyck / ArgMinSplit / Positions / Plan / Envelope (final runs) | 2.63 / 4.12 / 3.48 / 6.66 / 22.20 (Envelope with the Plan rebuild) s | exit 0 each; every intermediate failing run is in BUILDER_STAGE_LOG.md S1-2..S1-8 and S1-16 |
| `lake env lean scripts/preprocessing_spec_check.lean` (final) | 51.37 s | exit 0, PASS, 112 inventories |
| `scripts/preprocessing_builder_firewall.ps1` | 8.92 s | PASS, 7 closure modules |
| Trust scans K3/K4 over `RMQ`, `lakefile.toml`, `Spec/` and the spec consumer (after S1-9 and again after S1-19) | < 1 s | no matches (exit 1) |
| Producer mutations (effective-flag leaf, microtable swap) | 5.14 s, 6.70 s | both rejected; bytes restored and hash-checked |
| `git diff --check`, `scripts/design_decision_check.ps1 -Strict -Base c1c970b...` | see task response | run on the staged tree before the commit and on the committed range after it |

Matrix byte integrity: `ACCEPTANCE_MATRIX.md` after CRLF-to-LF normalization
starts with the exact `5f325dd` blob (57,616 bytes) and is strict UTF-8; the two
S1 appendices only add rows.

Not executed at S1 (not required by the S1 scope): contract replay, builder
replay, gate checkers, `lake build` of the default target, the executable
validator, claim-drift scan. No replay input changed.

## S1.5 Proof digestion

What changed conceptually. The target `buildMemory xs` is now an explicit
emission order: 174 metadata words that depend only on `n`, `lc` and `sc`,
then a re-chunking at width `W` of one bit string whose pieces are the old
header, the BP code, 18 access tables, 8 interior tables, 2 microtables and 2
zero paddings. Every table is its entry list written in fixed-width
little-endian bits, and this is proved from the table invariants rather than
read off a constructor. The four algorithmic insights a linear builder needs
are now theorems about the reference definitions: the BP code is a run-length
code of open counts, and right-end insertion into the stack tree changes those
counts in one place; the BP prefix never has more closes than opens; the
leftmost block argmin splits over any partition with a nonempty right part, so
doubling tables work; and one left-to-right scan yields every select position
and every sampled rank.

Plain English. We wrote down exactly which bits the fast builder must
produce, in which order, and proved that this list really is the accepted
memory image for every input. We also proved the four facts that let a simple
one-pass program compute those bits without re-scanning.

Live assumptions. None beyond the reference definitions; the side conditions
are `0 < b` in the split law (necessary), positive strides in the fill lemmas,
and `p ≤ bits.length` for the running-rank list index. The envelopes are crude
literal upper bounds (ruling Q7).

Named downstream consumers. S3 `bpSegment_eq` (open counts, insertion law),
S4 `blockStats_spec`/`localSparse_spec`/`globalSparse_spec` (Dyck and split
laws), S5 `posPass_spec`/`rankTables_spec`/`accessSegment_eq` (fills,
effective flags), S6 `bufferStage_spec` (both paddings, body length), S7
`metadataStage_spec` and `efficientBuild_eq_buildMemory` (`buildMemory_eq_plan`,
`metadataOf`), S8 `buildWork_bound` and `Workspace.lean` (the envelopes).

What a skeptical graduate student would ask next. "Your insertion law is
stated on the tree. The machine only has a stack of indices and an `ld` array.
Where is the lemma that `insertPoint` is the leftmost-descendant index of the
last node popped from the right spine, with pops taken from the deep end?" (Not
yet proved; it is the S3 stack invariant.) And: "Your envelopes bound the
reference counts, but the machine also runs inner loops you have not fixed yet,
such as the per-slot relative-offset scans and the per-row fringe statistics.
Are those inner loops really bounded by these counts times a constant?" (Only
the fringe and select-chunk row scans are bounded here; the others are S4/S5
obligations.)

## S1.6 Next

No S1 item remains. S2 and later stages wait for the coordinator's
authorization after the PRE-1-A1 continuation audit. No aggregate slot is
requested. Notes for the coordinator: (1) the kernel cannot evaluate
`buildMemory` (`Cartesian.shape` is well-founded recursion), so the plan's
"decide/rfl on the four fixtures" exit clause is met by kernel `decide` on the
structural reference objects (`insertRight` folds, positions, ranks) and by
`#guard` (Lean evaluator) comparing `buildMemory` with the plan on the four
lists; the plan's alternative, an IO check in `RMQ/Validation/Preprocessing.lean`,
belongs with that executable's creation in a later stage. (2) The spec consumer
is standalone and is not reached by the builder replay or a gate checker yet.
# PRE-1 Stage 0 report (contract amendments and operational foundations)

## 1. Identity

| Item | Value |
| --- | --- |
| Handle / title | PRE-1, `(PRE-1) Prove efficient packed preprocessing` |
| Worker | returning lane, resumed by a Claude worker after the first Stage 0 worker was cut off by a model usage limit; the resumed worker verified the on-disk state before continuing |
| Branch / worktree | `codex/pre-1-packed-preprocessing`, `C:/Users/poin/.codex/worktrees/2fb8/RMQ` |
| Base (frozen contract evidence head) | `c1c970b8bfbae03163633365e512d487ae1c98f2` (Lean, scripts and registries identical to contract commit `26d6b5c2b10ed06ae4f72d9075d746ede987bdab`) |
| Commit | the single Stage 0 commit on top of the base; its SHA is reported to the coordinator in the task response (a file cannot contain its own commit SHA) |
| Governance ref | `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; `git diff 0e6a00f -- .agents/skills` empty |
| Governing prompt | `extension-coordination-20260911/claude-coordinator-20260912/PRE1_BUILDER_CONTINUATION.md`, 32,330 bytes, SHA-256 CBB3DC08421F42DBB53AFAD451F3C101925E71E9D328880D9EB229BEA803C76A (verified) |
| Preflight | `scripts/project_skill_preflight.ps1 -GovernanceRef 0e6a00f... -RequiredSkills rmq-proof-sprint -RuntimeProjectSkills "rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint"`: PASS (first worker 6.58 s; resumed worker 5.68 s) |
| Toolchain | `leanprover/lean4:v4.22.0`, `C:/Users/poin/.elan/toolchains/leanprover--lean4---v4.22.0/bin/{lean,lake}.exe` (Lake rejects `-j`; `LEAN_NUM_THREADS=1` on every Lean/Lake process) |
| Host | Windows 11 Pro 10.0.26200, pwsh 7.6.6, Windows PowerShell 5.1.26100.9444; shared with a coordinator aggregate gate and other lanes |

## 2. Changed paths (Stage 0 commit relative to the base)

Modified: `docs/internal/DESIGN_DECISIONS.md` (DD-20260912-PRE1-002),
`docs/internal/WORKFLOW_DESIGN_DECISIONS.md` (WDD-20260912-PRE1-003),
`docs/internal/extensions/pre1/{ACCEPTANCE_MATRIX,AMENDMENTS,ATTACK_TABLE,CONTRACT,REPORT}.md`,
`scripts/gate.ps1` (AMEND-4 only).

Added: `RMQ/Core/WordRAM/Construction/{Program,Calculus,Safety,Structured,Compiler,Loop,ArrayRun,HeaderUse}.lean`;
`scripts/preprocessing_builder_{check.lean,firewall.ps1,gate.ps1,replay.ps1}`,
`scripts/preprocessing_contract_gate.ps1`;
`docs/internal/extensions/pre1/{BUILDER_PLAN.md,BUILDER_REPLAY_DESIGN.md,BUILDER_STAGE_LOG.md,builder_cases.json,builder_manifest.json}`;
`docs/internal/audit_reports/2026-09-12_PRE1_contract_fresh_blind.md`.

Byte-identical to the base (raw SHA-256 of the working files equals the
`c1c970b` blobs): `Primitive.lean` 80120235..., `Input.lean` 78316916...,
`Model.lean` 9d7b3d7e..., `scripts/preprocessing_contract_firewall.ps1`
1f6903d5..., `primitive_manifest.json` a1d31f0b..., `contract_cases.json`
aaec37a6..., `scripts/preprocessing_contract_replay.ps1` b85ff767....
`BUILDER_PLAN.md` equals the coordinator plan (SHA-256 81959334...0BF8) and the
audit copy equals the named report (88,646 bytes, SHA-256 2B35DD03...EA52).
`RMQ.lean`, `lakefile.toml`, shared Packed modules, public aliases, canonical
skills, FAMILY_SUMMARY and DIGESTION_LOG are untouched.

## 3. Amendments as implemented

### AMEND-1 run-level header use (finding P1-1)

Contract text: CONTRACT.md V2-1 (supersedes version-1 lines 64-66, quoted
byte-exact) and AMENDMENTS.md "O-POINTWISE header clause, version 2". Checked
certificate, `RMQ/Core/WordRAM/Construction/HeaderUse.lean` (outside the
operational closure, imports Calculus):

```lean
structure HeaderUse (program : List BInstr) : Prop where
  headerFirst : program[0]? = some headerInstruction
  tailNeverWritesR1 : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i
  wordMissingHeaderFault : ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    (run program fuel { wordInputState width xs with memory := put (encodeInput width xs) 0 none }).final.status = .fault ∧
    (run program fuel { ... }).steps = 1 ∧ (run program fuel { ... }).writes = [] ∧
    (run program fuel { ... }).reserves = [] ∧
    (run program fuel { ... }).final.extent = (wordInputState width xs).extent
  comparisonMissingHeaderFault : ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    -- the same five conjuncts from
    -- { comparisonInputState xs with memory := put (comparisonInputState xs).memory 0 none },
    -- extent compared with (comparisonInputState xs).extent
  wordHeaderReceipt : ∀ (width : Nat) (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (wordInputState width xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running
  comparisonHeaderReceipt : ∀ (xs : List Int) (fuel : Nat), 1 ≤ fuel →
    ∃ t : Transition, (run program fuel (comparisonInputState xs)).transitions[0]? = some t ∧
      t.instruction = headerInstruction ∧ t.before.regs 1 = 0 ∧
      t.after.regs 1 = xs.length ∧ t.after.status = .running
  oracleExtentOne : ∀ xs : List Int, (comparisonInputState xs).extent = 1
```

(The `{ ... }` abbreviations above stand for the same record update written out
in full in the source.) The five run-level fields have default proofs derived
from `headerFirst` through the generic calculus lemmas
`run_missing_header : program[0]? = some headerInstruction → ∀ s, s.pc = 0 → s.status = .running → s.regs 0 = 0 → s.memory 0 = none → ∀ fuel, 1 ≤ fuel → final.status = .fault ∧ steps = 1 ∧ writes = [] ∧ reserves = [] ∧ final.extent = s.extent`
and
`run_header_first : program[0]? = some headerInstruction → ∀ s, s.pc = 0 → s.status = .running → s.regs 0 = 0 → ∀ n, s.memory 0 = some n → 0 < s.extent → ∀ fuel, 1 ≤ fuel → ∃ t, transitions[0]? = some t ∧ t.instruction = headerInstruction ∧ t.before = s ∧ t.after.regs 1 = n ∧ t.after.status = .running ∧ t.after.memory = s.memory ∧ t.after.extent = s.extent`.
`headerUse_of_program (program) (hhead : program[0]? = some headerInstruction) (htail : ∀ i ∈ program.tail, WritesOnly (fun r => r ≠ 1) i) : HeaderUse program`
discharges the certificate of a closed constant from the two decidable facts
(`rfl` and `decide` at the constants, S7/S8). `tail_frame_of_never_writes`
packages the register-1 frame along a run that never returns to pc 0.
Consumer `scripts/preprocessing_builder_check.lean:19-69` restates all seven
fields at full type for every `program`. Replay cases: B04 weaken
`headerFirst` (producer `HeaderUse.lean:62:`), B05 weaken `tailNeverWritesR1`
(consumer `:22:`), B06/B07 weaken the two fault fields (`:36:`, `:54:`),
B08/B09 weaken the two receipts (`:59:`, `:64:`), B10 sibling fact for
`oracleExtentOne` (`:66:`), B11 delete `oracleExtentOne` (`:66:`), B12 comment
control accepts. Toy: `toy_headerUse : HeaderUse [load 1 0, reserve 2, store 2 1, halt 1]`.

### AMEND-2 two constants from one template (finding P1-2, ruling Q1)

Contract text only at Stage 0: CONTRACT.md V2-2 (supersedes version-1 lines
27-28 and 30-31, the latter corrected to "`ProgramContract` fixes the counts
to `Nat` parameters; the typed consumer pins the numerals") and AMENDMENTS.md
"O-UNIF, version 2": `builderProgram` (comparison model, padded
loadKey/loadKey/compareKey leaf, primary C1 constant) and `builderProgramWord`
(word model, add/load/add/load/comparison leaf, finite-key corollary), one
`ProgramContract` instance each with `family` definitionally
`fun _ => <constant>`, `rfl` literal pins on the compiled list, a `rfl`
equal-length/leaf-position theorem, and builder replay cases (i) width/size
parametrization and (ii) each literal numeral changed. None of these
declarations or cases exists yet; they are S7/S8 obligations.

### AMEND-3 positional emitted-cell extraction (finding P1-3)

Contract text: CONTRACT.md V2-3 and AMENDMENTS.md "O-BITS / O-WRITE, version 2".
Implemented vocabulary inside the closure (`Program.lean`):
`def emitted (s : State) (base len : Nat) : List Nat := (List.range len).map fun i => (s.memory (base + i)).getD 0`.
`efficientBuild`/`efficientBuildWord` (as `emitted final outBase (extent - outBase)`
of the accepted runs) are S7 obligations.

### AMEND-4 gate reach and layered firewall (finding P2-1, ruling Q4)

`scripts/gate.ps1` diff (only change to that file): two anchored call sites
`Invoke-Checker -Path "$PSScriptRoot\preprocessing_contract_gate.ps1" -Label 'PRE1-CONTRACT-GATE'`
and
`Invoke-Checker -Path "$PSScriptRoot\preprocessing_builder_gate.ps1" -Label 'PRE1-BUILDER-REPLAY'`
after `eg_cp_final_falsification_replay.ps1`, and roster entries
`'PRE1-CONTRACT-GATE {preprocessing_contract_gate.ps1}'` and
`'PRE1-BUILDER-REPLAY {preprocessing_builder_gate.ps1}'`; static
`$expectedCheckers` count 20 (was 18). `PRE1-CONTRACT-GATE` runs the contract
firewall (120 s, exact PASS line), `lake build RMQ.Core.WordRAM.Construction.Contract`
(900 s) and `lake env lean scripts/preprocessing_contract_check.lean` (300 s,
PASS line), each an owned bounded stage. `PRE1-BUILDER-REPLAY` runs
`scripts/preprocessing_builder_replay.ps1` in full as one owned bounded child
with `-OuterDeadlineSeconds 1800` = 3.48 x the measured full run of 516.8 s
(AMEND-4 requires at least 2x), requiring exit 0 and exactly one
`PRE-BUILDER-REPLAY: PASS mode=full` line. The layered
`scripts/preprocessing_builder_firewall.ps1` runs the unchanged contract guard
and requires its PASS line, checks the exact allowed-imports table of the seven
closure modules (Program: Model; Calculus: Program; Safety: Program;
Structured: Calculus, Safety; Compiler: Structured; Loop: Compiler; ArrayRun:
Program), rejects unregistered `Builder/` files, walks the transitive closure
against {Std, Primitive, Input, Model, closure} and checks
`builder_manifest.json` version 1 (strict UTF-8, CRLF-to-LF normalized SHA-256
per module). The contract guard and `primitive_manifest.json` are
byte-identical to the base. Scope expansion and rationale: WDD-20260912-PRE1-003.

### R1 safety judgment (Safety.lean)

```lean
def State.Fits (W : Nat) (s : State) : Prop :=
  (∀ r, s.regs r < 2 ^ W) ∧ s.pc < 2 ^ W ∧ s.extent < 2 ^ W ∧
    (∀ a v, s.memory a = some v → v < 2 ^ W) ∧ (∀ v, s.status = .halted v → v < 2 ^ W)
def Prim.OperandsFit (W : Nat) (p : Prim) : Prop := ∀ c ∈ p.constants, c.val < 2 ^ W
def Prim.SafeAt (W len : Nat) (s : State) : Prim → Prop
  | .load _ address => s.regs address < s.extent ∧ ∃ v, s.memory (s.regs address) = some v ∧ v < 2 ^ W
  | .constant _ _ | .move _ _ | .comparison _ _ _ _ | .halt _ | .compareKey _ _ _ => True
  | .arithmetic op _ lhs rhs => op.eval (s.regs lhs) (s.regs rhs) < 2 ^ W ∧
      (op = .sub → s.regs rhs ≤ s.regs lhs) ∧ (op = .div ∨ op = .mod → 0 < s.regs rhs) ∧
      (op = .shl ∨ op = .shr → s.regs rhs < W)
  | .jump target | .branchZero _ target => target.val < len
  | .jumpRegister _ => False
  | .store address value => s.regs address < s.extent ∧ s.regs value < 2 ^ W
  | .reserve _ => s.extent + 1 < 2 ^ W
  | .loadKey _ address => ∃ k, s.keys (s.regs address) = some k
def Prim.Safe (W len : Nat) (s : State) (p : Prim) : Prop := p.OperandsFit W ∧ p.SafeAt W len s
def Run.Safe (W : Nat) (program : List BInstr) (r : Run) : Prop :=
  ∀ t ∈ r.transitions, Prim.Safe W program.length t.before t.instruction.primitive ∧ t.after.Fits W
```

(The source writes each `True` arm separately.) `Prim.safe_not_fault : Prim.Safe W len s p → s.status ≠ .fault → (execPrim p s).status ≠ .fault`;
`Prim.safe_fits : s.Fits W → Prim.Safe W len s p → s.pc < len → len < 2 ^ W → (execPrim p s).Fits W`;
`Run.Safe.of_transitions : program.length < 2 ^ W → s.Fits W → (∀ t ∈ (run program fuel s).transitions, Prim.Safe W program.length t.before t.instruction.primitive) → Run.Safe W program (run program fuel s)`;
`Run.Safe.not_fault`, `Run.Safe.final_fits` (Compiler.lean).

### R2, R3, R4

R2: the builder runner's `Test-CaseVerdict` requires, for a consumer
rejection, `Test-LineSetEquality` between the set of failing consumer lines and
the registered set; firewall and producer rejections pin one diagnostic line or
location. R3: CONTRACT.md V2-5; the closure imports no Controls/Contract/
Conservative module (firewall-checked) and operates on `List BInstr`. R4:
ATTACK_TABLE.md "Version 2 corrections": FK-1's basis is run identity
(REQ-PRE-EXACT/REQ-PRE-MACHINE, INV-TRACE-EXECUTION, INV-NO-SYNTHETIC), FK-5's
cheap fixed-table variant is counted code.

## 4. Operational foundations (checked theorem types)

Closure modules (namespace `RMQ.SuccinctFinal.PackedConstruction`; each imports
only the frozen roots and earlier closure modules):

- Program.lean: `Transition` (before, instruction, after); `fetch`; `stepProgram`
  (fetch, then `checkedStep`); `run : List BInstr → Nat → State → Run`;
  `Run.steps := transitions.length`; `Run.categories`, `categoryCount`;
  `Transition.write?` (successful store only, address and value from the
  pre-state), `reserve?`, `load?`, `keyRead?`; `Run.writes/reserves/loads/keyReads`
  as `filterMap`; `Run.result`; `emitted`; `Prim.destination?`; `WritesOnly`
  with a `Decidable` instance; `execPrim_frame`.
- Calculus.lean: `run_add`, `RunsTo` with `refl/trans/of_step/instruction/steps`,
  `RunsTo.fuel_extension : RunsTo program s s' ts → s'.status ≠ .running → ∀ extra, run program (ts.length + extra) s = ⟨s', ts⟩`,
  `run_steps_le_fuel`,
  `Run.steps_partition : ∀ r : Run, r.steps = r.categoryCount .read + ... + r.categoryCount .oracleComparison` (ten categories),
  `run_transition_spec`, `run_write_at` and `run_load_at` (positional provenance at
  transition index `k`: `t.before = (run program k s).final`, fetched
  instruction, arm-specific memory/register facts; exact types in
  ACCEPTANCE_MATRIX.md Stage 0 rows and consumer lines 96-123),
  `run_extent_mono`, `run_cleanTail : CleanTail s → CleanTail (run program fuel s).final`,
  `run_frame : (∀ i ∈ program, WritesOnly allowed i) → ∀ r, ¬ allowed r → (run program fuel s).final.regs r = s.regs r`,
  `writes_replay : (run program fuel s).final.memory = (run program fuel s).writes.foldl (fun m e => put m e.1 (some e.2)) s.memory`,
  `State.Agree` (regs, extent, keyRegs, pc, status), `TransitionsAgree`, `Run.Agree`,
  `run_agree_of_reads` (fine form: agreement on loaded addresses and read keys),
  `run_agree_of_supplied` (coarse form under `CleanTail` on both states, also
  concluding `s'.memory = s.memory`), `Run.Agree.{steps,categories,writes,reserves,result}`,
  `run_missing_header`, `run_header_first`.
- Safety.lean: section 3 (R1).
- Structured.lean (namespace `...PackedConstruction.Structured`): `Action` (nine
  non-control constructors) with `Action.prim`; `Block := skip | action | exit | seq | ifZero | loop`;
  `Block.size`; `fin`; `Block.compileAt` (loop = forward `branchZero` past the
  body, body, backward `jump`); `Block.WritesOnly`;
  `inductive EvalG (P : State → Action → Prop) : Block → State → State → Nat → Prop`
  with exact costs (action 1, exit 1, ifZero taken k+1, fallthrough k+2 or k+1
  if stopped, loop exit 1, loop step k₁+k₂+2, loop stopped k₁+1, stopped
  states identities of cost 0); `Eval := EvalG (fun _ _ => True)`;
  `SafeEval W := EvalG (Action.Safe W)` with `Action.Safe W s op := Prim.Safe W 0 s op.prim`;
  executable `evalF` with `evalF_sound : evalF fuel b s = some (s', k) → Eval b s s' k`.
- Compiler.lean: `HostedAt program base code := ∀ i < code.length, program[base + i]? = code[i]?`;
  `EvalG.compile_realizes` (type in ACCEPTANCE_MATRIX.md, REQ-PRE-MACHINE row:
  exact transition count `ts.length = k`, `PcAgree s'' s'`, running result at
  `base + b.size`, every transition classified by `TransitionShape`);
  `SafeEval.compile_safe : 32 ≤ W → program.length < 2 ^ W → SafeEval W b s s' k → HostedAt program base (b.compileAt base) → base + b.size < 2 ^ 32 → base + b.size < program.length → ({ s with pc := base }).Fits W → ∃ s'' ts, RunsTo program { s with pc := base } s'' ts ∧ ts.length = k ∧ s'' = { s' with pc := s''.pc } ∧ (s''.status = .running → s''.pc = base + b.size) ∧ Run.Safe W program (run program ts.length { s with pc := base }) ∧ s''.Fits W`;
  `Block.compile_writesOnly`, `Block.compile_length`.
- Loop.lean: `EvalG.loop_iterate`, `EvalG.loop_iterate_potential(_cost)`,
  `EvalG.loop_measure(')` (types in consumer lines 245-271).
- ArrayRun.lean: `ExecState` (registers, memory, keys and key registers as
  arrays), `ExecState.abstract`, `Prim.RegistersBelow`, `execPrimArray`,
  `runArray` (fuel recursion, events accumulated without per-transition state
  copies),
  `runArray_abstract : (∀ i ∈ program, i.primitive.RegistersBelow R) → es.regs.size = R → es.keyRegs.size = R → steps, categories, writes, reserves and result of runArray program.toArray fuel es equal those of run program fuel es.abstract ∧ final.abstract = (run program fuel es.abstract).final`,
  `ExecState.ofWordInput_abstract : (ExecState.ofWordInput R width xs).abstract = wordInputState width xs`,
  `ExecState.ofComparisonInput_abstract`, `ExecState.abstract_cleanTail`.

Typed consumer `scripts/preprocessing_builder_check.lean` restates every exit
theorem at an independently written full type, pins the toy program on the
mathematical run by `decide` (`toy_run`: steps 4, categories
`[.read, .allocation, .write, .control]`, extent 3, writes `[(2, 1)]`, reserves
`[2]`, result `some 1`; `toy_missing_header`: fault after 1 step), proves
`countdown_cost` (exact `4 * k + 1`), checks the array evaluator by `#guard`
(steps 1/5/29 at k = 0/1/7, final registers `#[0, 28, 1, 0]`, toy writes
`[(2, 1)]` from `ExecState.ofWordInput 4 40 [3]`) and prints 25 axiom
inventories. Observed inventory (baseline consumer stage of the full builder
replay and again inside the isolated builder-gate run): every printed set is a
subset of {propext, Classical.choice, Quot.sound}; `run_write_at`,
`run_load_at`, `writes_replay`, `run_frame`, `RunsTo.fuel_extension`,
`Prim.safe_not_fault`, `evalF_sound`, `toy_run` use only `propext`;
`EvalG.loop_measure`, `runArray_abstract`, `ExecState.ofWordInput_abstract`,
`countdown_cost` use all three.

## 5. Replay results

| Replay | Mode | Result | Duration | Identity |
| --- | --- | --- | --- | --- |
| Contract (regression) | full, 18-case registry v1 | PASS, executed = expected = 18 (C01..C18 in order), 198 stages, 28 self-tests (7 registry, 9 matcher, 9 selector, 3 deadline), every case at its frozen stage/line, restoration EXACT, baseline = restored Git head/status/worktree/index | 557.7 s (06:24:41Z-06:33:59Z 2026-09-13) | registry `aaec37a62bc74b483d09362a5d16f62afc2ae3a7be007577bc13e4c87c98574e` and runner `b85ff767098d3a3249a86b78d2e9e96e63d7822dd82a3752fac933479cf5424c` unchanged; evidence `.lake/preprocessing-contract-replay/20260912-232443-94634936f26c4d4d9fc9647ea720e9b5` |
| Builder | `-StartupOnly` | PASS, 11 stages | 34.8 s | runner `a5cf0b4abab4ed1db57094505292ec88352b38d26ce5684997e2ed8c525c63b4`, registry `fdfcbb189438974f63390733f0da079cc3eba7e59fb045dda1912038a7685658` |
| Builder | `-OnlyCase B06_WORD_MISSING_WEAKEN` | PASS, executed 1, consumer `:36:`, restoration EXACT | 81.7 s | same |
| Builder | full, registry v1 (13 cases) | PASS, executed = expected = 13 (B01..B13), 145 stages, 44 self-tests (32 registry/matcher, 9 selector, 3 process), every case restoration EXACT, no stage timed out | 516.8 s | same; the 21 recorded source hashes equal the Stage 0 bytes; evidence `.lake/preprocessing-builder-replay/20260912-222805-1503b7b95df0437092e1528cde924a47` |
| Builder | Windows PowerShell 5.1: `-RegistrySelfTestOnly`, `-SelectorBoundarySelfTestOnly` | PASS (32), PASS (9) | 0.7 s, 19.4 s | same |

Builder case surfaces (full run): B01 firewall `imports rejected: .../Program.lean`;
B02 firewall `frozen closure bytes changed: .../Program.lean`; B03 firewall
`contract guard failed: PRE1-FIREWALL imports rejected: .../Primitive.lean`;
B04 producer `HeaderUse.lean:62:`; B05-B11 consumer lines 22, 36, 54, 59, 64,
66, 66; B12 accept; B13 consumer line 84.

The full builder replay was not rerun standalone: no replay-relevant file
changed after it (the only later script edit is the gate checker's measured
deadline, which the replay does not read or hash). The isolated
`PRE1-BUILDER-REPLAY` checker run below necessarily executed the full builder
replay once more; that is the checker's own acceptance purpose (AMEND-4), not a
duplicate standalone run.

## 6. Gate checker results (isolated; `scripts/gate.ps1` itself was not run)

| Checker | Invocation | Result | Duration |
| --- | --- | --- | --- |
| PRE1-CONTRACT-GATE | subprocess, `-LakePath` pinned Lake (PATH `lake` on this host is the elan proxy) | exit 0; firewall 2.955 s, producer 1.574 s (warm), consumer 4.345 s; `PRE1-CONTRACT-GATE PASS` | 11.83 s |
| PRE1-CONTRACT-GATE | in-process `Invoke-Checker` mimic (no parameters; pinned bin first on PATH, as the coordinator gate driver requires) | `threw=none lastExitCode=0`; `PRE1-CONTRACT-GATE PASS` | 12.46 s |
| PRE1-BUILDER-REPLAY | in-process `Invoke-Checker` mimic (no parameters), under the heavy-verification mutex | `threw=none lastExitCode=0`; `PRE-BUILDER-REPLAY: PASS mode=full executed=13 registry=13`, `PRE1-BUILDER-REPLAY PASS`; replay evidence `.lake/preprocessing-builder-replay/20260912-233625-96ca6b0d1c4d408da0fada481e7fc51b` (same runner, registry and 21 source hashes as the first full run; executed = expected B01..B13; 145 stages; 44 self-tests; every case at its registered surface with restoration EXACT; same 25 axiom inventories) | 633.1 s replay child (checker-measured), 637.2 s including the harness; 1800 s is 2.84x this second measurement |

Roster: `$expectedCheckers` lists 20 entries (static count). The
`GATE COVERAGE: 20 of 20` line is produced only by an aggregate run, which is
coordinator-scheduled on the frozen final candidate.

## 7. Checks on the Stage 0 tree

| Check | Role / rows | Command (see list below) | Duration | Outcome |
| --- | --- | --- | --- | --- |
| Frozen matrix byte integrity | final-required; all 31 IDs | K1 | < 1 s | PASS: LF-normalized candidate starts with the exact `c1c970b` blob (38,845 bytes); 31/31 IDs occur exactly once as a table row and once as a `###` section, each row byte-identical to the base; 0 missing or duplicate IDs; exactly one `S0 / <ID>` evidence row per ID; no mojibake spellings |
| Frozen contract surfaces | non-goal guard | K2 | < 1 s | PASS: 7/7 raw SHA-256 identical to the base blobs |
| Trust hygiene | final-required | K3 | < 1 s | exit 1, no matches |
| Native-decision scan | final-required | K4 | < 1 s | exit 1, no matches |
| Axiom inventories | Stage 0 required | K5 | 7.2-7.3 s per consumer stage | 25 inventories, union {propext, Classical.choice, Quot.sound} |
| Script parse | Stage 0 required (5.1 parse) | K6 | 1.3 s / 1.9 s | 0 errors on both hosts |
| Whitespace | final-required | K7 | < 1 s each | exit 0, no output (working tree and index, on the staged Stage 0 tree) |
| Design-decision policy | final-required | K8 | 2.45 s | exit 0, `DESIGN-CHECK: checked 27 changed files (9 code, 16 workflow, 3 neutral)` |

Commands:

- K1: Python over `git cat-file blob c1c970b:docs/internal/extensions/pre1/ACCEPTANCE_MATRIX.md`
  and the candidate file (strict UTF-8, CRLF-to-LF, prefix and per-ID row and
  section extraction).
- K2: raw SHA-256 of `Primitive.lean`, `Input.lean`, `Model.lean`,
  `scripts/preprocessing_contract_firewall.ps1`, `primitive_manifest.json`,
  `contract_cases.json`, `scripts/preprocessing_contract_replay.ps1` against
  `git cat-file blob c1c970b:<path>`.
- K3: `rg -n "\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\b|import Mathlib" RMQ lakefile.toml`
- K4: `rg -n "native_decide|Lean\.ofReduceBool" RMQ` (also run over
  `RMQ/Core/WordRAM/Construction` and both `scripts/preprocessing_*_check.lean`
  files together with the K3 pattern: exit 1)
- K5: the `#print axioms` block of `scripts/preprocessing_builder_check.lean`,
  as printed by the baseline consumer stage of both full builder replays
- K6: `[System.Management.Automation.Language.Parser]::ParseFile` over
  `scripts/preprocessing_{builder_gate,contract_gate,builder_replay,builder_firewall}.ps1`
  and `scripts/gate.ps1` under Windows PowerShell 5.1.26100.9444 and pwsh 7.6.6
- K7: `git diff --check` and `git diff --cached --check` with every owned path staged
- K8: `pwsh -NoLogo -NoProfile -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base c1c970b8bfbae03163633365e512d487ae1c98f2` on the staged tree (the script also reads working-tree and untracked changes; none were outside the staged set)

After the commit the worker also runs `git diff --check c1c970b8bfbae03163633365e512d487ae1c98f2..HEAD`
and the strict design check on the committed range; those outcomes are
reported in the task response because they postdate this file.

## 8. Heavy commands (one Lean/Lake process at a time in this tree)

| Command | Deadline | Duration | Exit |
| --- | --- | --- | --- |
| first worker: focused `lake build` of Program, Calculus, Safety, Structured, Loop/ArrayRun/HeaderUse (with Compiler), Loop, HeaderUse | 600 s each | 4.6-36.1 s | 0 |
| first worker: `lake env lean scripts/preprocessing_builder_check.lean` | 600 s | 9.89 s, 6.99 s | 0 |
| first worker: builder replay full | 600 s per stage | 516.8 s | 0 |
| `lake build ...Loop ...ArrayRun ...HeaderUse` (cache check) | 900 s | 0.34 s | 0 |
| contract replay full | outer 2400 s; stages 300/60/12 s | 557.7 s | 0 |
| `preprocessing_contract_gate.ps1` (twice) | 120/900/300 s | 11.83 s, 12.46 s | 0, 0 |
| `preprocessing_builder_gate.ps1` via harness | outer 2400 s; checker 1800 s | 637.2 s | 0 |

Launch errors recorded, not semantic runs: two scratch-wrapper argument-binding
errors (no child started) and one Git Bash MSYS path conversion of the
`-LakePath` value that stopped the contract replay at its `PRE-TOOLCHAIN`
preflight before any stage (`.lake/preprocessing-contract-replay/20260912-232424-c1cf0f5710e54c6c87379f4263c22ed2`).
Retained development failures of the first worker: two
`-RegistrySelfTestOnly` runs of an earlier runner (`Index was outside the
bounds of the array.`). Full per-command ledger: BUILDER_STAGE_LOG.md.

## 9. Unexecuted checks and limits

- `scripts/gate.ps1` aggregate: not run (coordinator-owned). The 20-of-20
  coverage line is therefore not observed.
- POSIX/WSL branch of the owned-process tooling: not executed on this host
  (both runners record it as uncovered). The CI Ubuntu job will be the first
  POSIX execution of the two new checkers.
- Full builder replay under Windows PowerShell 5.1: not run (registry and
  selector self-tests and a parse of all new scripts only).
- Default `lake build`, `lake build rmq_preprocessing_validate`, claim-drift
  scan: not applicable at Stage 0 (no root import, no executable, no
  FAMILY_SUMMARY/DIGESTION_LOG entry yet).
- Cold builds were not remeasured in this session (warm cache).
- B04 (weaken `HeaderUse.headerFirst`) is rejected at the producer
  (`HeaderUse.lean:62:`), because the derived defaults need the field, not at a
  consumer line; the other field cases reach the consumer.
- `headerUse_of_program` initializes the two syntactic fields with
  `first | exact h | trivial`; the `trivial` branch cannot fire on the real
  field types and exists so weakening mutations reach the consumer.
- A registry case mutating a closure module always stops at the manifest hash
  surface; semantic producer-stage mutations of closure modules need a
  registry-driven manifest re-hash in a later stage (WDD-20260912-PRE1-003).
- `toy_run` and `toy_missing_header` evaluate a four-transition toy run in the
  kernel by `decide`, as the plan's S0 exit requires; ruling Q9's ban on kernel
  evaluation concerns builder machine runs. Flagged for the coordinator.
- `SafeEval.compile_safe` takes `base + b.size < 2 ^ 32` and
  `base + b.size < program.length` as explicit hypotheses; the program-level
  facts discharging them are S8.
- AMEND-1 (a)/(b) at `builderProgram`/`builderProgramWord`, all of AMEND-2's
  declarations and replay cases (i)/(ii), AMEND-3's `efficientBuild`, and the
  Q3 relocation non-claim in Capstone.lean comments are future obligations.
- Nothing about `buildMemory`, linear work, workspace or the query join is
  claimed.

## 10. Proof digestion

What changed conceptually. The contract phase fixed what one primitive step
may do; Stage 0 fixes how a whole program runs and how later stages will
reason about it. A run is now a list of recorded transitions, each with its
real pre-state and fetched instruction, so work, writes, reservations, reads
and categories are all projections of one object rather than separately
supplied numbers. Structured blocks (sequence, zero test, top-tested loop)
compile to that interpreter with an exact transition count, and a single
per-transition safety judgment carries every width, address, divisor and shift
obligation. The header-use certificate turns "the program reads the length
from cell 0" from prose into seven checked fields.

Plain English. Before writing the preprocessing program, we built and checked
the ruler it will be measured with: a step counter that cannot be faked, a
compiler from readable loops to primitive instructions that preserves the exact
step count, one safety rule that later proofs must use everywhere, and a
certificate that any accepted builder really loads the input length from the
header and faults immediately without it.

Live assumptions. Functional indexed state (no Lean-runtime claim); fuel is a
termination device only; the frozen ISA with unbounded-`Nat` arithmetic, made
word-sized only through `Prim.Safe`; compiled code must fit below `2^32`
program-counter values; the array evaluator is related to the mathematical run
by `runArray_abstract` under register-bound and array-size premises.

Named downstream consumers. `efficientBuild_eq_buildMemory`,
`efficientBuildWord_eq_buildMemory` and `constructionAndQueryCapstone_holds`
(none exist yet) will be assembled from `SafeEval`/`EvalG` stage facts through
`SafeEval.compile_safe` and the loop rules, with `HeaderUse builderProgram` and
`HeaderUse builderProgramWord` discharged by `headerUse_of_program`.

What a skeptical graduate student would ask next. "Your compiler theorem
needs the block to fit below 2^32 and to be followed by an instruction, and
your safety rule is stated per transition. When the real builder is a few
thousand instructions with data-dependent loops, can you still prove each loop
body's cost is a literal constant independent of n, and does `Run.Safe` at
`wordWidth n` actually hold for the input sizes where `wordWidth n` is
smallest?" A second: "the missing-header weakening fails at the producer, not
the consumer; is `headerFirst` really load-bearing at the consumer?" (It is
projected at consumer line 20, and every run-level field is derived from it.)

## 11. Next

The coordinator commissions the PRE-1-A1 continuation audit on the Stage 0
commit. While it runs, only S1 (machine-free pure specification, outside the
firewall, no builder program text) is permitted; S2-S8 wait for the
coordinator's authorization. No aggregate slot is requested at this phase.

# PRE-1-R1 claim-scan evidence repair (appended 2026-09-14)

Appended after the last line of the PRE-1 report; nothing above changed except
lines 245 and 246, which now state the quoted scanner summaries (11 hits and 0
strict failures; 2047 hits) in prose with the same integers. The repair worker's
status and evidence are in `repair-r1/REPORT.md`, its frozen contract in
`repair-r1/ACCEPTANCE_MATRIX.md`, and the command rows R1-1 onward in
BUILDER_STAGE_LOG.md. In short: the byte-exact PRE-1-A1 contract audit report
now lives as `evidence/audit-archive/2026-09-12_PRE1_contract_fresh_blind.md.gz`
and `evidence/author-final-checks-summary.json` as its own path plus `.gz`, both
decompressing to their base blobs; the unchanged scanner's self-test and strict
scans pass on the repaired commit; no Lean source, script, registry, manifest,
contract text or frozen row changed. The PRE-1 status above is unchanged; the
coordinator aggregate gate, the audit disposition and acceptance remain open.

# PRE-1-R2 builder consumer markers and controls (appended 2026-09-17)

Appended after the last line of the PRE-1 report and the PRE-1-R1 section; nothing above changed. The repair worker's frozen contract is `repair-r2/ACCEPTANCE_MATRIX.md` (frozen in `9e06fe77fd06bc537c48260f1b056fe46593b0d1`), its command rows are R2-1 onward in BUILDER_STAGE_LOG.md, and its receipts are under `repair-r2/receipts/`. Fresh blind audit PRE-1-A2 of `84ae12f` found (P1-1) a gate hygiene hit in the capstone consumer's docstring, (P2-1) typed consumers printing their PASS markers while failing, (P2-2) a `work` field that holds for every program with no case weakening `halts`, (P3-1) the unrecorded placement of the `Cw`/`Dw` cases, (P3-2) four stale places in BUILDER_REPLAY_DESIGN.md and (P3-4) no case mutating `Run.Safe`. The repair is committed in `341bc2803dc26a123c48b1b8d0566e5e1583de7a` on the verified PRE-1-R1 tip `a0c93e9` and verified on the receipt chain that follows it (`c33f2a8`, `e935f84`, `26b175e`, `f5d6128`, `ec9303a`, `9598f72` and the closing commit change only `docs/internal/`; `f7bdf20` raises the builder gate checker's deadline under coordinator ruling R-R2-1). In short: the capstone docstring is reworded in place (lines 11-12, line count unchanged, both gate hygiene commands print nothing); every PRE-1 typed consumer (builder, capstone, contract, spec, stage) prints its marker if and only if the whole file elaborated with no error-severity message and its witness and guard conditions hold, by re-elaborating its own source text in-process with the marker command blanked and reading every command's message log (Lean 4.22 resets the command message log before each command, so a later command cannot otherwise see an earlier error), established by the committed control matrix on all five consumers; the builder replay registry is version 2 (55 cases, content pin `3e27e762...` replacing `0bc1fba4...`), its runner additionally requires the profile's marker to be absent from every consumer-stage rejection (B16, B17 and B18 are regression controls), and B53 (`halts` weakened to a proposition every program satisfies at fuel 0 without the halted status), B54 (`halts` at a larger literal fuel) and B55 (`Run.Safe` at `program.length + 1`) are registered and rejected at the capstone lines 227 and 349 and the builder-consumer line 457 in the complete 55-case replay; CONTRACT.md V3-7a/V3-10a and AMENDMENTS.md record the `Cw`/`Dw` placement and the marker refinement; BUILDER_REPLAY_DESIGN.md is corrected; the complete contract replay, the validator, the firewall and the self-tests on both hosts pass on the tip.

Reading of finding P2-2, recorded here as REQ-PRE-R2-HALTS requires. `BuilderRunFacts.work` states `(run program (builderBudget xs.length) s0).steps ≤ 1000000000 * xs.length + 1000000000`, and `builderBudget n = 1000000000 + 1000000000 * n`, so the literal is the fuel itself; since a run of `fuel` steps has at most `fuel` steps (`run_steps_le_fuel`), the `work` field holds for every program and every state, the empty program included (`repair-r2/tools/p2_2_work_probe.lean`, rerun on the tip: `work_literal_is_fuel`, `empty_program_work`, and `empty_program_never_halts` showing the empty program fails `halts`). `work` is therefore fuel-trivial and is not by itself a linear-work theorem. The linear-work content of REQ-PRE-COST is `halts` together with `work` at the pinned linear fuel: `halts` says the run at fuel `builderBudget xs.length` reaches `.halted outBase`, and with fuel insensitivity that is exactly the statement that the executed run halts within `C * n + D` interpreter transitions, which the capstone consumer pins at lines 227 and 349 (`check_comparisonRun_halts`, `check_wordRun_halts`) with the fuel body pinned by B33 and B34. Registry version 2 makes that content load-bearing under mutation: B53 and B54 are rejected at exactly those two lines while their producers build, whereas B45 (which weakens only `work`) remains the control for the fuel literal.

Two records for the coordinator. First, the second worker session's runtime refused to create the durable worker record `repair-r2/REPORT.md` (its file tool rejects report files for subagents), so that record's content is delivered in the submission message for the coordinator to persist; the matrix evidence appendix, the receipts, the ledger entries and this section carry the same evidence. Second, the measured durations of the builder-consumer and capstone-consumer stages before and after the repair, on one build and host, are 3.46 s and 10.95 s (builder) and 56.09 s and 120.58 s (capstone); the complete builder replay measured 8674.82 s, so the gate checker's deadline is 23,400 s (`f7bdf20`).

The PRE-1 status above is unchanged; the continuation audit, the coordinator aggregate gate and acceptance remain open.
