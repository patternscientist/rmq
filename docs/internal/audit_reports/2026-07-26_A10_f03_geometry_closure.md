# (A10) EG-CP-F03 geometry-closure fresh-blind audit

## 1. Scope and audit mode

- Auditor: A10.
- Mode: FRESH BLIND DELTA, report-only.
- Base: d09bed78185d2b13c36a29b018bb9544176a714c.
- Target: 6be9e5532d90412db74506a658c3393175f6e6f7. The prescribed rev-parse matched it exactly.
- Audited commits: db43b25, d988166, and 6be9e55.
- Frozen acceptance object: EG-CP-F03-GEOMETRY-CLOSURE at docs/internal/RMQ_ENDGAME_ROADMAP.md:374, including the Day-0 amendment at :384 and model contract at :300-363.

I did not use prior audit verdicts, coordinator chat, or worker reports as evidence. I inspected each of the five conclusion-bearing Markdown deltas (the three E1 records and the two decision logs) as a claim source. The 320-file f03_evidence directory was checked for imports, build targeting, and citations; its README declares its individual working artifacts unvetted, so I did not promote them to evidence. Target Git blob IDs, rather than working-tree hashes, are:

- GeometryClosure.lean: 88e251bf821bcd6b0892b3119f3bffb7d57394b2.
- RMQ.lean: 91b2ad8a6e09cc6432be5e4a62471c4561f9484b.
- RMQ_ENDGAME_ROADMAP.md: bb15bc9ed5fd12c416242d0bb9f617e49b4fbce7.
- E1_ENDGAME_F03_CLOSURE_RESULT.md: 7f1c5afc0eef2074ef2a60eb180f6c67e5f16a99.

### Project-skill preflight

The explicit no-role preflight ran first. Exact output:

~~~text
SKILL-PREFLIGHT: governance=6be9e5532d90412db74506a658c3393175f6e6f7
SKILL-PREFLIGHT: checkout=6be9e5532d90412db74506a658c3393175f6e6f7
SKILL-PREFLIGHT: expected=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: checkout_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: working_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: runtime_skills=rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint
SKILL-PREFLIGHT: required=<none>
SKILL-PREFLIGHT: required_mode=explicit-no-role
SKILL-PREFLIGHT: PASS
~~~

The platform lacked pwsh, so the same prescribed script succeeded through PowerShell with ExecutionPolicy Bypass. A harmless global-Git-ignore permission warning followed it.

## 2. Verdict on EG-CP-F03

| Question | Verdict | Reason |
|---|---|---|
| Letter of the frozen row | **NOT CLOSED** | The row requires a checked exhaustive typed inventory for every current logical-read source and universal consumers. The only inventory working files are expressly unvetted and excluded from acceptance; no eligible artifact or owner amendment replaces the requirement. |
| Spirit of the frozen row | **NOT CLOSED** | The new proof is a meaningful shared-supplied-store congruence, but does not connect its whole ReadStore parameter to memory xs, separately account for header words, or establish sequential prior-probe discipline. |
| Checked obstruction | **Not established** | The proof is positive kernel evidence against a content-dependent variation of the supplied-store evaluator. It does not establish an unreconstructable route-controlling value over frozen objects and quantifiers. |

This does not reject T4_wholeQuery_trace_size_only as a Lean theorem. It rejects using that theorem alone as acceptance evidence for this frozen row.

## 3. Findings

### P1 — A10-F03-01: the required inventory-and-consumer artifact is absent

Roadmap line 374 gives this minimum evidence:

> Exhaustive typed inventory for every current logical-read source and universal consumers, not representative rows.

Line 384 makes F03 the exhaustive-and-universal requirement and directs that inventory to completion, or to a named non-derivable value, before broad later work. The target has no checked exhaustive typed inventory of every current logical-read source and no eligible artifact mapping those sources to universal consumers. The working inventory files below f03_evidence are expressly unvetted, excluded from acceptance, and described by the campaign as refuted/incomplete.

The strongest new theorem materially says:

~~~lean
For equal-size Cartesian shapes, every shared WordRAM.ReadStore, and
all endpoints, the two supplied-store whole-query TraceResults are equal.
~~~

That is strong extensional evidence, but it does not enumerate every local offset, length, branch, divisor, or selector. The proposed contraposition cannot prove that structural enumeration: a local content-dependent calculation can be dead, cancel before an observed trace event, or otherwise be observationally masked. Equal final traces for all shared stores do not establish a typed source inventory or prove each intermediate calculation factors through permitted inputs.

The target result document concedes at E1_ENDGAME_F03_CLOSURE_RESULT.md:88-93 that no inventory artifact exists. The campaign document records the missing universal-consumer inventory at E1_ENDGAME_F03_GEOMETRY_CLOSURE_CAMPAIGN.md:23-28. Those are process disclosures only; the finding follows from the frozen row and absent artifact.

Evidence tier: T4 is Tier 1 kernel evidence for its actual proposition; the absent artifact is a Tier 4 repository-surface fact; decision prose is Tier 5 only.

### P1 — A10-F03-02: shipped scope language exceeds the theorem and conflicts internally

GeometryClosure.lean:9-13 presents the module as settling the entire row and describes allowed inputs without naming its shared arbitrary store parameter or header words. DESIGN_DECISIONS.md:5096-5110 likewise chooses the capstone instead of the inventory. Those assertions conflict with the same delta's reservation that the substitution is an owner decision at :5121-5127 and with WORKFLOW_DESIGN_DECISIONS.md:6453-6456, which explicitly retains the row as open.

The actual theorem requires both executions to receive the same whole WordRAM.ReadStore. It does not state a header-word interface or an ordered prefix of previously returned replies. The accurate supplied-store caveat at GeometryClosure.lean:34-37 comes after the stronger source headline and does not repair it. This is a document-scope overstatement under the audit rejection condition, not a defect in the Lean proof.

Evidence tier: Tier 1 for the actual theorem type; Tier 5 for the inconsistent claims. Severity is P1 because a shipped document presents broader acceptance scope than its load-bearing proposition supports.

### P2 — A10-F03-03: the supplied-store theorem is not yet the frozen dependency model

The model contract at RMQ_ENDGAME_ROADMAP.md:327-338 says a closed packed controller has dynamic inputs exactly n, endpoints, and contents returned by prior probes into memory xs. The actual store-free public route is SuccinctClassic.queryTraceResult at SuccinctRMQClassic.lean:191-197. The theorem targets queryTraceResultWithStore at :199-207, which takes an unrestricted whole WordRAM.ReadStore.

SuccinctFinalStoreParam.lean:202-209 has a private locality predicate, but the new public theorems neither export a sequential prior-reply invariant nor bind their store to memory xs. The result proves the useful conditional statement “with one shared supplied store,” not the frozen statement that all dynamic dependence is through preceding probes of one packed memory.

The fence is real. An independent executable control found equal-length lists [3,1,2,0] and [0,2,1,3] with store-free trace and cost lengths 55 and 52. With a deliberately shared supplied store, the public theorem applies; it does not apply to separately generated stores.

Evidence tier: Tier 2 model-surface theorem and Tier 3 independent executable control. This is a missing composition result, not a counterexample to T4.

### P2 — A10-F03-04: header words are neither typed nor separately accounted for

The command below returned no matches:

~~~text
rg -n -i "header" RMQ/Core/SuccinctFinal/RAM/GeometryClosure.lean
~~~

The frozen row explicitly names header words as permitted inputs. F01/F02 own schema and counted consumption, but treating headers as an undifferentiated part of ReadStore does not prove which header words exist, how they are read, or that they are the only non-probe metadata consumed. The result document records this omission at E1_ENDGAME_F03_CLOSURE_RESULT.md:165-169.

F01/F02 jurisdiction does not erase F03's own input language. It allows deferral of the schema, not declaration that an untyped store parameter completes F03.

Evidence tier: Tier 4 source-surface fact and Tier 5 disclosure.

### P0 and P3

No P0 trust failure was found. No separate P3 finding is needed: unpinned event-count anecdotes were not used for the verdict.

## 4. Positive evidence independently reproduced

### Actual route, evaluator, and leaf coverage

Definition expansion confirms the intended controller rather than a sibling:

1. SuccinctFinalRAM.lean:4356-4364 defines five instructions: two select-close calls, LCA-close, guarded rank-close, and guarded output.
2. SuccinctFinalStoreParam.lean:2058-2091 evaluates four instruction constructors with a supplied store; :2302-2311 recursively evaluates the program.
3. SuccinctRMQClassic.lean:199-207 is the public supplied-store entry. The sibling at :191-197 is the store-free route.
4. wholeQueryInstr_congr at GeometryClosure.lean:1209-1238 case-splits every constructor, and wholeQueryProgram_congr at :1245-1261 is universal over every program and start state.

All three shape-consuming leaves are covered without a size threshold:

- L1: SelectLeaf.L1_route_shape_size_only at :287-306.
- L2: L2_route_size_only at :1182-1198; L2_lcaClose_size_only at :1105-1124 handles the dispatcher.
- L3: L3_rankClose_size_only at :1170-1179.

The dispatcher is the real one: ChargedFringeWiring.lean:487-503 branches on blockOfClose equality, calls the same-block arm at :498-499 and cross-block arm at :501-503. The proof uses by_cases on that predicate and supplies equality for each arm.

Evidence tier: Tier 1 for compiled definitions and kernel theorems, Tier 2 for the supplied-store model surface.

### Anti-vacuity scratch controls

All scratch files were outside the repository.

- A10_RflMustFail.lean deliberately exited 1 with fifteen rfl-failed errors after dropping the size/length premise from L1, L2, L3, validRange_congr, instruction/program congruence, both T4 forms, public trace/footprint/cost and factorization forms, offsets_congr, and interiorRangeMinComputation_congr.
- A10_NoGenericUnification.lean deliberately exited 1: rfl cannot construct a.size = b.size for arbitrary shapes. A separate control applies T4 at explicitly different equal-size shapes, rather than identifying the two sides.
- A10_GeometryProbe.lean compiled. It proves node (node empty empty) empty and node empty (node empty empty) have equal size 2 and different bpCode. It also proves [3,1,2,0] and [0,2,1,3] have equal length but different Cartesian shapes. T4 and the public supplied-store theorem typecheck at those off-diagonal pairs.
- The executed footprint is nonempty, endpoint-sensitive, and store-sensitive. With the first list and its canonical store, endpoints (0,2) give trace/footprint length 55 and (0,3) give 71. Replacing that store by an all-none store gives 8 and changes the value from some 1 to none.
- At n = 10, blockOfClose gives (1,3) blocks (0,0) and (1,17) blocks (0,2). Scratch applications of L2_route_size_only compiled at both. Direct L2 trace lengths were nonzero on both arms: 12/29 with the empty store and 13/47 with the canonical store.

Evidence tier: equalities and theorem applications are Tier 1; executable trace measurements are Tier 3.

### Trust surface and evidence-directory inertness

Direct #print axioms on every named load-bearing theorem found only propext, Classical.choice, and Quot.sound. validRange_congr has no axioms. The new module has no direct sorry, admit, axiom, unsafe, opaque, implemented_by, native_decide, or Lean.ofReduceBool occurrence. The required whole-tree hygiene command found no matches in RMQ or lakefile.toml.

The only root import change is RMQ.lean:52. No pre-existing source under RMQ/Headlines, RMQPaper, scripts, SuccinctRMQClassic.lean, SuccinctFinalRAM.lean, or SuccinctFinalStoreParam.lean changed between base and target. Both axiom inventories pass, so the new edge does not change a pre-existing headline theorem's axiom footprint.

The delta has 320 files below docs/internal/f03_evidence. Its README says the directory is unvetted, outside build targets, and not acceptance evidence. No lakefile.toml or lake-manifest.json entry references it, and no RMQ Lean file imports it. The one RMQ occurrence is a provenance comment at GeometryClosure.lean:53-55; the cited lemmas are re-stated and proved in-tree. No load-bearing proof argument relies on an evidence-file declaration.

Evidence tier: targeted axiom prints are Tier 1; source/diff/import analysis is Tier 4; the README is Tier 5 and was checked against build configuration.

## 5. Scope fence, header, and F08 jurisdiction

The supplied-store fence accurately describes the theorem, but an arbitrary total store is broader than the closed controller's permitted prior replies. It is compatible with useful preparatory work but insufficient for row acceptance.

The header treatment is likewise preparatory. Folding headers into a store does not identify a permitted metadata interface or prove the controller reads only such fields and prior replies. F01/F02 remain the correct owners of schema and counted retrieval, but their non-goal status cannot relax F03's own input language.

F08 jurisdiction is correct: roadmap line 379, rather than F03, owns the packed codec, cell crossings, and n-independent physical cap. The reported 118 at n = 32 is a small-sample executable observation (Tier 3), not evidence of a physical cap. The result document keeps that caveat, so it is not a separate overclaim.

## 6. Objections considered and rejected

1. “The proof is vacuous or diagonal.” Rejected. Dropped-premise rfl failures, generic-premise type error, distinct-shape witnesses, and off-diagonal theorem applications show it is not obtained by unifying both sides.
2. “This proves a sibling or legacy route.” Rejected. Definition expansion reaches the five-instruction program, intended supplied-store evaluator, and queryTraceResultWithStore.
3. “Only the L2 same-block route is covered.” Rejected. The dispatcher proof has both by_cases arms, and independently forced endpoints exercise both.
4. “The root import silently changed old headline trust.” Rejected. Relevant old sources are unchanged, both inventories pass, and new theorem axiom prints have only ordinary assumptions.
5. “Unvetted campaign artifacts secretly supply acceptance evidence.” Rejected. They are excluded from targets/imports; the sole source mention is provenance, not a dependency.
6. “F03 must prove the physical probe cap.” Rejected. The frozen table assigns that to F08. Conversely, F08 ownership does not cure the missing F03 inventory or composition evidence.

## 7. Verification outcomes

| Check | Outcome and exact observed result |
|---|---|
| git status --short --branch | Exit 0 before this report: ## HEAD (no branch). |
| git log --oneline --decorate -20 | Exit 0. Relevant prefix: 6be9e55 Close EG-CP-F03: prove geometry closure and land it in the library; d988166 Prove T1; db43b25 Front-load the F03 campaign; d09bed7 Adopt the packed cell-probe endgame roadmap with two corrections. |
| git diff --stat d09bed7..6be9e55 | Exit 0: 327 files changed, 38581 insertions(+); code delta is one new 1,425-line module plus one root import, with 320 f03_evidence files. |
| git diff --check d09bed7..6be9e55 | Exit 0, no output. |
| first literal lake build | Wrapper timeout after 904 seconds while a child build continued. I inspected the process and artifacts rather than rerunning blindly; GeometryClosure.olean and RMQ.olean appeared after it. |
| final literal lake build | Exit 0 in 1.4 seconds. Success tail: [226/261] Replayed RMQ.Core.SuccinctFinalRAM, followed by existing replay warnings, then Build completed successfully. No warning names the new module. |
| lake env lean scripts/headline_axiom_check.lean | Exit 0. Every listed headline used only propext, Classical.choice, and/or Quot.sound; only existing unused-variable warnings at script lines 387, 406, 408, 418, 419, 429, 430, and 440. |
| lake env lean scripts/axiom_check.lean | Exit 0 after 355.2 seconds; 2,478 inventory lines, all using only the same standard assumptions or a subset. No sorryAx, native evaluator shortcut, custom axiom, or opaque trust escape was printed. |
| strict claim drift | Before report: Exit 0, 1,488 policy hits and 0 strict failures. Post-report: Exit 0, exact tail: CLAIM-DRIFT: scan complete (1491 hits, 0 strict failures). |
| strict design-decision check | Before report: Exit 0, DESIGN-CHECK: checked 12 changed files (9 code, 8 workflow, 2 neutral). Post-report: Exit 0, exact output: DESIGN-CHECK: checked 13 changed files (9 code, 8 workflow, 3 neutral). |
| paper topology lint | Exit 0: PAPER-TOPOLOGY: PASS [m1-safe-dependency] direct segment<23 -> safe-to-dynamic -> ordered equality -> packet -> paper; PAPER-TOPOLOGY PASS (86 broad documentary identifiers; 52 paper identifiers resolved). |
| independent scratch Lean controls | The successful proof/execution and deliberate rfl/unification failures are detailed in Section 4. |

The post-report git diff --check command also exited 0 with no output. These post-report checks ran on the tree containing this report.

## 8. Roadmap alignment and best next target

This delta materially advances the packed-cell-probe direction: it gives a kernel proof that the real five-instruction supplied-store controller has equal-size cross-shape trace congruence, including all three leaves and both L2 arms.

It does not yet reach the intended packed target because the exact inventory, typed universal-consumer map, header interface, and connection between supplied replies and the same memory xs remain unproved. Its purpose therefore remains open rather than merely documentary.

Best next target: create a checked exhaustive typed inventory of every current logical-read source and its universal consumer, then connect each entry to a controller invariant whose only dynamic inputs are n, endpoints, typed header words, and replies already present in the ordered trace of memory xs. Keep the new congruence as a reusable lemma. If an owner wants a theorem to replace the inventory artifact, the frozen row must first be amended explicitly and then audited against the new quantifiers.

## 9. Proof digestion

Conceptually, the delta says: hold a read store fixed, change the Cartesian shape while keeping its size, and the controller emits the same trace and value. In plain English, this evaluator cannot distinguish those shapes except through answers from the supplied store.

The live assumptions are equal Cartesian sizes, a shared arbitrary whole-store function, and the supplied-store evaluator. A skeptical graduate student should next ask where the typed list of all geometry decisions, header interface, and proof that the only usable store answers are previous probes of the same packed memory are. Those are the remaining acceptance surface.

## 10. Report path

docs/internal/audit_reports/2026-07-26_A10_f03_geometry_closure.md
