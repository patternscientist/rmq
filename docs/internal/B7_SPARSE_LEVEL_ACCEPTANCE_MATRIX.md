# B7 Charged Sparse-Table Level Acceptance Matrix (frozen before implementation)

Worker: B7-01 (branch `claude/b7-charged-sparse-level`, base
`f6564ec`). Contract source: the B7-01 delegation prompt, governed by
DD-20260718-012 (the Milestone 0 mechanism determination, committed at
`052eca4` BEFORE this matrix and before any implementation) and by
DD-20260717-C05-001. Requirement wording below is verbatim from the
delegation prompt. Frozen at this commit; after this commit only
evidence, status, and coordinator-approved amendments may change.

This matrix ADDS rows. No closed B2/B3/B4/B6 row is weakened or reopened.

## The finding this rung closes

`let level := Nat.log2 count` at four EXECUTED evaluator sites
(`RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorRAM.lean:573`,
`:621`, `:819`, `:867`, the latter two on `macroSpanCount`), with cost
twins at `EndpointFringe/InteriorCandidate/LocalGlobalSparse.lean:30` and
`:603` and store-parametric twins at
`RelativeRmmMacro/ConcreteDirectoryRAMStoreParam.lean:1405` and `:1995`.
The level feeds an accepted READ ADDRESS through `bpLocalSparseCellSlot`
(`EndpointFringe/PrefixRange/LocalSparseOffset.lean:15-17`) and
`bpGlobalSparseCellSlot` (`LocalGlobalSparse.lean:199-201`). `Nat.log2`
is a Theta(log n) recursion emitting no trace events on a runtime-derived
argument.

THE SPAN IS IN SCOPE. Each site also evaluates `bpSparseLogSpan count =
2 ^ Nat.log2 count` (`EndpointFringe/PrefixRange/SparseArgMin.lean:598-599`);
`Nat.pow` is a second Theta(log n) recursion at the same site. A fix that
charges the level and leaves the span uncharged does NOT close this rung.
This is recorded here because the delegation named the span in the
finding, and because DD-20260718-011 (E1-R4m) independently flagged both.

## Chosen mechanism (DD-20260718-012)

Mechanism 3 in a single-source, single-read form: one new counted table
over domain `D = macroSize + macroCount + 1`, cell `i` storing
`Nat.log2 i * D + bpSparseLogSpan i`, unpacked by constant-divisor
div/mod, read once per two-span call. Mechanisms 1, 2, and 4 rejected
with the evidence recorded in DD-20260718-012. An `msb`/`log2` ISA
instruction and any bound weakened to accept Theta(log n) work were NOT
evaluated, per the user decision recorded in the delegation.

## Derived consequence, frozen at freeze time as a DERIVATION not a result

The cost chain 5 -> 10 -> 30 is exactly tight
(`spanCandidateCosted_cost_le_five` at `LocalSparseOffset.lean:450` and
`LocalGlobalSparse.lean:494`; `twoSpanCandidateCosted_cost_le_ten` at
`LocalGlobalSparse.lean:41`/`:613`;
`bpTwoLevelInteriorCandidateCosted_cost_le_thirty` at
`TwoLevelCandidate.lean:53`), and 30 is ATTAINED on the cross-macro
branch, which carries all three new reads. So the interior cap is
expected to move 30 -> 33 and the literal 207 -> 210. Unlike B6, this
rung's recharged leaf IS on the maximizing branch. REQ-B7-05 records this
as the expected outcome but its evidence column is authoritative: the
derivation wins over this prediction if they disagree.

## Verified anchors (this worktree, base `f6564ec`)

- the four executed sites and two cost twins, as listed above;
- caller chain: `twoSpanCandidate...` ->
  `bpTwoLevel{Adjacent,LeftMiddle,Cross}MacroCandidateTraceResult`
  (`InteriorRAM.lean:1150`, `:1198`, `:1257`; segment variants `:1321`,
  `:1371`, `:1432`) -> `bpTwoLevelInteriorCandidateTraceResult(AtSegments)`
  (`:1498`, `:1579`) ->
  `concreteBPRelativeRmmInteriorRangeMinTraceResult...OfReady`
  (`RelativeRmmMacro/ConcreteDirectoryRAM.lean:376`, `:398`, `:423`) ->
  `crossBlockCloseTraceResultWithRankSeed...` (`:1920`, `:2051`) ->
  `lcaCloseTraceResultWithRankSeedAtSegments...` (`:3700`, `:3746`) ->
  `concreteBPNativeLCACloseWordTraceResultAtSegmentsOfSizeGe`
  (`SuccinctFinalRAM.lean:2238`);
- argument provenance (`InteriorRAM.lean:1515-1525`,
  `TwoLevelCandidate.lean:32-42`): `count`, `leftCount = macroSize -
  startBlock % macroSize`, `rightCount`, `middleMacroCount`;
- range hypotheses actually available: `0 < count`,
  `count <= macroSize` (local) and `0 < macroSpanCount`,
  `macroSpanCount <= macroCount` (global), converted to
  `Nat.log2 _ < levelCount` by the ASSUMED `hlocalLevel`/`hglobalLevel`
  at `TwoLevelCandidate.lean:241-248`;
- sizing constants: `canonicalBPRelativeSummaryBase = Nat.log2 size + 1`
  (`RelativeSummary.lean:1238`), `blockSize = 2 * base` (`:1242`),
  `macroSize` (`RelativeSummary.lean:2733-2736`), `levelCount` /
  `globalLevelCount` (`:2743-2755`), `machineWordBits`
  (`SuccinctRank.lean:38-39`);
- new-source template to follow: `ChargedFringeSpace.lean:37-77`
  (`bpChunkedOverheadCandidate`, `bpChunkedBuildPayloadCandidate`,
  `..._littleO`, `..._length`) plus `ChargedFringeTableFacts.lean`;
- cost algebra: `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra`
  (`SuccinctFinalRAM.lean:8810-8820`; `selectClose := 35`,
  `rankClose := 11`, `endpointFringe := 37`, `interiorDirectory := 30`),
  `..._CloseCost_eq = 126` (`:8818`), `..._TraceCost_eq = 207` (`:8822`);
  historical-constant pattern at `:8825-8875` (76, 142) and 328;
- consumers of 207: `Headlines/RMQ.lean:70/:497/:529`,
  `Validation/SuccinctClassic.lean:266`,
  `Validation/SuccinctClassicCostHarness.lean:118` (`canonicalBoundIs207`),
  `RMQExamples/Concrete.lean:84`, `scripts/paper_topology_lint.ps1`
  (`SumLe207`), `scripts/headline_axiom_check.lean`;
- vocabulary theorem:
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`.

| ID | Exact frozen requirement (verbatim) | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-B7-00 | "MILESTONE 0 - MECHANISM DETERMINATION (do this first, commit the finding before implementing) ... recording the evidence and the rejected alternatives in a DD entry". | Process | A DD entry committed BEFORE any implementation commit, evaluating mechanisms 1-4 in the stated preference order, choosing the highest that works, and recording the rejected alternatives with evidence rather than assertion. | Governs every other row. | The rejections must rest on checked structural or arithmetic facts at cited file:line, not on plausibility. Mechanism 1 in particular must be rejected by an argument about read ORDER, not by an unsuccessful search. | DD-20260718-012 committed at `052eca4`, before this matrix and before any Lean change. Mechanism 1 rejected structurally: the level forms the ADDRESS consumed by `bpLocalSparseCellSlot`/`bpGlobalSparseCellSlot`, so it is required strictly before the first charged read of the span exists; the reads present are single-field `FixedWidthNatTable.readCosted` (`SuccinctSpace/Tables.lean:86-91`). Mechanism 2 rejected arithmetically: the cross-macro branch needs the levels of THREE different runtime values (`InteriorRAM.lean:1278-1287`), and the offset cell has ~1 spare bit. Mechanism 4 rejected by a size computation: span-indexing costs `n * macroSize` bits = Theta(n polylog). | Closed |
| REQ-B7-01 | "mechanism justification". | Local | The chosen mechanism's o(n) sizing derived over the domain of values that ACTUALLY OCCUR (`count` / `macroSpanCount` ranges), not over all of `Nat`, with the domain bound checked against the route's own hypotheses. | Feeds REQ-B7-06 (erasure/capacity/o(n)) and REQ-B7-02. | The domain must be shown to COVER every reachable index (else reads fall out of range and the table is vacuous), and to be o(n)-sized (else the public space claim breaks). Both directions required. | | Open |
| REQ-B7-02 | "value equivalence to the accepted level at every executed site under the route's own hypotheses". | Local | Checked theorems: the table-read level equals `Nat.log2 count` and the table-read span equals `bpSparseLogSpan count`, universally quantified, under exactly the hypotheses available at the accepted call sites (`0 < count`, `count <= macroSize`; `0 < macroSpanCount`, `macroSpanCount <= macroCount`) - not on sampled inputs, and not under added readiness guards. Plus: the amended two-span objects have the SAME `.value` as the accepted ones. | Route exactness through `bpTwoLevelInteriorCandidateCosted_erase_exact` (`TwoLevelCandidate.lean`) and the `..._erase_..._exact` chain in `LocalGlobalSparse.lean`. | P = value equality of the full `Option (Nat x Nat)` result at all four sites for all reachable invocations. Reject Q1 (agreement on sampled inputs), Q2 (level only, span left uncharged), Q3 (agreement under an added hypothesis the route cannot discharge). Name the checked theorem rejecting each. | | Open |
| REQ-B7-03 | "positional receipt/trace equality". | Local | TraceResult and WithStore twins for the amended two-span objects whose trace is the accepted events PLUS exactly one `readWord levelSegment slot` per two-span call, in a checked POSITIONAL (`List` equality) statement; `_refines`, `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`, `_trace_forall`, `_eq_of_agree`, `_store_parametric`. | Amended dispatchers up to `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`. | The trace must contain the ACTUAL `readWord` event produced by the store computation, never an `ofCosted` synthetic marker; the refined value must depend on the read word. | | Open |
| REQ-B7-04 | "charged-read backing and provenance to the W19 standard if a new source is added". | Local+roadmap | A new source is added, so the FULL treatment is required: counted source, segment number, store arm, erasure exactness, capacity, littleO, and provenance packets (`every_emitted_read_has_listed_region`, `..._occurrence_provenance`, `..._eventValue_producer_provenance`) regenerated with a level-read producer path; a W19 successful-occurrence witness exhibited on an execution that actually reads the level table. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`; chain: level read -> segment -> source -> region -> physical address -> counted payload. | Provenance must cover the ACTUAL emitted level events by PRODUCER (producing instruction + occurrence position), not merely assert segment membership; deleting the level case from the regenerated induction must break adequacy. `canonical_segments_complete` must move from `< 22` to the new bound. | | Open |
| REQ-B7-05 | "derived route literal". "DERIVE whether that happens again - do not assume it either way. If the literal must move, freeze 207 as a named historical constant with its `_eq` theorem and guards exactly as 142/76/328 already are, and update every Lean consumer plus the current topology anchor (`SumLe207` -> the new value in `scripts/paper_topology_lint.ps1` and `scripts/headline_axiom_check.lean`; frozen legacy anchors untouched). If it does not move, say so with the derivation." | Local+public | The literal RE-DERIVED by `rfl` from the named component algebra over the amended route, never asserted. If it differs from 207: mint `concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost = 207` by the 142/76/328 pattern, and update every consumer enumerated in the anchors above. | `SuccinctClassic.queryCost_eq` -> paper main theorem conjunct -> headline abbrevs -> harness/validation/examples guards -> topology anchor. | The literal must be DERIVED (`rfl`) from the algebra, not asserted against an independent numeral; mutating a component constant must break the `_eq` right-hand side. If the value moves, verify it moves BECAUSE the new reads are genuinely in the accounting on the maximizing branch (exhibit the checked branch bound), not because a cap was loosened. | | Open (expected 207 -> 210 per DD-20260718-012; derivation authoritative) |
| REQ-B7-06 | "erasure/capacity/o(n) preservation with the exact public statement shape `buildPayload.length <= 2*n + overhead n`, `overhead = o(n)`". | Public surface | The amended payload/overhead pair keeps the EXACT public statement shape, with `LittleOLinear` for the amended overhead, following `ChargedFringeSpace.lean:37-77`; physical erasure of the new table checked; entry width within the reviewer machine word. | `SuccinctRMQClassic.lean:951` public payload bound; capstone conjunct. | The o(n) proof must be about the ACTUAL table the route reads (two-payload trap), and must hold at every n including tiny shapes, with no threshold. | | Open |
| REQ-B7-07 | "vocabulary theorem re-established". | Public | `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only` RE-PROVED over the amended route (re-elaborated after the definitions change), not inherited from the pre-amendment object. | Whole-query trace surface. | The new level events must be `readWord`; the theorem must fail to build if the level read emitted anything else. | | Open |
| REQ-B7-08 | "charge-policy doc repaired" - "repair the charge-policy section of `docs/PAPER_MODEL_ADEQUACY.md` so it is TRUE after this rung - including the representation-artifact-versus-algorithmic-work principle with named bridge lemmas." | Public surface | The charge-policy section amended so its claim is true of the amended route; the sparse level named as the leg that made it false; the round-7 principle stated with NAMED bridge lemmas distinguishing representation artifacts (value checked-equal to an input parameter or a charged read) from algorithmic work; residual uncharged work enumerated precisely with its checked cap. | Paper adequacy doc; `claim_drift_scan.ps1`, `paper_topology_lint.ps1`. | Every "bounded per step" claim must name the checked cap. The principle must come with actual bridge lemma NAMES, not a prose restatement. Deleting a false sentence without stating the new truth is insufficient. | | Open |
| REQ-B7-09 | "library-green-per-commit"; "no dead sources at any commit"; parallel-then-swap. | Process | Per-commit `lake build RMQ` exit 0 recorded in the `B7_WORKLOG.md` ledger; the swap atomic within one commit; no commit introduces a counted-but-unread source. | Coordinator audit of branch history. | `git log` + ledger cross-check at final report. Note the standing warning: per-file `lake env lean` is an iterate aid only and has previously reported clean on code spliced inside a `/-!` comment. | | Open |
| REQ-B7-10 | "committed hygiene". | Verification | No NEW forbidden-token hits in touched files; native_decide scan clean; `git diff --check` and `git diff --check f6564ec..HEAD` clean; `design_decision_check.ps1 -Strict -Base f6564ec`, `claim_drift_scan.ps1`, `paper_topology_lint.ps1` exit 0. Do NOT run `scripts/axiom_check.lean` or `gate.ps1`. | Hygiene. | `#print axioms` AFTER a root build on every claimed theorem (per-file checks write no olean, so fresh names report `unknown constant` until then). | | Open |
| INV-STORE-IDENTITY | Inherited: "the exact payload/store executed is the payload/store counted by the public space theorem". | Inherited | The level reads execute against the same counted table object that the amended public space theorem counts; flatten/erasure chain extended, not bypassed. | REQ-B7-04 chain. | Two-payload trap: the counted table component must be the same object the level execution reads. A new source makes this a REAL obligation here, unlike B6 where it was inherited. | | Open |
| INV-VALUE-DEPENDENCY | Inherited: "returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads". | Inherited | A corruption witness at a slot the level execution actually reads changes the RETURNED interior candidate value, not merely the trace log. | REQ-B7-02. | The corruption must move the returned `Option (Nat x Nat)`; a witness that moves only the level variable while the candidate is unchanged is insufficient. | | Open |
| INV-NO-SYNTHETIC | Inherited: "synthetic events, decorative rereads, and post-hoc replay do not support the execution claim". | Inherited | `_no_syntheticCostOnlyPrimitive` checked for every new level trace object; every charged unit is a table read. | REQ-B7-03. | Decorative-read challenge: the level read's value must flow into the result - it does so through the ADDRESS of the subsequent span read, which is the strongest possible form of dependence. | | Open |
| INV-ALL-SIZE | Inherited: "exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch". | Inherited | All new equivalence/cost theorems quantified over all shapes/sizes; no `Ready`/threshold predicate; degenerate `count = 0`, `count = 1`, and maximal `count = macroSize` / `macroSpanCount = macroCount` covered by the same unguarded statement. | REQ-B7-01/02. | Grep the new code for readiness predicates. Check `count = 0` specifically: `Nat.log2 0 = 0` and `bpSparseLogSpan 0 = 1`, so the table's cell 0 must agree with whatever the accepted route does on that argument, or the equivalence must carry `0 < count` and the route must discharge it. | | Open |
| INV-PUBLIC-COMPOSITION | Inherited: a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution. | Inherited | The capstone/profile theorems re-proved over the amended route (amended payload, amended execution), not conjoined across pre- and post-swap objects. | REQ-B7-05/06. | The capstone's `rfl` conjunct must still hold against the AMENDED payload - and since this rung DOES add a source, that conjunct genuinely changes, unlike B6. | | Open |
| CHK-01 | "`lake build RMQ RMQPaper RMQExamples`". | Verification | Exit 0. | - | - | | Open |
| CHK-02 | "`lake env lean scripts/wordram_axiom_check.lean`". | Verification | Exit 0. | - | - | | Open |
| CHK-03 | "`lake env lean scripts/headline_axiom_check.lean`". | Verification | Exit 0, with the anchor moved to the derived literal. | - | - | | Open |
| CHK-04 | "cost harness". | Verification | Harness run recorded; guards consistent with the DERIVED literal; interior-route windows must MOVE (empirical anti-vacuity that the swap is live). | - | - | | Open |
| CHK-05 | "hygiene `rg` + native_decide scan". | Verification | No new forbidden-token hits; zero `native_decide`/`ofReduceBool`. | - | - | | Open |
| CHK-06 | "`git diff --check` + `git diff --check f6564ec..HEAD`". | Verification | Exit 0. | - | - | | Open |
| CHK-07 | "`design_decision_check.ps1 -Strict -Base f6564ec`". | Verification | Exit 0. | - | - | | Open |
| CHK-08 | "`claim_drift_scan.ps1`; `paper_topology_lint.ps1`". | Verification | Exit 0, with `SumLe207` migrated to the derived literal if it moves. | - | - | | Open |
| STRETCH-01 | "a COMPLETE INVENTORY of every uncharged computation reachable from the accepted whole-query route, each classified as representation artifact (with its checked bridge lemma) or charged, committed as a doc section." | Stretch | An enumeration with a stated derivation method (so its completeness is auditable), each entry classified with its bridge lemma name or its charging evidence. | Converts "we fixed the ones we found" into "here is the complete list". | The enumeration must state HOW completeness was established (e.g. mechanized reachability from the route root), not merely list what was noticed. Already-known input: the dead `maxRel` read at the min-candidate site (DD-20260718-012). | | Open (stretch; attempted only after the rung closes) |

## Amendment 1 (coordinator-relayed correction, before implementation)

Recorded per the matrix's own rule that after freezing, only evidence,
status, and coordinator-approved amendments may change. Full evidence in
DD-20260718-013. Nothing below weakens a requirement; two rows get
HARDER-to-satisfy evidence and one gets lighter.

1. SITES CORRECTED. The "finding this rung closes" section above cites
   `InteriorRAM.lean:573/621/819/867`. Those are cost-model twins on the
   refinement ladder, NOT the executed route. The executed sites are the
   `FlatStoreComputation` family: `InteriorDirectory.lean:2117` (local,
   level -> `bpLocalSparseCellSlot` at `:2088`), `InteriorDirectory.lean:2131`
   (global, level -> `bpGlobalSparseCellSlot` at `:2106`), and
   `SparseArgMin.lean:599` (invoked at `:2118`/`:2132`). Root:
   `canonicalRelativeRmmInteriorRangeMinComputation`
   (`InteriorDirectory.lean:2185`), reached from
   `canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment`
   (`ConcreteDirectoryRAM.lean:1113`). REQ-B7-02 and REQ-B7-03 must be
   evidenced on THESE objects; evidence on the `PayloadLive*` family does
   not discharge them.

2. REQ-B7-04 IS LIGHTER THAN FROZEN. `flatStoreExecutionTraceResultAtSegment`
   (`InteriorRAM.lean:175-180`) maps the whole interior execution onto ONE
   component segment, so the new table joins the existing interior
   component store as a region rather than becoming a new segment. NO new
   segment, NO new `ReviewerSource`, and `canonical_segments_complete` does
   NOT move. The row's remaining obligations (erasure, capacity, littleO,
   producer provenance, W19 witness on an execution that actually reads the
   level table) stand unchanged.

3. REQ-B7-05 SETTLED IN ADVANCE, WITH EVIDENCE. The interior cap is
   genuinely tight: in
   `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
   (`InteriorDirectory.lean:4451-4510`) the cross-macro branch discharges
   `..._cost_le_thirty_of_macro_crossing` DIRECTLY against the cap with no
   `Nat.le_trans` and zero numeric slack, while the other three branches
   carry slack 12, 10, 10. So interior 30 -> 33 and the literal 207 -> 210.
   The row's evidence column remains authoritative and the final value must
   still be `rfl`-derived over the amended route.

4. REQ-B7-01 SIZING SUPERSEDED. Build ONE generic count-indexed table and
   instantiate it TWICE (local, indexed by `count <= macroSize`; global,
   indexed by `macroSpanCount <= macroSampleCount`) rather than one merged
   table over a summed domain. The global instance reuses
   `logLogSampledDirectoryOverhead_littleO` (`Asymptotics.lean:243`) via
   `LittleOLinear.of_le` (`:35`); the local instance repackages
   `eventually_scale_log2_succ_cube_le_self` (`Asymptotics.lean:516`). The
   chunk-table `littleO` pattern must NOT be copied. Linear-capacity feed
   analogues are still required.

5. NOT A CONSTRAINT. The E1 note at `E1_WORKLOG.md:2340-2343` rejecting a
   table read on positional-receipt grounds is over-strict; B2/B3/B6 each
   added reads to the accepted route.

## Evidence at commit A (`f6000c3` .. `90c1fbf`), recorded by B7-06

Appended rather than written into the frozen cells, so the frozen
requirement text stays verbatim. NO ROW IS CLOSED BY THIS SECTION and no
row is weakened. Commit A is the staging half of the rung; the swap
(commit B) is not started.

Statuses that MOVE: none.
Statuses that gain evidence while remaining Open: REQ-B7-05, REQ-B7-08,
CHK-01, CHK-02, CHK-03, CHK-04, CHK-05, CHK-06, CHK-07, CHK-08.

### REQ-B7-05 - REMAINS OPEN, and the reason matters

The literal now reads `210` and re-derives by `rfl` from the named
component algebra:

    closeLCA   = 2*rank11 + 2*fringe37 + interior33 = 129
    wholeQuery = 2*select35 + 129 + rank11          = 210

checked by `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq`
and `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`, both
`by rfl`, both reporting "does not depend on any axioms".

The freeze half is DONE by the 142/76/328 pattern:
`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq = 207`,
its `..._CloseCost_eq = 126` companion, the public abbrev
`canonicalSilentSparseLevelQueryCost`, guards in
`Validation/SuccinctClassic.lean` and `RMQExamples/Concrete.lean`, and the
anchor migration `SumLe207 -> SumLe210` in both scripts. All four fields of
the frozen algebra are literals (two numerals, two pinned components), per
the `228ae8f` freezing discipline. No frozen identity renamed or deleted.

The row nevertheless STAYS OPEN. Its anti-vacuity challenge requires the
literal to move BECAUSE the new reads are genuinely in the accounting on
the maximizing branch, "not because a cap was loosened". At commit A it
moved because a cap was loosened - that is precisely the condition the row
tells us not to accept. Closing REQ-B7-05 requires re-deriving `210` over
the AMENDED route at commit B and exhibiting the checked branch bound that
consumes the three units.

### REQ-B7-08 - substantially advanced, REMAINS OPEN

`docs/PAPER_MODEL_ADEQUACY.md` gains a new section, "Why the Literal Moved:
Representation Artifact vs Algorithmic Work", which states the principle
(the model's unit of cost is the memory touch, not the comparison; a
representation artifact must be charged, and leaving one uncharged is an
unmodelled algorithm rather than a cheaper one) and names the bridge
lemmas rather than paraphrasing them:

- `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_literal_of_size_ge_four_of_bounded`
- `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded`
- `canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCloseCost_eq` (129)
- `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq` (210)
- `concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost_eq` (207)

B6's stale "207, unchanged" narrative is corrected in place rather than
deleted, and the `48 <= 126` step is restated as `48 <= 129`.

OPEN because the row demands the section be true of the AMENDED route. It
is currently true of commit A's route, which is not the same thing. The
residual-uncharged-work enumeration with checked caps is also still owed
(that is STRETCH-01's inventory feeding this row).

### Verification rows, as observed

- CHK-01 `lake build RMQ RMQPaper RMQExamples`: exit 0, 267/268, "Build
  completed successfully". Evidence obtained; row stays Open because it
  must hold at the CANDIDATE state, which is post-swap.
- CHK-02 `lake env lean scripts/wordram_axiom_check.lean`: exit 1, ONE
  error, `scripts/wordram_axiom_check.lean:197:14: error: unknown constant
  'RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_76'`.
  This is the KNOWN RED item owned by `claude/a07-blocker-repairs`,
  recorded and not fixed per the delegation. It references the retired
  `76`, not `207`/`210`, so B7's migration neither caused it nor worsened
  it - the error count is still exactly one and it is the same one.
- CHK-03 `lake env lean scripts/headline_axiom_check.lean`: exit 0, with
  the anchor moved to `...SumLe210`.
- CHK-04 cost harness: exit 0, "all reported windows agree",
  `canonicalBound=210` / `canonicalBoundIs210=true` on every window - so
  the guards ARE consistent with the derived literal. But every one of the
  twelve `modeledTraceCost` values is IDENTICAL to the session-2 pre-swap
  baseline, so the anti-vacuity half - "interior-route windows must MOVE" -
  is NOT satisfied and is NOT claimed. Correct at commit A, which adds no
  reads; dischargeable only at commit B.
- CHK-05 hygiene: zero forbidden-token hits across all eight touched Lean
  files; zero `native_decide`/`ofReduceBool` repo-wide.
- CHK-06 `git diff --check`: exit 0 on the working tree.
  `git diff --check f6564ec..HEAD`: exit 2, hits ONLY
  `docs/internal/B7_STEP2_WIP.patch` - the structural committed-patch
  property documented since B7-03, not a source defect.
- CHK-07 `design_decision_check.ps1 -Strict -Base f6564ec`: exit 0 after
  WDD-20260719-001 was logged (exit 1 before, on
  `scripts/paper_topology_lint.ps1`).
- CHK-08 `claim_drift_scan.ps1`: exit 0. `paper_topology_lint.ps1`:
  "PAPER-TOPOLOGY PASS (83 broad documentary identifiers; 49 paper
  identifiers resolved)", exit 0, with `SumLe207` migrated to `SumLe210`.

Per the delegation, `scripts/axiom_check.lean` and `gate.ps1` were NOT run.

### Invariant rows

INV-STORE-IDENTITY, INV-VALUE-DEPENDENCY, INV-NO-SYNTHETIC, INV-ALL-SIZE
and INV-PUBLIC-COMPOSITION are all untouched by commit A and remain Open.
Commit A adds no source, no read, and no store region; it changes a cap, a
literal, and the names carrying that literal. INV-ALL-SIZE is worth one
positive note: the new literal interior theorem and the slack artifact
carry exactly the hypotheses the pre-existing cap theorem carried
(`4 <= shape.size` and the block bound) and add no readiness or threshold
predicate.

## Evidence at session 7 (B7-07): an obstruction to REQ-B7-05's predicted value

Appended per the matrix's own rule that after freezing only evidence, status
and coordinator-approved amendments may change. NO ROW IS CLOSED by this
section and no row is weakened. The swap (commit B) is still not landed.

Statuses that MOVE: none.
Statuses that gain evidence while remaining Open: REQ-B7-01, REQ-B7-05.

### REQ-B7-05 / REQ-B7-01 - the "one charged read per two-span call" premise is FALSE as stated

This matrix's "Derived consequence" section, DD-20260718-012, Amendment 1
point 3, and commit A all rest on each two-span call gaining exactly ONE unit
of charged cost, hence interior `30 -> 33` and literal `207 -> 210`.

DERIVED THIS SESSION over the amended route, and it contradicts that
prediction. In this cost model a table read costs one unit PER MACHINE WORD
TOUCHED, not one unit per read:
`canonicalRelativeRmmMachineReadNatCosted_cost_le_one`
(`InteriorDirectory.lean:3945`) is available only under
`width <= SuccinctRank.machineWordBits shape.bpCode.length`.

The charged level table's stored width is
`bpSparseLevelWidth domain = Nat.log2 (domain * domain) + 1`
(`SparseLevelTable.lean:131`) with `domain = macroSize + 2` and
`macroSize = b^2`, `b = Nat.log2 size + 1`. That width EXCEEDS the machine
word on reachable macro-crossing shapes:

    size    b   macroSize  domain  width  machineWord  read cost
    2048    12  144        146     15     13           2
    8192    14  196        198     16     15           2
    32768   16  256        258     17     17           2
    65536   17  289        291     17     18           1

Macro crossing is `size > b^3`; at `size = 2048`, `b^3 = 1728 < 2048`, so the
CROSS-MACRO branch - the maximizing branch carrying all three new reads - is
reachable where each level read costs 2. The cross-macro bound is therefore
`30 + 3*2 = 36`, giving `closeLCA 132` and `wholeQuery 213`, NOT the `33` and
`210` commit A already froze and migrated every consumer to.

This is precisely the outcome REQ-B7-05's anti-vacuity challenge exists to
catch: commit A moved the literal because a cap was loosened, and deriving it
over the amended route yields a different number.

RECOMMENDED ROUTE, recorded so the row is not closed against the wrong value:
the cell is over-wide by construction, not by necessity. `bpSparseLevelCell_lt`
(`SparseLevelTable.lean:99`) bounds the level by `domain` when it is in fact
bounded by `Nat.log2 domain`. Tightening the width to
`Nat.log2 (domain * (Nat.log2 domain + 1)) + 1` yields widths 11-12 against
machine words 13-18 on exactly the shapes above - one word, with margin -
restoring cost 1 per two-span call and with it `33` / `210`. The literal must
still be DERIVED over the amended route, not assumed back into place.

REQ-B7-01 gains this as evidence too: the row requires the sizing to be derived
over the domain of values that ACTUALLY OCCUR. The same over-approximation that
inflates the width (bounding the level by `domain` rather than by
`Nat.log2 domain`) is a sizing defect in the table as built, not only a cost
defect.

### Verification rows - unchanged and NOT re-claimed

CHK-01 through CHK-08 were not re-run this session; the rung is not at a
candidate state. CHK-04 in particular remains OPEN and unclaimed: no swap
landed, so the twelve interior windows are necessarily still identical to the
commit A baseline. The slack artifact remains present and true.

## Evidence at session 8 (B7-08): the width obstruction is CLOSED, all-size

Appended per the matrix's own rule that after freezing only evidence, status
and coordinator-approved amendments may change. NO ROW IS CLOSED by this
section and no row is weakened. The swap (commit B) is still not landed.

Statuses that MOVE: none.
Statuses that gain evidence while remaining Open: REQ-B7-01, REQ-B7-05,
REQ-B7-06.

### REQ-B7-01 - the sizing defect session 7 identified is REPAIRED

Session 7 recorded that bounding the stored level by `domain` rather than by
`Nat.log2 domain` is a SIZING defect in the table as built, not only a cost
defect, and that this row requires the sizing to be derived over the domain of
values that ACTUALLY OCCUR. Repaired at `fa5e94d`:

    theorem bpSparseLevelCell_lt
        {i domain : Nat} (hdomain : 2 <= domain) (hi : i < domain) :
        bpSparseLevelCell domain i < domain * (Nat.log2 domain + 1)

    def bpSparseLevelWidth (domain : Nat) : Nat :=
      Nat.log2 (domain * (Nat.log2 domain + 1)) + 1

The stored level is `Nat.log2 i` with `i < domain`, so `Nat.log2 domain` is the
bound the occurring values actually justify. The table is correspondingly
smaller at every domain.

### REQ-B7-05 - the read is now ONE MACHINE WORD, proved for ALL shapes

The coordinator ruled that the width be tightened to recover commit A's frozen
`210`, rather than freezing `210` as a historical constant and migrating to
`213`. The policy reason is recorded in DD-20260719-001: `76`, `142` and `207`
each genuinely described the accepted route at some point in its history;
`210` never did, so freezing it would place a fiction in the permanent record.

The evidence required was explicitly NOT a sampled table of sizes. It is a
checked all-size proposition carrying the route's own reachability hypothesis:

    theorem bpSparseLevelLocalWidth_le_machine_of_macro_crossing
        {shape : Cartesian.CartesianShape}
        (hmacro : (RelativeRmm.canonicalLayout shape).macroSize <
            (RelativeRmm.canonicalLayout shape).blockCount) :
        bpSparseLevelWidth
            (bpSparseLevelDomain (RelativeRmm.canonicalLayout shape).macroSize) <=
          SuccinctRank.machineWordBits shape.bpCode.length

with the global twin over `macroSampleCount`. Both report
`[propext, Quot.sound]` only.

WHY THE HYPOTHESIS IS NOT A THRESHOLD, which is the substance of this row's
anti-vacuity concern. `hmacro` is exactly what the interior dispatcher already
derives from its own branch guard `hcross` and the route-level `hbound` before
a cross-macro two-span call is reachable at all; the existing
`canonicalRelativeRmmRelativeWidth_le_machine_of_macroSize_lt_blockCount`
carries the identical hypothesis for the relative summary field. Nothing was
added to the public route, and no size regime is tested anywhere.

The hypothesis is LOAD-BEARING rather than decorative: at `size = 4` the
tightened width is 6 against a `machineWordBits` of 4, so the fit genuinely
FAILS there and is saved only because macro crossing requires
`macroSize = 9 < blockCount = 1`, which is false. `10 <= base` is DERIVED by
eliminating `base <= 9` against `base^3 < size < 2 ^ base`, not assumed.

Branches that do not carry `hmacro` are covered by two UNCONDITIONAL fit
theorems at the `cost_le_eight` rate, so no branch is left without a checked
width bound.

THE ROW STAYS OPEN. This establishes that the read CAN be one word on the
maximizing branch; it does not re-derive the literal. Closing REQ-B7-05 still
requires deriving the literal over the AMENDED route and exhibiting the
maximizing branch bound that consumes the three units. No swap has landed, so
that derivation does not yet exist.

### REQ-B7-06 - the o(n) accounting survives, and was re-derived not assumed

The tighter width makes the table smaller, so every space bound gets easier -
but the four space-accounting links state the width SYNTACTICALLY (13
occurrences across the raw-overhead def, the `527` linear feed and the envelope
arithmetic), so they do not transport for free. Each is inherited through one
`Nat.le_trans` on a new bridge:

    private theorem bpSparseLevelWidth_le_square_width
        {domain : Nat} (hpos : 0 < domain) :
        bpSparseLevelWidth domain <= Nat.log2 (domain * domain) + 1

Consequences relevant to this row: the `527` capacity constant and both
`LittleOLinear` envelopes are UNCHANGED and remain valid (now loose rather than
tight, which is sound for upper bounds), so `ReviewerPhysical.lean` needs no
second migration. The row's "no threshold" requirement is unaffected - the
space accounting is unconditional and covers every `n` including `n = 0`, whose
case needed one genuine repair (it previously closed on `Nat.log2 9` and now
needs `bpSparseLevelWidth 3`, routed through the bridge).

THE ROW STAYS OPEN: the accounting is stated over the amended payload only in
the WIP patch, not in committed source.

### Verification rows - unchanged and NOT re-claimed

CHK-04 remains OPEN and unclaimed. No swap landed this session, so the twelve
interior windows are necessarily still identical to the commit A baseline and
the harness was not run. The slack artifact remains present and true, which is
the correct state for a tree where the swap has not landed.

`lake build RMQ` at `fa5e94d`: exit 0, 243/244, zero errors, twelve
pre-existing warnings (baseline-identical, none in a touched file). This is the
per-commit evidence REQ-B7-09 asks for.

## Evidence at session 10 (B7-10): the swap is COMMITTED and the library is green

The swap landed as real source at `c45e62c` (preservation commit `714fb4a`
first). `lake build RMQ RMQPaper RMQExamples` exits 0. The last blocker was a
read-order defect in `ReviewerReachabilitySmall.lean`, not a performance
problem; see the session-10 worklog entry for the diagnosis.

### REQ-B7-05 - the literal is DERIVED, and the maximizing branch is exhibited

Quoted proposition, `RMQ/Core/SuccinctFinalRAM.lean:8828`:

    theorem concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq :
        concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 210 := by
      rfl

The right-hand side is reached through the NAMED component algebra
(`:8811-8821`), whose `interiorDirectory` field names the LIVE cap definition
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost`
(`InteriorDirectory.lean:1934`, `:= 33`):

    closeLCA   = 2*rank11 + 2*fringe37 + interior33 = 129
    wholeQuery = 2*select35 + 129 + rank11          = 210

ANTI-VACUITY (P/Q): P = "the literal is computed from the algebra";
Q = "mutating a component constant breaks the `_eq` right-hand side". Because
`interiorDirectory` names the live cap rather than a numeral, moving the cap
necessarily moves `210`; this is the same mechanism that moved it from `207`.
`#print axioms` reports `queryCost_eq`,
`..._PrincipledAllSizeChargedTraceCost_eq` and `..._CloseCost_eq` as "does not
depend on any axioms" - a pure computation, not an assertion.

THE MAXIMIZING BRANCH, `InteriorDirectory.lean:5461-5517`. The four live
branches of `..._cost_le_thirty_three_literal_of_size_ge_four_of_bounded`
discharge as:

    within-macro (two-span)   _cost_le_twenty_six_of_size_ge_four    26, slack 7
    adjacent-macro            _cost_le_twenty_two_of_macro_crossing  22, slack 11
    left-middle-macro         _cost_le_twenty_two_of_macro_crossing  22, slack 11
    cross-macro               _cost_le_thirty_three_of_macro_crossing 33, slack 0

The cross-macro branch is discharged by a BARE `exact` against the cap
(`:5516-5517`) with no `Nat.le_trans` and no numeric slack, while the other
three route through `Nat.le_trans ... (by simp)`. The cap is therefore attained,
not merely respected - which is exactly the shape Amendment 1 predicted for the
recharged rung, and it is what makes `30 < cap` unprovable.

THE FROZEN HISTORICAL CONSTANT IS GENUINELY FROZEN. `207` is retained as
`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost` (`:8959-8964`)
over an algebra whose components are PINNED LITERALS (`:8852 := 30`,
`:8874 := 37`), not names of live definitions. The docstring at `:8832-8844`
states the trap explicitly: a historical constant that names a live definition
silently tracks the live route and rewrites history on the next recharge.

Disposition: evidence complete. NOT closed unilaterally; coordinator acceptance
required.

### THE SLACK ARTIFACT IS DELETED

`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_of_size_ge_four_of_bounded`
no longer exists as a declaration. `InteriorDirectory.lean:5541-5555` carries a
tombstone recording that it was DELETED rather than weakened, and why its first
conjunct (`route <= 30`) became false. Verified by search: the identifier
survives only in prose and in the historical WIP patch, in no `theorem` line.

### REQ-B7-07 - the vocabulary theorem holds over the AMENDED object

`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
(`SuccinctFinalRAM.lean:9708`) re-elaborated over the amended route in the
`c45e62c` build; `#print axioms` `[propext, Classical.choice, Quot.sound]`.
The new level events are `readWord`, since the theorem quantifies over the
whole-query trace which now contains them.

### W19 provenance - carried by the EXISTING constructor, no new segment

The charged level read is emitted inside
`concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural`,
which is precisely the object the existing `ReviewerProducerReadPath.lcaInterior`
constructor is stated over (`SuccinctFinalRAM.lean:5397-5401`). It is discharged
at `:5543` and consumed at `:6138`. No new constructor and no new segment were
needed, and `canonical_segments_complete` still reads `segment < 23`
(`SuccinctFinalModelAdequacy.lean:116`).

### CHK-04 - six of eight interior windows moved; the two that did not CANNOT

Harness exit 0, `canonicalBound=210` on every window, all windows agree with
reference semantics. Deltas against the session-2 baseline:

    generated-64      [0,64)  116 -> 118   [7,39)  126 -> 128
    zigzag-128        [0,128)  92 ->  93   [17,97)  96 ->  97
    generated-128-alt [0,128)  93 ->  94   [15,96)  95 ->  96
    tie-boundary n=6  [0,6)    76 ->  76   [1,5)    72 ->  72   (UNMOVED)

The tie-boundary fixture has `blockCount=2` (probed), so a crossBlock query has
no block strictly between its two endpoint blocks; the interior range-min is
invoked with `count=0` and takes the `Costed.pure` branch. Probed interior
costs: `count=0` costs 0, `count=1` and `count=2` cost 18 on both that shape and
`generated-64`. The charged level read lives inside the two-span computation,
which `count=0` never reaches, so those two windows carried zero interior reads
before AND after the swap.

The row's stated rationale - "windows identical to baseline would mean the store
grew and nothing reads it" - is therefore DISPROVEN as a reading of these two
rows: the store is read on every window whose fixture has `blockCount >= 3`.
But the row's literal window list names `76` and `72`, which did not move.

Disposition: CHK-04 REMAINS OPEN. It is not closed here and the row is NOT
weakened. The coordinator should rule on whether to amend the window list to
exclude the `blockCount=2` fixture, on the probe evidence above.

### Verification rows - as observed at `c45e62c`

CHK-01 `lake build RMQ RMQPaper RMQExamples` exit 0. CHK-03
`headline_axiom_check` exit 0, zero `ofReduceBool`/`sorryAx`. CHK-05 hygiene and
native_decide scans ZERO hits. CHK-06 `git diff --check` exit 0 on the working
tree; `f6564ec..HEAD` exit 2 hitting ONLY the committed `.patch` (documented
structural property). CHK-07 `design_decision_check.ps1 -Strict -Base f6564ec`
exit 0, 24 files. CHK-08 `claim_drift_scan.ps1` exit 0 (721 hits, 0 strict
failures) and `paper_topology_lint.ps1` PASS. CHK-02 NOT run per the delegation.

KNOWN RED and externally owned: `lake exe rmq_succinct_classic_validate` fails at
elaboration on the a07-owned fixture `singletonRepeatedEqualReadPositionsOK`
(`Validation/SuccinctClassic.lean:253`), which the delegation ring-fenced. Not
caused by, and not repaired by, this rung.

## Evidence at session 11 (B7-11): CHK-04 discharged on a widened observation set

Appended per the matrix's own rule that after freezing only evidence, status and
coordinator-approved amendments may change. NO REQUIREMENT WORDING IS EDITED. No
row is weakened. No fixture was removed.

Coordinator ruling implemented (relayed in the B7-11 delegation): session 10
asked whether to amend CHK-04's window list to exclude the `blockCount = 2`
`tie-boundary` fixture. The ruling DECLINED that and required ADDING a
tie-boundary fixture with `blockCount >= 3` instead, on two grounds: excluding a
fixture because it did not move inverts the purpose of an anti-vacuity row, and
the probe had independently revealed that leftmost tie-breaking WITH A
PARTICIPATING INTERIOR was untested. CHK-04's requirement text is therefore
unchanged and the `blockCount = 2` fixture is retained.

### The added fixture, and the checked reason it reaches the interior

`tie-boundary-live-interior` (n=24, `base=5`, `blockSize=10`, `blockCount=4`) in
`RMQ/Validation/SuccinctClassicCostHarness.lean`. The interior invocation
condition is read off the live route rather than inferred from size:
`canonicalCrossBlockCloseCostedWithRankSeed`
(`RelativeRmmMacro/ConcreteDirectoryRAM.lean:2336-2340`) enters
`(canonicalRelativeRmmInteriorDirectory shape).rangeMinCosted (leftBlock + 1)
(rightBlock - leftBlock - 1)` only when `leftBlock + 1 < rightBlock`. Probed:

    [0,24)  leftBlock=0 rightBlock=4 interiorLive=true  count=3 interiorCost=18
    [4,20)  leftBlock=1 rightBlock=4 interiorLive=true  count=2 interiorCost=18
    [10,20) leftBlock=2 rightBlock=4 interiorLive=true  count=1 interiorCost=18
    [11,12) leftBlock=2 rightBlock=2 interiorLive=false count=0 interiorCost=0

The interior is LOAD-BEARING on this fixture, not merely live: the minimum value
`4` occurs only at indices 5, 7, 9, 11, 13, 16, 18, all of which lie in interior
blocks 1-3, while both fringe blocks (indices 0-3 and 19-23) contain no minimum.
The leftmost-tie answer for `[0,24)` is index 5 (close 11, block 1), so the
answer is decided by the interior range-min breaking ties across blocks 1, 2 and
3. This is the coverage gap the ruling identified, and it is now closed.

### CHK-04 - evidence obtained

Both sides measured in this session rather than inherited: a detached scratch
worktree at the pre-swap commit `714fb4a` received the identical fixture, and
both harnesses were run. Both exit 0, both report "all reported windows agree
with reference List Int RMQ semantics", and `canonicalBound=210` /
`canonicalBoundIs210=true` on all 21 windows on both sides - so the guards are
consistent with the DERIVED literal.

    fixture (blockCount)             window    route      cnt  before after delta
    tiny-leftmost-ties     n=5  (1)  [0,5)     crossBlock   0     68    68     0
                                     [2,4)     sameBlock    -     57    57     0
                                     [1,1)     invalid      -      0     0     0
                                     [2,1)     invalid      -      0     0     0
                                     [0,6)     invalid      -      0     0     0
    tie-boundary           n=6  (2)  [0,6)     crossBlock   0     76    76     0
                                     [1,5)     crossBlock   0     72    72     0
                                     [2,3)     sameBlock    -     54    54     0
    tie-boundary-live-     n=24 (4)  [0,24)    crossBlock   3    112   114    +2
      interior  (NEW)                [4,20)    crossBlock   2    107   109    +2
                                     [10,20)   crossBlock   1    105   107    +2
                                     [11,12)   sameBlock    0     73    73     0
    generated-64           n=64 (9)  [0,64)    crossBlock   8    116   118    +2
                                     [7,39)    crossBlock   3    126   128    +2
                                     [31,32)   sameBlock    -     62    62     0
    zigzag-128            n=128 (16) [0,128)   crossBlock  14     92    93    +1
                                     [17,97)   crossBlock   9     96    97    +1
                                     [64,65)   sameBlock    -     57    57     0
    generated-128-alt     n=128 (16) [0,128)   crossBlock  14     93    94    +1
                                     [15,96)   crossBlock  10     95    96    +1
                                     [63,64)   sameBlock    -     57    57     0

ACCOUNTING CORRECTION. Session 10's table listed eight crossBlock and four
sameBlock windows; it omitted the `tiny-leftmost-ties` fixture entirely. The
true pre-existing counts are NINE crossBlock and FIVE sameBlock. The omission
was in the write-up, not the harness. The nine pre-existing crossBlock and five
sameBlock "before" values above reproduce session 10's recorded baseline
exactly, so that baseline is corroborated by independent measurement.

ANTI-VACUITY, sharper than the row requires. The set of windows that MOVED is
EXACTLY the set whose interior is invoked with `count > 0`: all nine such
windows moved, and all twelve windows with no live interior (three crossBlock at
`count = 0`, five sameBlock, three invalid, one sameBlock in the new fixture)
did not. No window falls on the wrong side of that partition. The row's stated
rationale - "windows identical to baseline would mean the store grew and nothing
reads it" - is answered in both directions: growth WITH reads is observed on
nine windows including three tie-boundary ones, and the twelve unmoved windows
are the ones the route provably never charges.

The `blockCount = 2` fixture is RETAINED and its stability is coverage, not a
defect: it exercises the zero-interior path, where the interior range-min is
never entered and the answer comes from the fringe decoders alone. A charged
read added inside the two-span computation MUST NOT change the cost of a route
that never reaches it; had those windows moved, that would have been the defect.

Store growth is independent of window movement and is observed on every shape:
`payloadBits` before -> after, tiny 541->616, tie n=6 577->652, new n=24
1871->2096, gen64 4635->5103, zigzag 10781->11384, gen128alt 10781->11384.

Disposition: CHK-04 evidence complete, on the row's unamended wording. NOT
closed unilaterally; coordinator acceptance required.

### Verification rows re-observed at the B7-11 candidate state

Re-run in this session rather than inherited from session 10; see the B7-11
verification ledger in `B7_WORKLOG.md` for the pasted decisive lines.

## B7-R1 repair contract (frozen before repair implementation)

Worker: B7-R1. Branch: `codex/b7-charged-sparse-level-r1`. Exact repair base:
`55e2b9ae3704a16129aaecc9c12f487aee5df12e`. Workflow governance:
`bd854edaa65944d5a7fa0fac5667e9572c370bbb`. This append-only section was
written before any B7-R1 Lean, trust, harness, hygiene-artifact, or public-
surface implementation edit. The original B7 requirement wording above is
unchanged. Evidence and status may move after this freeze; requirement text may
move only through an explicit coordinator amendment.

The named join is the accepted-route interior evaluator at an exact reachable
cost of `33`, consumed by the same-object whole-query algebra
`210 = 2*35 + (2*11 + 2*37 + 33) + 11`, together with the restored public
historical `328` identity, trust gates, replayable 21-window harness, committed
range hygiene, and every current surface registered by
`docs/internal/CLAIM_DRIFT_POLICY.json`.

The hard obligation is semantic attainment on the canonical reachable object,
not a syntactic observation about an upper-bound proof. Forbidden substitutes
include an upper bound presented as attainment, `352` relabeled as the old
`328` history, deleted trust coverage, an allowlisted whitespace failure, a
scanner-only surface audit, or conflation of payload, proof, model-cost, trace,
source, segment, allocation, runtime, or measured-time categories. Valid stop
conditions are exactly completion, a same-domain kernel-checked obstruction,
a genuine external-state blocker, or coordinator/user redirection.

### Frozen B7-R1 rows

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge planned | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-B7R1-TIGHTNESS-WITNESS` | prove semantic tightness/attainment if the frozen B7 claim is to remain. Require a checked canonical reachable accepted-route witness whose relevant interior execution has exact cost 33, or an equivalent lower-bound theorem showing 33 is necessary on the same object and domain. A theorem `cost <= 33`, use of `exact`, lack of `Nat.le_trans`, comments, or a harness cost for a different aggregate object do not close this row. Also prove/refute the old `cost <= 30` claim on the same reachable object. If the exact frozen tightness target is false, stop only with a kernel-checked obstruction or precise checked counterexample and request the coordinator's design choice; do not silently soften the contract. | Local rung + roadmap join | A theorem over one canonical reachable `canonicalRelativeRmmInteriorRangeMinCosted` execution concluding `.cost = 33`, plus a theorem concluding `not (.cost <= 30)` (or a same-object lower bound implying it). | Concrete canonical shape/query route -> interior `startBlock`/`count` -> `canonicalRelativeRmmInteriorRangeMinCosted` -> live interior cap -> named whole-query component algebra -> public `210`. | Compare P = exact cost `33` on the reachable accepted object with Q = only `cost <= 33`; attempt the old `cost <= 30` proposition on that identical object. | | Open |
| `REQ-B7R1-HISTORICAL-328-IDENTITY` | restore and pin the public historical identity `RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq : canonicalTransitionalQueryCost = 328` under the same public name. Do not relabel 352 as that history. If a live 352 compatibility bound remains useful, give it a distinct accurately named definition/theorem and migrate live consumers explicitly. Ensure future component changes cannot move the 328 identity. | Public/history | Checked theorem with the exact required public name and conclusion `= 328`, backed by literal-pinned historical components; any live `352` compatibility declaration has a distinct name and its consumers name it explicitly. | `RMQ.SuccinctClassic` public history -> validation/examples/headlines/topology/current policy. | Mutate a live component and confirm the `328` historical identity remains definitionally fixed; search all `352` consumers for accidental historical attribution. | | Open |
| `REQ-B7R1-WORDRAM-AXIOM-GATE` | update the stale WordRAM axiom inventory to exact live/historical theorem names and require `lake env lean scripts/wordram_axiom_check.lean` exit 0 on the final candidate. Do not delete coverage merely to make it green. | Trust gate | The inventory names the live `210` weighted-trace theorem and all retained historical/public anchors; the exact command exits `0`. | Source theorem inventory -> WordRAM trust packet. | Replace the stale removed name without dropping its semantic coverage; inspect the complete inventory diff. | | Open |
| `REQ-B7R1-COMMITTED-DIFF-HYGIENE` | make both `git diff --check` and `git diff --check f6564ec..HEAD` exit 0. Repair the tracked WIP patch artifact truthfully; do not waive or reinterpret the frozen command. | Hygiene | Working-tree and committed-range checks exit `0`, including `55e2b9ae..HEAD` and `f6564ec..HEAD`; the tracked WIP patch remains truthful and replayable or is explicitly retired by an accurate artifact update. | `docs/internal/B7_STEP2_WIP.patch` -> committed B7 history/evidence. | Inspect every reported whitespace location inside the patch rather than allowlisting the path. | | Open |
| `REQ-B7R1-CURRENT-PUBLIC-SURFACES` | derive the current surface inventory from the candidate's `docs/internal/CLAIM_DRIFT_POLICY.json`. Every registered live surface must consistently state the checked current facts: exact cost `210 = 2*35 + (2*11 + 2*37 + 33) + 11`; 22 physical reviewer sources over logical segments `0..22`, with BP roles 0 and 19 sharing one physical source; live segment 21 and rejected fresh segment 23; global trace positions 0 and 15 from instruction positions 0 and 1; and the canonical trace's separate strong public `readWord`-only theorem identity. Preserve accurate compatibility and frozen-history vocabulary. | Public/current surfaces | A machine-readable exact current-surface registry, a strict scan/regression, topology lint, and manual theorem-type/surface reread agree on every listed fact. | Live source theorems -> public headline aliases -> every registered Markdown surface. | Add stale `207`, `20-source`, fresh `21`, positions `0/12`, retired aliases, and weaker three-constructor vocabulary to current paths; production verdict must reject each while precise history remains allowed. | | Open |
| `INV-B7-CHARGED-SPARSE-LEVEL` | preserve actual table-read value dependence, positional trace equality, exact accepted-route erasure, one-word width on every reachable macro-crossing case, same counted store, provenance, capacity 218 to 527, and at-most `2*n + o(n)` without conflating allocation, payload, proof fields, or model ticks. | Inherited local + public | Recheck the exact source theorems and object chain for table read -> decoded level/span -> subsequent address/result; positional trace; erasure; reachable width; physical counted-store erasure/backing/provenance; 218/527 capacity bridge; public payload inequality and `LittleOLinear`. | Interior component store -> reviewer physical words -> canonical payload -> public profile/list-facing query. | Corrupt an actually read level cell and trace the returned candidate/route consequence; compare counted and executed object arguments; check tiny and macro-crossing boundaries. | | Open |
| `INV-B7-READWORD-ONLY` | preserve the exact source/public theorem that every event in the accepted whole-query trace is `isReadWord`; do not attribute that stronger conjunct to a weaker three-constructor theorem or capstone. | Inherited public | Quote the exact source theorem and strong public headline alias types; current prose attributes the strong claim only to that identity, while any three-constructor capstone clause is labeled weaker. | Whole-query trace -> source `..._readWord_only` -> `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`. | Present the weaker `readWord or wordRank or wordSelect` theorem as support; strict policy/topology and manual type audit must reject the substitution. | | Open |
| `INV-HALF-OPEN-LEFTMOST` | preserve guarded half-open leftmost `List Int` RMQ semantics, invalid-range behavior, and tie boundaries. | Inherited semantic | Exact list-facing theorem types plus the 21-window registry cover valid half-open leftmost answers, empty/reversed/out-of-bounds rejection, same-block, zero-interior, and load-bearing interior ties. | `scanWindow` specification -> guarded `queryCosted_exact`/invalid result -> harness expected answers. | Retain the leftmost-tie fixture with a participating interior and invalid-range controls; expected answers come from the independent List semantics. | | Open |
| `COMPLETE-B7R1-EVIDENCE` | one committed clean candidate contains the exact matrix mapping, four-part proof digestion, command ledger, and no claimed result from an earlier tree. | Completion | Append-only final-candidate evidence maps every original non-stretch and B7-R1 row to exact theorem/check output from the final commit; worktree is clean. | All local rows -> roadmap-node evidence packet; coordinator acceptance remains separate. | Invalidate/re-run transitive checks after any source/checker/public edit; do not reuse earlier-tree results as final evidence. | | Open |
| `REPLAY-EXACT-REGISTRY` | preserve a committed exact ordered registry for all 21 cost-harness windows, with expected answer, route class, pre/post swap cost disposition, and the leftmost-tie fixture; reject missing/duplicate IDs. | Executable replay | Typed ordered registry has exactly 21 unique stable IDs and records expected answer, route, pre-swap cost, post-swap cost, and disposition; validation rejects missing/duplicate IDs. | Registry -> default harness traversal and focused selector. | Remove or duplicate an ID and require registry validation to fail before query execution. | | Open |
| `REPLAY-SELECTOR-NONVACUITY` | any focused harness selector must execute exactly one requested registered window, reject unknown selectors, and make zero-case selection fail rather than pass vacuously. | Executable replay | A known ID reports exactly one case; unknown/empty selection exits nonzero; default mode reports exactly all 21 in registry order. | CLI selector -> exact registry entry -> query runner. | Known, unknown, and zero-selection controls with counted executed cases. | | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | every spawned Lean/Lake child has a positive evidence-based deadline, process-tree cleanup, failure classification, and final clean-tree restoration; do not discover timeouts by duplicating a quiet command. | Verification process | Command ledger records positive deadlines derived from prior runs, owned process-tree disposition on timeout, failure class, and final clean status. The committed Lean harness itself spawns no child process. | Verification orchestration -> final candidate evidence. | On any timeout inspect the surviving owned tree and artifacts; never launch an unchanged duplicate. | | Open |

The original non-stretch IDs that must receive final-candidate evidence remain
exactly `REQ-B7-00` through `REQ-B7-10`, `INV-STORE-IDENTITY`,
`INV-VALUE-DEPENDENCY`, `INV-NO-SYNTHETIC`, `INV-ALL-SIZE`,
`INV-PUBLIC-COMPOSITION`, and `CHK-01` through `CHK-08`. `STRETCH-01` keeps its
frozen status: stretch, attempted only after the assigned rung closes, and not
silently promoted into or removed from the non-stretch contract.

Local-rung evidence and roadmap-node evidence are distinct. B7-R1 may report
the local repair matrix complete only when every non-stretch original row and
every B7-R1 row is evidenced on one clean commit. The broader B7 roadmap-node
join remains coordinator-owned and additionally requires independent replay
and any designated blind exact-commit audit.

### B7-R1 verification coverage ledger (planned before verification)

Prior comparable timings: the governed preflight took 8.5s; focused file
elaboration historically completed within minutes; the prior aggregate
`lake build RMQ RMQPaper RMQExamples` completed successfully but no precise
duration was recorded, so its final timeout receives cold-cache margin. Only
one heavy Lean/Lake process may run in this worktree at a time, coordinated
under `Global\\RMQHeavyVerification` when overlap is possible.

| Role | Exact command | Changed paths / rows covered | Unique risk | Planned timeout |
| --- | --- | --- | --- | --- |
| Development-loop | `git diff --check` | Every edited path; `REQ-B7R1-COMMITTED-DIFF-HYGIENE` | Immediate whitespace defects in the working diff. | 30s |
| Development-loop | `lake env lean RMQ/Core/SuccinctClose/EndpointFringe/InteriorCandidate/InteriorDirectory.lean` | Tightness theorem; `REQ-B7R1-TIGHTNESS-WITNESS`, `INV-B7-CHARGED-SPARSE-LEVEL` | Exact witness elaboration on the live evaluator object. | 15m |
| Development-loop | `lake env lean RMQ/Core/SuccinctFinalRAM.lean` | Cost/public source chain; `REQ-B7R1-TIGHTNESS-WITNESS`, `INV-B7-READWORD-ONLY` | Direct consumer breakage after theorem/history changes. | 20m |
| Development-loop | `lake env lean RMQ/Core/SuccinctRMQClassic.lean` | Historical identity; `REQ-B7R1-HISTORICAL-328-IDENTITY`, half-open public consumers | Public-name/type migration errors. | 15m |
| Development-loop | `lake env lean scripts/wordram_axiom_check.lean` | Trust inventory; `REQ-B7R1-WORDRAM-AXIOM-GATE`, `CHK-02` | Stale names or untrusted axiom dependencies. | 15m |
| Development-loop | `lake exe rmq_succinct_classic_cost_harness` | Registry/default execution; `CHK-04`, all three `REPLAY-*`, `INV-HALF-OPEN-LEFTMOST` | Missing/duplicate windows, wrong answer/route/cost/disposition, default under-execution. | 20m |
| Development-loop | `lake exe rmq_succinct_classic_cost_harness -- --window <registered-id>` | `REPLAY-SELECTOR-NONVACUITY` | Focused selector executes other than exactly one case. | 10m |
| Development-loop | `lake exe rmq_succinct_classic_cost_harness -- --window __unknown_b7r1__` | `REPLAY-SELECTOR-NONVACUITY` | Unknown selector passes vacuously; expected nonzero. | 10m |
| Development-loop | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | Registered current surfaces; `REQ-B7R1-CURRENT-PUBLIC-SURFACES`, `CHK-08` | Stale current claims outside manually noticed files. | 5m |
| Development-loop | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_policy_regression.ps1` | Policy/scanner edits; current-surface anti-vacuity | Production-verdict/path/allowance bypass. | 10m |
| Development-loop | `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | Public symbols/topology; `REQ-B7R1-CURRENT-PUBLIC-SURFACES`, `CHK-08` | Dead/retired/compatibility symbols presented as current. | 10m |
| Final-required | `lake build RMQ RMQPaper RMQExamples` | All Lean/public/example edits; `CHK-01` | Aggregate import/consumer coherence. Run once on unchanged final tree. | 45m |
| Final-required | `lake env lean scripts/wordram_axiom_check.lean` | Final trust inventory; `CHK-02` | Exact live/historical trust surface. | 15m |
| Final-required | `lake env lean scripts/headline_axiom_check.lean` | Headline/public trust; `CHK-03` | Public theorem or literal migration not reflected in headline inventory. | 15m |
| Final-required | `lake exe rmq_succinct_classic_cost_harness` plus known/unknown focused-selector controls | All 21 windows; `CHK-04`, `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, `INV-HALF-OPEN-LEFTMOST` | Exact ordered coverage and non-vacuous selection on final tree. | 20m each; no concurrent heavy child |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | Every registry-derived current surface; `CHK-08` | Strict current/history vocabulary drift. | 5m |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_policy_regression.ps1` | Policy production verdict | Held-out/path/allowance anti-bypass. | 10m |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | Public topology; `CHK-08` | Documentary symbol resolution and current/compatibility roles. | 10m |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 55e2b9ae3704a16129aaecc9c12f487aee5df12e` | B7-R1 design/evidence edits; `CHK-07` | Missing design rationale for current branch changes. | 5m |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base f6564ec` | Original B7 committed range; `CHK-07` | Original-rung design record not visible over full range. | 5m |
| Final-required | `rg -n "\\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\\b|import Mathlib" RMQ lakefile.toml` | Lean hygiene; `REQ-B7-10`, `CHK-05` | Trust-footprint regression. Expected repository-baseline classification, no new hit. | 2m |
| Final-required | `rg -n "native_decide|Lean\\.ofReduceBool" RMQ` | Trust examples; `REQ-B7-10`, `CHK-05` | Unapproved native-decision trust shortcut. | 2m |
| Final-required | `git diff --check` | Working tree; `REQ-B7R1-COMMITTED-DIFF-HYGIENE`, `CHK-06` | Uncommitted whitespace. | 30s |
| Final-required | `git diff --check 55e2b9ae3704a16129aaecc9c12f487aee5df12e..HEAD` | B7-R1 committed range; `COMPLETE-B7R1-EVIDENCE` | Post-commit whitespace invisible to a clean worktree check. | 30s |
| Final-required | `git diff --check f6564ec..HEAD` | Full original B7 + repair range; `REQ-B7R1-COMMITTED-DIFF-HYGIENE`, `CHK-06` | Historical WIP patch whitespace remains committed. | 30s |
| Final-required | `git diff --name-only 55e2b9ae3704a16129aaecc9c12f487aee5df12e..HEAD` and `git status --short --branch` | Write scope / cleanliness; `COMPLETE-B7R1-EVIDENCE` | New path outside closed transitive scope or dirty final tree. | 30s |
| Conditional | `rg -n "native_decide|Lean\\.ofReduceBool" RMQ RMQExamples` | If trust/examples consumers change | Broader smoke-example trust regression. | 2m |

`scripts/gate.ps1`, `scripts/axiom_check.lean`, and the unrelated A07 validator
are explicitly excluded from B7-R1 final acceptance. A timeout is classified as
infrastructure/process evidence until the owned child, artifacts, and imports
are inspected; an unchanged quiet command is never duplicated.

### B7-R1 pre-implementation scope stop

`REQ-B7R1-CURRENT-PUBLIC-SURFACES` remains Open and blocks implementation under
the delegation's closed write scope. The candidate policy registers five stale
current paths outside that scope:

- `docs/PAPER_RELATED_WORK.md`;
- `docs/PUBLICATION_STRATEGY.md`;
- `docs/RELATED_WORK_AND_LIMITATIONS.md`;
- `docs/ROADMAP.md`;
- `docs/internal/RMQ_FINAL_ROADMAP.md`.

They state the old current `76` algebra and/or weaker three-constructor event
vocabulary. Correcting them is required by the exact row; removing or
allowlisting them would weaken the registry. `docs/ADD_PROVENANCE.md` is the
inverse discrepancy: it is in the granted write scope and contains stale
current facts, but is absent from the registry. The exact evidence and command
results are recorded in the B7-R1 worklog entry.

Disposition: `REQ-B7R1-CURRENT-PUBLIC-SURFACES` Open, every other B7-R1 row
Open, `COMPLETE-B7R1-EVIDENCE` Open. Coordinator authorization to add the five
paths, or an explicit contract amendment, is required before substantive repair
work resumes.

## B7-R2 governed continuation (frozen before repair implementation)

Worker B7-R2 continues the unchanged B7-R1 frozen rows on branch
`codex/b7-charged-sparse-level-r2` in
`C:\Users\poin\.codex\worktrees\25b6\RMQ`.  The exact base is the two-parent
join `e23875542995ca31404567cba5b128c9271e861a`, whose ordered parents are the
clean B7-R1 scope checkpoint `24a166c5959aa1cac52be6d0aeefb3e2811f056c`
and workflow governance `5fc02e5a8960c4cc5bacba4daa58cc8f4bd8a91f`.
The exact governed skill preflight passed before this section and before any
B7-R2 implementation edit.

The repaired prompt authorizes all 18 paths matched at the base by
`currentFactSurfacePathRegex`; therefore the B7-R1 scope blocker is removed.
No acceptance wording or ID changes.  The blocking contract is exactly the
original non-stretch rows `REQ-B7-00`--`REQ-B7-10`,
`INV-STORE-IDENTITY`, `INV-VALUE-DEPENDENCY`, `INV-NO-SYNTHETIC`,
`INV-ALL-SIZE`, `INV-PUBLIC-COMPOSITION`, `CHK-01`--`CHK-08`, together with
all B7-R1 rows from `REQ-B7R1-TIGHTNESS-WITNESS` through
`REPLAY-SUBPROCESS-DEADLINE`.  `STRETCH-01` remains explicitly deferred until
that non-stretch contract closes.

The join theorem is the same-object canonical interior statement
`canonicalRelativeRmmInteriorRangeMinCosted ... .cost = 33`, connected through
the canonical store-backed structural trace and the list-facing accepted query
to the live component algebra
`210 = 2*35 + (2*11 + 2*37 + 33) + 11`.  Its anti-vacuity challenge is the
identical object's proposition `cost <= 30`.  Separately,
`INV-VALUE-DEPENDENCY` retains its own frozen corruption challenge; the exact
cost witness cannot substitute for it.

Verification remains ordered from static/source reconstruction to the focused
interior theorem, direct public/history consumers, trust inventories, exact
21-window registry/default/known/unknown controls, strict public scans, then
the one final aggregate build on an unchanged tree.  Every spawned Lean/Lake
stage used for replay will run under a positive observed-runtime-based
deadline with an owned process, process-tree termination on timeout, explicit
timeout classification, `finally` cleanup/survivor inspection, and clean-tree
verification.  The Lean harness itself remains child-free.

### B7-R2 scope-blocker evidence (2026-07-19)

`REQ-B7R1-TIGHTNESS-WITNESS` has a kernel-checked implementation checkpoint on
the authorized tree: the source proves exact cost `33` and rejects `cost <= 30`
on the identical `(shape, startBlock, count)` object; the accepted structural
consumer pins the real query `[1704,3469)`, closes `3409/6937`, blocks
`142/289`, interior invocation `(143,146)`, and trace cost/length `33`. This is
checkpoint evidence only, not row closure, because the final candidate does
not yet exist.

Work must stop before `REQ-B7R1-HISTORICAL-328-IDENTITY` is edited. Its frozen
quantifier requires *every* live `352` declaration to have a distinct accurate
name and its consumers to name it explicitly. The following required direct
consumers are outside this task's authorized path set:

- `RMQ/Core/SuccinctFinalStoreParam.lean`:
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCostedWithStore_cost_le_of_footprint_global_canonicalTransitional`
  concludes against the live raw expression
  `3 * sparseDenseFalseSelectQueryCost + canonicalCompactBPCloseQueryCostWithRankSeed ... = 352`;
- `RMQ/Core/SuccinctFinalModelAdequacy.lean`:
  `concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_canonicalTransitional`
  re-exports that live `352` expression;
- `RMQ/Headlines/RMQCompatibility.lean`: the public declarations
  `succinctRMQCompatibility328WholeQueryGlobalWordTraceCostedCostLe`,
  `succinctRMQCompatibility328QueryCostEq`, and
  `succinctRMQCompatibility328FinalFullModelCostLeOfFootprintGlobal` currently
  attach `328` names/comments to live `352` propositions;
- `RMQ/Validation/SuccinctClassic.lean`: the checked historical guard still
  asserts `canonicalTransitionalQueryCost == 352`.

Restoring only
`RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq :
canonicalTransitionalQueryCost = 328` inside the authorized file would leave
those descendants mislabeled or ill-typed and would therefore violate the
same frozen row rather than close it. No implementation obstruction exists:
the required repair is to literal-pin historical `328`, introduce a distinct
live-compatibility-`352` definition/theorem, and migrate the four paths above.
That repair requires coordinator/user expansion of the write scope.

## B7-R3 governed continuation (frozen before repair implementation)

Worker `B7-R3` owns the local charged-sparse-level repair rung on branch
`codex/b7-charged-sparse-level-r3` in the fresh worktree
`C:\\Users\\poin\\Documents\\RMQ\\.worktrees\\b7-charged-sparse-level-r3`.
The exact base is the two-parent join
`14e38031a541bcaa2df8d67976078c76dbae975a`; its ordered parents are the
unaccepted implementation checkpoint
`16645c60792954b84ad588b56f5b56da720847df` and workflow governance
`986e8066f9b93f6576edd20e6d25e363eb029fa1`. The governed
`rmq-proof-sprint` preflight passed before this freeze and before any
implementation edit.

This continuation changes no acceptance ID, wording, quantifier, or object.
The frozen non-stretch contract remains `REQ-B7-00`--`REQ-B7-10`,
`INV-STORE-IDENTITY`, `INV-VALUE-DEPENDENCY`, `INV-NO-SYNTHETIC`,
`INV-ALL-SIZE`, `INV-PUBLIC-COMPOSITION`, `CHK-01`--`CHK-08`, and every
B7-R1 row from `REQ-B7R1-TIGHTNESS-WITNESS` through
`REPLAY-SUBPROCESS-DEADLINE`. `STRETCH-01` remains explicitly deferred.
The four R2-blocking consumers are now authorized:
`RMQ/Core/SuccinctFinalStoreParam.lean`,
`RMQ/Core/SuccinctFinalModelAdequacy.lean`,
`RMQ/Headlines/RMQCompatibility.lean`, and
`RMQ/Validation/SuccinctClassic.lean`.

The join target is one clean candidate carrying the canonical reachable
same-object source/store/accepted-query/structural-trace chain with exact cost
`33`. Its rejected predicate is `cost <= 30` on the identical execution;
neither a `<= 33` bound nor a different aggregate object is evidence. The
separate value-dependency corruption challenge remains independent. Historical
`canonicalTransitionalQueryCost = 328` is literal-pinned under its public name;
the live raw-expression value `352` receives a distinct accurate definition
and theorem, and every direct consumer is migrated explicitly.

The replay target is one typed ordered registry whose literal expected-ID list
contains exactly 21 unique IDs and whose entries freeze exact answer, route,
pre-cost, post-cost, and disposition. Default execution must run those 21 in
registry order; a known exact selector must execute exactly one case; unknown
and zero-match selectors must exit nonzero. Count-only checks and the empty
recursive base are not acceptance evidence. External verification stages use
positive observed-runtime-based deadlines and owned cleanup; the Lean harness
remains child-free.

### B7-R3 final-evidence ledger

All rows below are `Planned` until recorded against the final unchanged
candidate. Inherited checkpoint builds and prose are diagnostic only.

| Class | Exact command/evidence | Frozen rows / anti-vacuity | Deadline |
|---|---|---|---:|
| Development | focused `lake env lean` on each changed Lean source and its direct consumer | Exact propositions, composition chain, and typechecking | observed runtime plus cold-cache margin |
| Final | `lake build RMQ RMQPaper RMQExamples` once on the unchanged final tree | `CHK-01`--`CHK-04`, public composition | 45m |
| Final | `lake env lean scripts/wordram_axiom_check.lean` and `lake env lean scripts/headline_axiom_check.lean` | `REQ-B7R1-WORDRAM-AXIOM-GATE`, `CHK-05` | 20m each |
| Final | default harness plus known, unknown, and zero-match selector controls | `CHK-04`, `REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, `INV-HALF-OPEN-LEFTMOST` | 20m each |
| Final | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | all 18 registered current surfaces, `CHK-08` | 10m |
| Conditional | `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_policy_regression.ps1` iff policy changes | policy anti-bypass | 15m |
| Final | `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1` | topology and historical/live symbol roles | 15m |
| Final | strict design-decision checks with bases `14e38031a541bcaa2df8d67976078c76dbae975a` and `f6564ec` | `CHK-07`, original-rung history | 10m each |
| Final | hygiene scans required by `AGENTS.md` | `REQ-B7-10`, `CHK-05` | 5m |
| Final | `git diff --check`; `git diff --check 14e38031a541bcaa2df8d67976078c76dbae975a..HEAD`; `git diff --check f6564ec..HEAD` | `REQ-B7R1-COMMITTED-DIFF-HYGIENE`, `CHK-06` | 2m each |
| Final | exact changed-path inventory and clean `git status --short --branch` | closed write scope, `COMPLETE-B7R1-EVIDENCE` | 2m |

The aggregate gate, `scripts/axiom_check.lean`, and the unrelated A07 validator
remain excluded. A timeout is classified only after inspecting its owned
process tree, artifacts, prerequisites, and narrow failing surface; an
unchanged quiet command is never blindly repeated.

## B7-R3 final-candidate evidence reconstruction

This section is append-only evidence for the unchanged frozen rows. It does
not edit a requirement or record coordinator acceptance. The candidate commit
cannot contain its own hash or post-commit command results; the exact hash and
exact-commit certification ledger are therefore reported in the B7-R3 handoff
after this evidence packet is committed and the tree is clean.

### Exact proposition packets and object chains

The charged-table domain and decoded values are universal, not sampled:

```lean
bpSparseLevelDomain_covers :
  count <= bound -> count < bpSparseLevelDomain bound

bpSparseLevelCell_div :
  2 <= domain -> i < domain ->
    bpSparseLevelCell domain i / domain = Nat.log2 i

bpSparseLevelCell_mod :
  2 <= domain -> i < domain ->
    bpSparseLevelCell domain i % domain = bpSparseLogSpan i
```

`readCellCosted_erase_div` and `readCellCosted_erase_mod` lift those equalities
to the actual table read. The executed
`canonicalRelativeRmmMachineLocalTwoSpanCandidateComputation_refines` and
global twin equate the canonical flat-store computations to the accepted
costed two-span objects. The dispatcher then reaches
`canonicalRelativeRmmInteriorRangeMinCostedWithStore_erase_exact`, whose exact
conclusion is the accepted pair
`some (bpRangeMinExcess shape blockSize startBlock count,
bpRangeArgMinPrefixPos shape blockSize startBlock count)`.

The tightness packet is one composition chain, not a conjunction of sibling
objects:

```text
canonical size-3469 right-spine shape and List representative
  -> valid List window [1704,3469), closes 3409 and 6937
  -> endpoint blocks 142 and 289
  -> accepted middle invocation (startBlock,count)=(143,146)
  -> canonical component-store execution
  -> exact interior cost = 33 and footprint length = 33
  -> segment-20 structural trace cost = trace.length = 33
  -> Not (cost <= 30) on that same trace
```

The source propositions are
`canonicalRelativeRmmInteriorCost33Witness_exact`,
`canonicalRelativeRmmInteriorCost33Witness_not_cost_le_thirty`,
`canonicalRelativeRmmInteriorCost33Witness_store_exact`,
`canonicalRelativeRmmInteriorCost33Witness_footprint_length`, and
`canonicalRelativeRmmInteriorCost33Witness_store_erase_exact`. The direct
accepted consumer propositions are
`concreteBPNativeB7Cost33Witness_query_geometry`,
`concreteBPNativeB7Cost33Witness_acceptedMiddleInvocation`, and
`concreteBPNativeB7Cost33Witness_interiorTrace_exact`.

The value-dependency packet is the separate proposition
`canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate`.
For the identical canonical shape and `(0,1)` query it concludes both exact
read memberships, the canonical accepted `some` result, the dropped-store
`none` result, and inequality of those two returned `Option (Nat x Nat)`
values. The two stores differ only at the one-word local-level address
`offsets.localLevel + 1`. Thus P and Q have identical shape, query, guards, and
quantifiers; Q is rejected at the returned value rather than only in a log.

Store/public composition is literal:

```text
local/global charged level tables
  -> canonicalRelativeRmmInteriorComponentStore
  -> canonicalRelativeRmmInteriorComponentStore_flattens_payload
  -> canonicalClose reviewer source
  -> concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases
  -> concreteBPNativeSuccinctRMQCanonicalReviewerPayload
  -> SuccinctClassic.buildPayload
  -> SuccinctClassic.buildPayload_length and overhead_littleO
```

The charged level part satisfies
`canonicalRelativeRmmInteriorLevelPartOverhead_littleO`; the complete raw
directory satisfies
`canonicalRelativeRmmInteriorRawPayloadOverhead_littleO` and
`canonicalRelativeRmmInteriorRawPayloadOverhead_le_linear : ... <=
527*(n+1)`; the public profile retains exactly
`buildPayload.length <= 2*n + overhead n` with `LittleOLinear overhead`.
Amendment 1 remains authoritative: the level words extend the existing
canonical-close component/source rather than minting a synthetic segment.

Current cost/history propositions are disjoint:

```lean
concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq :
  concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost = 210

RMQ.SuccinctClassic.canonicalTransitionalQueryCost_eq :
  canonicalTransitionalQueryCost = 328

RMQ.SuccinctClassic.liveCompatibilityQueryCost_eq :
  liveCompatibilityQueryCost = 352
```

The first theorem is `rfl` over
`2*35 + (2*11 + 2*37 + 33) + 11`. Historical `328` is literal-pinned and is
therefore definitionally independent of every live component. The live raw
expression is named `352` at the source, store-parametric, adequacy, classic,
headline, validation, example, topology, and trust consumers. No checked
`Compatibility328` proposition mentions the live raw expression.

The current physical/public surface reconstructs these checked facts:

- `concreteBPNativeSuccinctRMQReviewerPhysicalSources_length = 22` and
  `Nodup`; logical segment map exactly `0..22`; segments `0` and `19` resolve
  to the single `.sharedBPCode` source;
- segment `21` is live and the counterfactual source at fresh segment `23`
  has no operational producer;
- repeated equal successful events retain distinct indexed receipts at
  global positions `0` and `15`, arising from instruction positions `0` and
  `1`;
- `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
  concludes `forall event, event in trace -> event.isReadWord`; the exact
  public alias is
  `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly`.

The current-surface inventory is derived from
`docs/internal/CLAIM_DRIFT_POLICY.json.currentFactSurfacePathRegex` and has
exactly 18 paths: `README.md`, `artifact/CLAIMS.md`, `artifact/README.md`,
`docs/FAMILY_SUMMARY.md`, `docs/PAPER_CLAIM_CORRESPONDENCE.md`,
`docs/PAPER_MAIN_THEOREM.md`, `docs/PAPER_MODEL_ADEQUACY.md`,
`docs/PAPER_RELATED_WORK.md`, `docs/PAPER_THEOREM_MAP.md`,
`docs/PUBLICATION_STRATEGY.md`, `docs/RELATED_WORK_AND_LIMITATIONS.md`,
`docs/ROADMAP.md`, `docs/TRUST_AUDIT_PACKET.md`, `docs/WHAT_IS_PROVED.md`,
`docs/WORD_RAM_REVIEW_PACKET.md`,
`docs/digests/PROJECT_DIGESTION_CURRENT.md`,
`docs/internal/CLAIM_DRIFT_POLICY.md`, and
`docs/internal/RMQ_FINAL_ROADMAP.md`. `docs/ADD_PROVENANCE.md` is additionally
repaired as an explicitly scoped provenance dependency outside that
regex-based count.

### Every frozen non-stretch row mapped on the candidate content

| Frozen row | Exact candidate evidence and rejected challenge | Candidate disposition |
|---|---|---|
| `REQ-B7-00` | DD-20260718-012 is in ancestry before the mechanism implementation. It rejects a pre-span free read by read order: the runtime level forms the later sparse-cell address; mechanisms 2/4 are rejected by the recorded checked arithmetic/size facts. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-01` | `bpSparseLevelDomain_covers`; two separate local/global instantiations; `canonicalRelativeRmmInteriorLevelPartOverhead_littleO`; raw capacity `<=527*(n+1)`. Missing/duplicate-domain Q cannot discharge the executed-read refinement. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-02` | Exact division and remainder projections, their `readCellCosted` lifts, local/global executed-computation refinement, and dispatcher/store erasure exactness give the full returned `Option (Nat x Nat)` at every reachable site. Sample-only, level-only, and added-readiness Qs do not match these universal theorem types. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-03` | `canonicalRelativeRmmInteriorRangeMinTraceResultAtSegment_refines`, `_matchesReadStore`, and `_no_syntheticCostOnlyPrimitive`, plus the AllSizeStructural and WithStore `_eq_of_agree`/`_refines_of_agree`/`_store_parametric`/`_matchesReadStore` twins, map execution-ordered `FlatStoreExecution.reads` positionally. The decisive theorem records the level address in both actual read lists. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-04` | Per Amendment 1, no new segment/source: the level table extends the counted canonical-close component. Component-store flattening, reviewer physical erasure/capacity, counted-source producer may-path, occurrence/value provenance, live segment `21`, and fresh `23` rejection remain in the same adequacy/public packet. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-05` | The live literal is `rfl`-derived `210`; exact same-object cost `33` and rejected `<=30` prove the three-unit movement is executed, not slack. Frozen `207` remains historical. Mutating the live interior component breaks the `=210` derivation but cannot move historical `207`. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-06` | Executed level words are in the flattened counted store; level/raw/public overheads are `LittleOLinear`; public payload theorem retains exactly `<=2*n+overhead n`; all-size capacity path includes the `218 -> 527` directory-envelope migration. The two-payload Q fails the literal erasure/object chain. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-07` | The source theorem universally concludes `isReadWord` on the amended whole-query trace; the exact headline alias points to it. The weaker three-constructor theorem has a different type and is labeled compatibility-only. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7-08` | `docs/PAPER_MODEL_ADEQUACY.md` names the charged sparse-level leg, exact bridge lemmas/caps, representation-versus-algorithmic-work distinction, model categories, and residual assumptions; strict claim/topology checks are the executable consumers. | Evidence complete subject to final exact-commit scans. |
| `REQ-B7-09` | R3 is one atomic final candidate over the joined checkpoint: source, consumers, trust, replay, docs, and hygiene artifact commit together; no counted-but-unread source is introduced. The single final aggregate build certifies the committed tree. | Evidence complete subject to final exact-commit aggregate. |
| `REQ-B7-10` | WordRAM inventory retains and extends semantic coverage; forbidden-token/native-decision scans, three diff checks, two strict decision checks, strict claim scan, and topology lint are run on the exact candidate. Forbidden aggregate `gate.ps1`/`axiom_check.lean` remain untouched/unrun. | Evidence complete subject to final exact-commit commands. |
| `INV-STORE-IDENTITY` | The object chain above is exact: the same local/global level-table terms feed both `machineReadComputationAt` and `canonicalRelativeRmmInteriorComponentStore`, whose erasure reaches `buildPayload`. | Evidence complete; two-payload challenge rejected. |
| `INV-VALUE-DEPENDENCY` | `canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate` places the one changed word in both actual read logs and proves canonical `some` versus dropped `none` on the identical shape/query. | Evidence complete; trace-only challenge rejected. |
| `INV-NO-SYNTHETIC` | Interior and whole-query `_no_syntheticCostOnlyPrimitive` theorems plus the strong readWord-only theorem classify every charged unit as a supplied-store read; the decisive read value changes the returned value. | Evidence complete; decorative-read challenge rejected. |
| `INV-ALL-SIZE` | Domain/projection/refinement theorems quantify over all shapes/counts under route bounds, including cell `0`; no `Ready`/threshold dispatch is added. Empty/invalid public queries remain guarded pure `none`. | Evidence complete; hidden-threshold challenge rejected. |
| `INV-PUBLIC-COMPOSITION` | `listInt_two_n_plus_o_constant_query_profile` combines `overhead_littleO`, the same `buildPayload`, guarded query cost, invalid semantics, exact answer, and leftmost result; downstream adequacy/headline consumers use the amended execution. | Evidence complete; sibling-object conjunction challenge rejected. |
| `CHK-01` | Exact command: `lake build RMQ RMQPaper RMQExamples`, once after the content/ledger freeze and commit. | Post-commit certification recorded in handoff. |
| `CHK-02` | `lake env lean scripts/wordram_axiom_check.lean` includes the new corruption theorem, exact 33 chain, 210, historical 328, live 352, and strong read-only surface; stabilized-source run exited 0. | Evidence complete; repeated post-commit only if required by source change. |
| `CHK-03` | Exact command: `lake env lean scripts/headline_axiom_check.lean` after the aggregate supplies the top-level olean. | Post-commit certification recorded in handoff. |
| `CHK-04` | Typed 21-entry exact registry; default, known exact ID, unknown ID, and zero-match fixture controls. A timeout caused by later-started external builds is classified and cleaned in `B7_WORKLOG.md`; successful exact controls are required before commit. | Evidence complete subject to successful contention-free replay. |
| `CHK-05` | Required forbidden-token scan and `native_decide|Lean.ofReduceBool` scan over the final candidate. | Post-content-freeze results recorded below/in handoff. |
| `CHK-06` | Working diff, `14e38031..HEAD`, and `f6564ec..HEAD` exact diff checks. The WIP artifact is a real zero-context nine-path `65c6ab3..c45e62c` patch, replayed with native `patch.exe` in an isolated extraction and verified by nine exact target blob hashes; skip-only `git apply` output was rejected as vacuous. | Evidence complete subject to post-commit exact ranges. |
| `CHK-07` | Strict decision checks against exact base `14e38031...` and original `f6564ec`; DD-20260719-002/003 and WDD-20260719-008 cover the semantic/process choices. | Evidence complete subject to final rerun. |
| `CHK-08` | Strict registry-derived claim scan (policy regression because the policy changed) and topology lint distinguish current 210, historical 328, live 352, and the strong read-only identity. | Evidence complete subject to final rerun. |
| `REQ-B7R1-TIGHTNESS-WITNESS` | Exact source/store/accepted-query/structural-trace chain above concludes `cost=33`, `trace.length=33`, and `Not(cost<=30)` on the identical reachable object. A bare `<=33` theorem is not cited. | Evidence complete; coordinator acceptance pending. |
| `REQ-B7R1-HISTORICAL-328-IDENTITY` | Required public name concludes literal `=328`; live raw expression has distinct `liveCompatibilityQueryCost=352`; every inventoried direct consumer is migrated. | Evidence complete; mislabeled-352 challenge rejected. |
| `REQ-B7R1-WORDRAM-AXIOM-GATE` | Curated inventory retains live/historical/public coverage and adds the decisive value theorem; command exits 0. No check was deleted to obtain green. | Evidence complete. |
| `REQ-B7R1-COMMITTED-DIFF-HYGIENE` | Truthful WIP replay plus all exact diff checks. The original malformed-whitespace artifact is repaired rather than waived or allowlisted. | Evidence complete subject to post-commit exact ranges. |
| `REQ-B7R1-CURRENT-PUBLIC-SURFACES` | Exact 18-path regex inventory above plus repaired `ADD_PROVENANCE`; checked current algebra/source/segment/position/read-only facts; precise frozen history allowed only in historical context. | Evidence complete subject to final strict scan/lint. |
| `INV-B7-CHARGED-SPARSE-LEVEL` | Projection, executed refinement, positional reads, exact erasure, one-word crossing width, same store, producer packet, 527 capacity, and public little-o chain are all named above; the decisive corruption closes the returned-value subchallenge. | Evidence complete; coordinator acceptance pending. |
| `INV-B7-READWORD-ONLY` | Exact source theorem and exact headline alias are separate from the weaker compatibility vocabulary on every current surface. | Evidence complete. |
| `INV-HALF-OPEN-LEFTMOST` | `queryCosted_exact`, `queryCosted_leftmost`, and `queryCosted_invalid` retain guarded half-open List semantics. Registry entries pin empty, reversed, out-of-bounds, singleton, threshold/tie, and live-interior leftmost cases against independent `expectedAnswer`. | Evidence complete subject to final replay. |
| `COMPLETE-B7R1-EVIDENCE` | This append-only map, the command ledger, the four-part proof digestion in `B7_WORKLOG.md`, one staged/committed intended path set, exact post-commit checks, and clean status form the candidate packet. | Candidate completion only; roadmap/coordinator audit remains open. |
| `REPLAY-EXACT-REGISTRY` | `replayRegistry`, `expectedRegistryIds`, and `expectedPreRepairCosts` jointly require exactly 21 ordered unique IDs and exact answer/route/pre/post/disposition fields before execution. Removing or duplicating an ID makes structure validation fail. | Evidence complete subject to final replay. |
| `REPLAY-SELECTOR-NONVACUITY` | Default selects registry; known `interior-full-leftmost` must report `1/1`; unknown case and zero-match fixture must exit `4`; selection count `0` is rejected before success. | Evidence complete subject to final replay. |
| `REPLAY-SUBPROCESS-DEADLINE` | Harness is child-free. External stages use positive deadlines; the 1204.1s contention timeout was inspected, classified, cleaned by exact owned PIDs, and not blindly duplicated. Final status verifies no survivor/scratch path. | Evidence complete; final clean check pending. |

`STRETCH-01` remains explicitly deferred. Nothing in the candidate claims a
complete mechanized inventory of all remaining uncharged computation, and its
absence does not weaken or substitute for any non-stretch row.

## B7-R3 late replay-runtime amendment and exact control evidence

This append-only refinement records the in-scope repair found by the final
replay; it does not alter any frozen row. The exact proposition of
`canonicalRelativeRmmInteriorCost33LocalLevelDrop_changes_returned_candidate`
is unchanged. Its size-3469 address and dropped store now occur as explicit
theorem-local lets instead of closed executable definitions, so the checked
same-object P/Q challenge is proof-erased and cannot contaminate an importing
executable's wall-clock startup. DD-20260719-004 records that category
separation.

The exact registry now reuses one `PreparedInput` per typed `FixtureId` while
recursing over the same ordered `List ReplayCase`. Its success predicate also
requires `preparedCache.length` to equal the number of distinct selected
fixture IDs. WDD-20260719-009 rejects deadline inflation, case removal, and
untyped/result-based caching.

Measured anti-vacuity on the repaired content:

- default: exit 0 in 29.158s; exactly 21 selected and 21 executed cases in
  registry order; exactly six expected and six actual prepared fixtures;
- known `interior-full-leftmost`: exit 0 in 282ms; exactly one selected and
  executed case and one prepared fixture; `some 5`, cross-block, `112 -> 114`;
- unknown ID: exit 4 in 142ms;
- zero-match fixture: exit 4 in 143ms.

Every default entry reported exact answer, independent List answer, route,
post-cost, disposition, and `<=210` bound success. Thus `CHK-04`,
`REPLAY-EXACT-REGISTRY`, `REPLAY-SELECTOR-NONVACUITY`, and the executable part
of `INV-HALF-OPEN-LEFTMOST` are closed on the repaired content. Timeout
anti-vacuity is also concrete: every expired stage was inspected, its exact
owned PID tree was cleaned, no external tree was touched, and no unchanged
opaque command was repeated. A shape-only size-5 probe isolated the closed
witness initialization (>120.034s before theorem-localization, 2.135s after),
and the final successful default used the resulting repaired binary.

The amended source invalidates the first checkpoint's broad-build/trust
results as final-candidate evidence. `CHK-01`--`CHK-03`, strict public and
decision gates, exact diff ranges, and clean status remain subject to the new
post-commit certification ledger reported in the handoff. `STRETCH-01` remains
explicitly deferred.

## B7-R4 governed semantic-repair contract (frozen before implementation)

Worker `B7-R4` owns only the two proposition-level occurrence/reachability
repairs on branch `codex/b7-charged-sparse-level-r4` in
`C:\\Users\\poin\\.codex\\worktrees\\91bc\\RMQ`. The exact base is the
two-parent ordered join `07b0dda3878574070ae7ab0332cc61658e56f67a`, whose
parents are rejected B7-R3 candidate
`879edb0a3c61d44a7a20cee0026e96a121666791` and workflow governance
`7e0e6089251147b02365bc5603ebd2347902018f`. The governed
`rmq-proof-sprint` preflight passed before this freeze with the complete
runtime RMQ skill catalog. This section is the first R4 repository edit.

The join theorem is the actual accepted whole/list query on the canonical
size-3469 input at `[1704,3469)`, whose folded whole-query controller reaches
the LCA instruction with closes `3409` and `6937`, whose real cross-block
middle conditional selects the identical segment-20 structural interior trace
at `(143,146)`, and whose same component has cost and trace length `33` and
rejects `cost <= 30`. The independent occurrence join is the actual singleton
`([7] : List Int)` query `[0,1)`, with the same successful segment-`1`,
index-`0` select-directory read at global positions `0` and `15`, produced by
distinct select-close instructions at instruction positions `0` and `1`,
retaining exact folded pre-states, local positions, `ProducesEventAt`
witnesses, and occurrence receipts. Literal evaluation after the initial
freeze confirmed that the separate segment-`22` select-chunk read occurs at
positions `14` and `29`; the requested `0`/`15` constants therefore cannot
refer to that compatibility witness. This correction fixes more constants
and does not weaken the governed requirement.

The downstream consumers are independent exact-type checks through
`RMQ.SuccinctClassic`, `RMQ.Headlines.RMQ`, validation, examples, and both
curated trust inventories. A component-only evaluator, a separately rebuilt
`if`, existentially hidden positions, `List.Mem`, or proof-body coincidence is
not evidence. The valid stop conditions are closure of every row below, an
identical-object kernel-checked obstruction requiring a coordinator choice, a
genuine external blocker, or explicit redirection. Public prose and document
topology are outside this rung; no current-fact claim is changed.

The source/public theorem signatures and shared evidence records are causally
coupled, so there is no independent write leaf with a separate consumer.
B7-R4 therefore proceeds single-owner without subagents.

### Frozen B7-R4 rows

| ID | Exact frozen requirement | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge planned | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| `REQ-B7R4-WHOLE-QUERY-COST33-REACHABILITY` | prove on the canonical witness input and valid half-open query `[1704,3469)` that the actual accepted whole-query/list-facing execution invokes or contains the identical segment-20 structural interior trace at `(143,146)`. The checked proposition must connect the real query closes and LCA conditional to `concreteBPRelativeRmmInteriorRangeMinTraceResultAtSegmentsAllSizeStructural ... 143 146`, and preserve cost `33`, trace length `33`, and `Not (cost <= 30)` on that identical component. A separately rebuilt `if`, isolated component theorem, bare `cost <= 33`, or proof-body derivation is insufficient. It need not prove the total whole-query cost equals 210. | Local rung + actual public query | One checked proposition retains `ValidRange witnessInput 1704 3469`, `Cartesian.shape witnessInput = witnessShape`, the guarded list trace equal to the actual whole-query global trace, the two real select-close results `3409`/`6937`, the folded LCA instruction at program position `2`, its actual evaluator branch, the branch's exact cross-block middle conditional at `(143,146)`, and the identical interior trace's `toCosted.cost = 33`, `trace.length = 33`, and `Not (cost <= 30)`. | `SuccinctClose` witness input/shape -> `SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryProgram` folded on `1704,3469` -> position-2 `.lcaClose` pre-state with closes `3409,6937` -> `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural` -> its actual middle conditional -> segment-20 trace `(143,146)` -> `SuccinctClassic.queryTraceResult` valid guard -> headline and exact-type consumers. | Accepted predicate P is the full conjunction on the actual guarded list query, folded program, and identical interior trace. Q1 replaces the whole-query object with the isolated interior evaluator; Q2 changes the invocation to a pair other than `(143,146)`; Q3 keeps only `cost <= 33`. The independent expected-type consumers must reject Q1/Q2/Q3. | | Open |
| `REQ-B7R4-CONCRETE-POSITION-INSTRUCTION-IDENTITY` | for the actual singleton `([7] : List Int)` query `[0,1)`, expose one checked proposition that pins the two equal successful reads at global trace positions `0` and `15`, pins their producing instruction positions `0` and `1`, proves the producing instructions are the two distinct select-close instructions, and preserves the complete `ProducesEventAt`/folded-state/local-position/receipt information for the same event. The constants may not remain only inside a private proof or be erased behind existential receipts. | Local occurrence rung | One exported proposition existentially chooses only the successful word and literally fixes segment `1`, index `0`, global positions `0`/`15`, instruction positions `0`/`1`, local position `0` for both, exact left/right select-close instructions, `WholeQueryState.empty` and the actual one-instruction folded state, instruction inequality, both `ProducesEventAt` facts, both global `getElem?` facts, and both `ReviewerReadOccurrenceReceipt` facts for the same event. | `reviewerSingletonInput = [7]` -> actual closed whole-query program -> instruction 0 and folded instruction 1 -> identical segment-`1`, index-`0` select-directory read event at local position 0 -> global positions 0 and 15 -> two complete receipts -> public Classic/headline alias and exact-type consumers. The unchanged segment-`22` compatibility witness remains at its own positions `14`/`29`. | P is the literal-position/instruction/folded-state proposition on the singleton execution. Q1 replaces global `15`; Q2 replaces instruction position `1`; Q3 uses one producer instruction for both occurrences; Q4 removes folded-state or local-position identity; Q5 existentially hides the positions. The exact-type consumers must reject each Q. | | Open |
| `REQ-B7R4-PUBLIC-EXPECTED-TYPE-CONSUMER` | expose accurate public aliases/consumers for both strengthened propositions and add independent expected-type or exact-use checks such that changing the public proposition back to an isolated trace or existentially hidden positions breaks a committed consumer. Printing the mutable theorem type is not enough. | Public/trust | `RMQ.SuccinctClassic` theorems and `RMQ.Headlines` aliases expose both literal propositions; at least one validation/example consumer and each curated trust file state the independent expected proposition rather than adapting with `#check`/`#print`. | Source strengthened theorem -> Classic literal theorem -> headline literal alias -> validation/example expected-type proof -> WordRAM/headline expected-type trust consumer. | Mutate the public whole-query proposition to the old isolated trace, or mutate the occurrence proposition to existential positions/receipts. The committed expected-type consumer must fail at the theorem application before any mutable-type `#print` can pass. | | Open |
| `INV-B7R3-CHARGED-LEVEL-PRESERVATION` | Preserve the already-checked exact-cost-33 and same-object `Not (cost <= 30)` theorem, value/address dependency, store/footprint identity, strong readWord-only route, 22 physical sources/logical segments `0..22`, live 21/fresh rejected 23, one-word width, 218-to-527 capacity, `2*n+o(n)`, and exact `210 = 2*35 + (2*11 + 2*37 + 33) + 11` algebra. | Inherited local + public | Existing exact theorem types and object chains remain unchanged and elaborate after the two bridge additions; no payload, source, segment, cost constant, width, capacity, or space theorem changes. | Charged level table -> canonical component store -> reviewer physical payload -> global whole-query trace -> Classic/headline capstones. | Search/diff challenge: no payload/store/cost/source definitions change. Direct builds and trust inventories retain all named predecessor theorems. | | Open |
| `INV-B7R3-STORE-VALUE-TRACE-PRESERVATION` | Preserve the already-checked value/address dependency, store/footprint identity, exact charged table/store execution, positional trace equality, returned-value corruption witness, and strong readWord-only route on the same execution objects. | Inherited semantic | The R3 corruption theorem, store erasure/backing, positional trace, and readWord-only theorem retain their exact types; the new bridges mention those same canonical shape/trace objects and introduce no synthetic event or sibling store. | Level word -> executed component read/address -> returned candidate -> global canonical trace/store -> public list query. | Q substitutes a sibling trace/store or lets only the log differ; unchanged exact trust consumers and source diff reject it. | | Open |
| `INV-B7R3-328-352-SEPARATION` | Preserve historical `canonicalTransitionalQueryCost = 328`, separately named live `liveCompatibilityQueryCost = 352`, and current exact cost `210`; no theorem, alias, validation guard, or example may relabel one as another. | Inherited public/history | Existing literal theorem names and all current direct consumers elaborate unchanged; exact search shows no new compatibility-name drift. | Source cost identities -> Classic -> headlines/validation/examples/trust. | Q labels live `352` as historical `328` or allows live components to move the literal `328`; exact existing types reject it. | | Open |
| `INV-B7R3-REPLAY-PRESERVATION` | Preserve the exact typed 21-case registry, selector nonvacuity, unknown/zero failure, fixture cache, and child-free replay. | Inherited executable/process | Startup smoke, known exact selector, unknown and zero-match controls, then full ordered registry retain exact counts, order, answers, routes, costs, dispositions, cache counts, and exit codes. | Typed registry -> selected cases -> cached prepared fixtures -> exact child-free replay verdict. | Missing/duplicate entry, zero selection, untyped cache, or child process remains rejected by the unchanged executable. | | Open |
| `INV-HALF-OPEN-LEFTMOST` | Preserve half-open leftmost `List Int` semantics, valid `[1704,3469)` and `[0,1)` guards, invalid-range behavior, and the exact independent-answer replay controls. | Inherited semantic | Classic exactness/invalid theorem types, literal valid-range conjuncts in both new public propositions, validation/examples, and replay all remain checked. | `List Int` reference -> guarded Classic query -> actual whole-query trace/result -> replay expected answers. | Q removes the valid guard, changes a right endpoint to inclusive, changes the singleton domain, or changes leftmost ties; exact consumers/replay reject it. | | Open |
| `INV-CATEGORY-SEPARATION` | Preserve the distinction between payload bits, proof-only fields, model-level cost ticks, executable Lean runtime behavior, allocation/capacity, trace events, and measured wall time. Do not turn Lean wall time or proof-only witness data into modeled ticks or payload. | Inherited model/process | No closed large proof witness is added to executable initialization; startup smoke remains bounded; source changes are propositions/proofs/aliases only and do not alter payload/store/cost definitions. | Proof-local evidence -> erased theorem surface; executable replay remains operational evidence, not modeled cost. | Q introduces a closed size-3469 runtime constant or changes a cost/payload definition to encode proof evidence; diff plus startup smoke reject it. | | Open |
| `REPLAY-EXACT-REGISTRY` | preserve a committed exact ordered registry for all 21 cost-harness windows, with expected answer, route class, pre/post swap cost disposition, and the leftmost-tie fixture; reject missing/duplicate IDs. | Inherited executable | Unchanged `replayRegistry`, literal expected-ID order, `Nodup`, expected pre-cost vector, and default exact `21/21` execution. | Registry -> default traversal and exact case reports. | Remove/duplicate/reorder an ID; structure validation must fail before credited execution. | | Open |
| `REPLAY-SELECTOR-NONVACUITY` | any focused harness selector must execute exactly one requested registered window, reject unknown selectors, and make zero-case selection fail rather than pass vacuously. | Inherited executable | Known `interior-full-leftmost` reports exactly `1/1`; unknown `__unknown_b7r4__` and zero-match fixture `__zero_b7r4__` exit `4`. | CLI selector -> exact registry entry -> counted execution. | Known, unknown, and zero-selection controls with exact counts/exit codes. | | Open |
| `REPLAY-SUBPROCESS-DEADLINE` | every spawned Lean/Lake child has a positive evidence-based deadline, process-tree cleanup, failure classification, and final clean-tree restoration; do not discover timeouts by duplicating a quiet command. | Verification process | Command ledger records positive deadlines, observed durations, any exact owned process disposition, and clean restoration; the Lean harness remains child-free. | External verification wrapper -> one owned process -> final evidence. | On timeout inspect the surviving process/artifacts; never launch an unchanged duplicate. | | Open |
| `CHK-B7R4-FOCUSED-BUILDS` | Elaborate/build the two defining modules first, then `RMQ.Core.SuccinctRMQClassic`, `RMQ.Headlines.RMQ`, the exact validation/example consumers, and both trust inventory scripts as affected. On the unchanged committed tree run affected direct builds and `lake build RMQ RMQPaper RMQExamples` once. | Verification | Every named focused/direct/aggregate command exits `0` in the frozen order on the applicable dirty or exact committed tree, with timings and timeout rationale recorded. | Defining modules -> public imports -> validation/examples -> aggregate roots. | A source theorem or alias removed/changed must break its direct expected-type consumer before the broad build. | | Open |
| `CHK-B7R4-TRUST` | Run `scripts/wordram_axiom_check.lean`, `scripts/headline_axiom_check.lean`, the hygiene scans, topology lint, strict design-decision checks against `07b0dda3878574070ae7ab0332cc61658e56f67a` and original `f6564ec`, `git diff --check`, committed-range diff check, changed-path check, and clean status. Do not run `scripts/gate.ps1`, `scripts/axiom_check.lean`, the unrelated A07 validator, strict claim drift when public prose is unchanged, or policy mutation regression when policy is unchanged. | Verification/trust | Exact commands exit as required; expected baseline scan hits are classified with no new hit; excluded commands remain unrun; changed paths stay within scope. | Source/public propositions -> curated trust/decision/topology/hygiene packet. | Deleting a trust line or relying only on mutable theorem printing cannot satisfy the independent expected-type examples added to the trust files. | | Open |
| `CHK-B7R4-REPLAY-ORDER` | For replay imports, obey WDD-20260719-010: bounded startup/shape smoke, then one known selector, then full replay; only afterward run broad trust/topology/build certification on frozen content. Inspect processes and artifacts after a timeout; never repeat an unchanged quiet command. | Verification process | Exact order: `--shape-profile-size 5`, known `--case interior-full-leftmost`, full default registry, then unknown/zero anti-vacuity controls and only then broad certification. Record outcomes/durations. | Changed import closure -> startup isolation -> selector -> registry -> broad certification. | A ledger whose first observation is full replay or whose broad certification precedes replay closure fails this row. | | Open |
| `COMPLETE-B7R4-COMMITTED-EVIDENCE` | Stage only intended files and commit the semantic repair. Report `CANDIDATE_COMPLETE` only for this local B7-R4 rung; coordinator acceptance and the separate documentation disposition remain pending. The final packet must include exact theorem types, full composition/occurrence chains, frozen matrix, mutation results, expected-type consumer evidence, proof digestion, assumptions, skeptical question, decisions, command timings, clean status, and exact post-commit range checks. | Completion | One clean commit over exact base contains the two bridges, public consumers, trust checks, matrix/worklog evidence, and any required design decision. `git diff --check 07b0dda3878574070ae7ab0332cc61658e56f67a..HEAD` and clean status pass. | Every local row -> committed evidence packet -> coordinator reconstruction; document-authority consolidation remains coordinator-owned. | Any source/checker edit invalidates its transitive evidence; no result from an earlier tree is claimed as final. | | Open |

Every inherited non-document row from the original B7, B7-R1, B7-R2, and
B7-R3 sections remains unchanged and load-bearing. `STRETCH-01` and the
coordinator's document-authority consolidation are explicitly deferred and
non-blocking only for this local semantic rung. No public prose, policy,
roadmap, packet, README, artifact, or current-fact registry is in scope.

### B7-R4 verification coverage ledger (planned before implementation)

The closest observed R3 timings are: focused defining-source elaboration
20.945s to 33.3s, focused transitive harness rebuild 321.330s, startup shape
probe 2.135s, known selector 0.282s, full registry 29.158s, WordRAM trust
111.300s, headline trust 45.649s, and aggregate build 184.999s. Timeouts below
include cold-cache margin. Only one heavy Lean/Lake process runs at a time.

| Role | Exact command/evidence | Changed paths / rows covered | Unique failure mode | Planned timeout |
| --- | --- | --- | --- | ---: |
| Development-loop | `git diff --check` | Every edited path; `COMPLETE-B7R4-COMMITTED-EVIDENCE` | Immediate whitespace defect before compilation. | 2m |
| Development-loop | `lake build RMQ.Core.SuccinctFinalRAM` | Whole-query bridge; `REQ-B7R4-WHOLE-QUERY-COST33-REACHABILITY` | Actual folded LCA/trace object fails to elaborate. | 20m |
| Development-loop | `lake build RMQ.Core.SuccinctFinal.RAM.ReviewerReachabilitySmall` | Indexed singleton bridge; `REQ-B7R4-CONCRETE-POSITION-INSTRUCTION-IDENTITY` | Literal positions/instructions/local states do not inhabit `ProducesEventAt`. | 20m |
| Development-loop | `lake build RMQ.Core.SuccinctRMQClassic` then `lake build RMQ.Headlines.RMQ` | Public aliases; `REQ-B7R4-PUBLIC-EXPECTED-TYPE-CONSUMER` | Source/public type mismatch. | 20m each |
| Development-loop | `lake build RMQ.Validation.SuccinctClassic` and `lake build RMQExamples.Concrete` | Independent expected-type consumers | Public weakening or existential erasure remains unnoticed by aliases. | 20m each |
| Development-loop | `lake env lean scripts/wordram_axiom_check.lean` and `lake env lean scripts/headline_axiom_check.lean` | Exact expected-type trust consumers; `CHK-B7R4-TRUST` | Trust inventory follows mutable type or introduces an axiom. | 20m each |
| Replay startup | `lake exe rmq_succinct_classic_cost_harness -- --shape-profile-size 5` | `INV-CATEGORY-SEPARATION`, `CHK-B7R4-REPLAY-ORDER` | Imported proof witness regresses executable initialization. | 2m |
| Replay selector | `lake exe rmq_succinct_classic_cost_harness -- --case interior-full-leftmost` | `REPLAY-SELECTOR-NONVACUITY`, `CHK-B7R4-REPLAY-ORDER` | Exact selector does not run one load-bearing case. | 5m |
| Replay full | `lake exe rmq_succinct_classic_cost_harness` | `INV-B7R3-REPLAY-PRESERVATION`, `REPLAY-EXACT-REGISTRY` | Registry/order/answer/route/cost/cache regression. | 10m |
| Replay anti-vacuity | unknown `--case __unknown_b7r4__` and zero-match `--fixture __zero_b7r4__` | `REPLAY-SELECTOR-NONVACUITY` | Zero selected cases pass. Expected exit `4`. | 2m each |
| Final-required | affected direct builds above, then `lake build RMQ RMQPaper RMQExamples` once on the unchanged committed tree | `CHK-B7R4-FOCUSED-BUILDS`, inherited public composition | Cross-root/import coherence. | 45m |
| Final-required | both curated trust scripts on the unchanged commit | `CHK-B7R4-TRUST` | Exact public trust and expected-type consumption. | 20m each |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts\\paper_topology_lint.ps1` | `CHK-B7R4-TRUST` | New public aliases not reachable/currently classified. | 15m |
| Final-required | `powershell -ExecutionPolicy Bypass -File scripts\\design_decision_check.ps1 -Strict -Base 07b0dda3878574070ae7ab0332cc61658e56f67a` and the same command with `-Base f6564ec` | Design evidence; `CHK-B7R4-TRUST` | Missing or incomplete semantic decision record. | 10m each |
| Final-required | `rg -n "\\b(sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|noncomputable)\\b|import Mathlib" RMQ lakefile.toml` and `rg -n "native_decide|Lean\\.ofReduceBool" RMQ` | Hygiene; `CHK-B7R4-TRUST` | New trust shortcut or Mathlib dependency. | 5m each |
| Final-required | `git diff --check`; after commit `git diff --check 07b0dda3878574070ae7ab0332cc61658e56f67a..HEAD`; `git diff --name-only 07b0dda3878574070ae7ab0332cc61658e56f67a..HEAD`; clean `git status --short --branch` | Scope/hygiene/completion | Post-commit whitespace, unauthorized path, or dirty tree. | 2m each |

Strict claim drift is conditional and skipped because public prose is outside
scope and unchanged. Policy mutation regression is conditional and skipped
because policy is outside scope and unchanged. `scripts/gate.ps1`,
`scripts/axiom_check.lean`, the unrelated A07 validator, and duplicate broad
certification are excluded by the frozen prompt.

### B7-R4 candidate evidence map

The frozen pre-implementation rows above remain verbatim. This append-only map
records their disposition on the frozen semantic content. The exact semantic
source candidate is `ba71d1589e8a90ca82f88ce00465d069db034e43`;
post-commit commands are preserved in the B7-R4 handoff and the coordinator
closure ledger in `B7_WORKLOG.md`.

| Frozen row | Exact candidate evidence and rejected challenge | Candidate disposition |
|---|---|---|
| `REQ-B7R4-WHOLE-QUERY-COST33-REACHABILITY` | `concreteBPNativeB7Cost33Witness_wholeQuery_reaches_interiorTrace` retains valid `[1704,3469)`, shape identity, actual select values `3409`/`6937`, the folded position-2 LCA instruction, the real middle conditional at `(143,146)`, and append containment of the identical segment-20 trace in both the instruction and complete whole-query traces, with exact cost/length `33` and rejected `<=30`. The Classic proposition additionally retains guarded `queryTraceResult` equality. Isolated-evaluator, changed-invocation, and upper-bound-only Qs lack demanded conjuncts. | Evidence complete; coordinator acceptance recorded. |
| `REQ-B7R4-CONCRETE-POSITION-INSTRUCTION-IDENTITY` | `concreteBPNativeSuccinctRMQSingleton_repeated_read_exact_positions` retains actual `[7]`, `[0,1)`, component length `15`, segment-`1`/index-`0` events at global `0`/`15`, instruction `0`/`1`, unequal left/right select-close instructions, empty/one-instruction-folded states, local `0`, both `ProducesEventAt` facts, and both receipts. Changed position/instruction, collapsed producer, erased state/local, and existential-position Qs cannot inhabit the literal expected consumers. | Evidence complete; coordinator acceptance recorded. |
| `REQ-B7R4-PUBLIC-EXPECTED-TYPE-CONSUMER` | Classic propositions conjoin actual guarded query equalities with the exact source propositions; headline aliases preserve those types. Validation, example, WordRAM trust, and headline trust consumers independently unfold and demand literal fields instead of following only mutable `#print` output. | Evidence complete; public weakening challenge rejected. |
| `INV-B7R3-CHARGED-LEVEL-PRESERVATION` | No payload/store/cost/source definition changed. Exact `33`/not-`<=30`, charged table, one-word width, source/segment, `218 -> 527`, little-o, and exact `210` surfaces remain in the curated builds/trust inventories. Exact-commit direct, aggregate, and trust certification passed on `ba71d15`. | Evidence complete. |
| `INV-B7R3-STORE-VALUE-TRACE-PRESERVATION` | R3 store erasure, footprint, positional trace, returned-value corruption, and strong readWord-only theorems remain unchanged; new propositions name the existing canonical traces and add no store or event. | Evidence complete; sibling-store/trace challenge rejected. |
| `INV-B7R3-328-352-SEPARATION` | No compatibility cost declaration changed; historical `328`, live `352`, and current `210` remain separate direct/trust consumers. | Evidence complete. |
| `INV-B7R3-REPLAY-PRESERVATION` | Ordered default replay exited `0` in 39.2s with exact `21/21`, six expected/actual cached fixtures, and every answer/reference/route/post-cost/disposition/bound predicate true. | Evidence complete. |
| `INV-HALF-OPEN-LEFTMOST` | Both new propositions retain literal `ValidRange`; guarded Classic query equalities elaborate; the exact registry preserves independent answers, invalid guards, singletons, and leftmost ties. | Evidence complete. |
| `INV-CATEGORY-SEPARATION` | Changes are proof propositions/aliases/consumers only. Startup shape probe passed; no large closed runtime witness, payload, allocation, store, event, or modeled-cost definition was added. | Evidence complete. |
| `REPLAY-EXACT-REGISTRY` | Default traversal executed the unchanged literal registry in order, exactly `21/21`, with all exact predicates and cache counts true. | Evidence complete. |
| `REPLAY-SELECTOR-NONVACUITY` | Known selector passed exactly `1/1`; the built executable returned exit `4` for unknown `__unknown_b7r4__` and zero-match `__zero_b7r4__`. `lake exe`'s normalization of the unknown child failure to wrapper exit `1` is separately recorded and not mistaken for the executable contract. | Evidence complete. |
| `REPLAY-SUBPROCESS-DEADLINE` | Positive deadlines were used; startup, selector, full registry, and negative controls all returned before deadline. No survivor or retry existed. The topology lint's sandboxed dependency-download failure received no semantic verdict and its permitted rerun passed. The final `ba71d15` worker tree and independent audit tree were clean. | Evidence complete. |
| `CHK-B7R4-FOCUSED-BUILDS` | Both defining modules, Classic, Headlines, validation, examples, and both trust files passed development builds. On exact semantic commit `ba71d15`, all six affected direct targets passed and `lake build RMQ RMQPaper RMQExamples` passed in 49.9s. | Evidence complete. |
| `CHK-B7R4-TRUST` | Both curated exact-commit trust inventories passed in 113.5s and 48.1s with literal expected consumers and only the established Lean logical axioms. Final topology, both strict DD baselines, exact committed-range checks, hygiene, changed-path, and clean-tree checks passed. | Evidence complete. |
| `CHK-B7R4-REPLAY-ORDER` | Exact observed order was startup (41.1s), known selector (3.0s), full registry (39.2s), negative controls (1.7s/1.5s), then topology/decision/hygiene diagnostics. | Evidence complete. |
| `COMPLETE-B7R4-COMMITTED-EVIDENCE` | Exact semantic commit `ba71d15` contains the two source propositions, guarded public/headline surfaces, independent expected consumers, DD-20260719-005, this matrix, and the worklog/digestion packet. Its exact-commit certification, coordinator reconstruction, independent literal expected-type elaboration, scope audit, committed-range checks, and clean status are preserved in the closure ledger. This evidence-only repair changes no Lean, executable, policy, public-prose, or theorem file. | Evidence complete; coordinator integration authorized. |

Every inherited non-document row remains load-bearing and unchanged. Public
prose and policy were not edited, so strict claim drift and policy mutation
regression remain correctly skipped. The forbidden broad gate, aggregate axiom
script, and unrelated A07 validator were not run. Coordinator acceptance is
recorded for the local semantic rung; document-authority consolidation,
stale-prose disposition, and `STRETCH-01` remain separate open work.
