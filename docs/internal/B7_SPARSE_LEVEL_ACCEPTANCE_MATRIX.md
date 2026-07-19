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
