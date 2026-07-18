# B6 Charged Same-Block LCA Acceptance Matrix (frozen before implementation)

Worker: B6-01 (branch `claude/b1-b2-charged-fringe-tables`, base
`c0c32c4a0ba63fda2246806f0775ebe5b61d928d`).
Contract source: the B6-01 delegation prompt (coordinator round 5 decision,
`docs/internal/AUDIT_AND_A_DESIGN.md`), governed by DD-20260717-C05-001
(which forbids leaving the fringe min-excess extraction event-silent) and
`docs/internal/OPTION_B_CHARGED_FRINGE_DESIGN.md`.
Requirement wording below is verbatim from the delegation prompt.
Frozen at this commit; after this commit only evidence, status, and
coordinator-approved amendments may change.

This matrix ADDS rows. No closed B2/B3/B4 row is weakened or reopened.

## The finding this rung closes

`localBPSameBlockCloseSeededCosted`
(`RMQ/Core/SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean:1128-1143`)
sets `cost := 4` while computing `localBPSeededPrefixRangeMinExcess` and
`localBPSeededPrefixRangeArgMinPrefixPos` over
`count = rightClose - leftClose + 1` positions, unbounded in input size
(`count` reaches `blockSize = 2*(Nat.log2 size + 1)`). B2 charged the
cross-block arm and left this arm byte-identical. It is the last
event-silent computation on the accepted route.

## Verified anchors (this worktree, HEAD `c0c32c4`)

- silent same-block leaf: `localBPSameBlockCloseSeededCosted`
  (`LocalBPDecoder.lean:1128`), cost lemma `_cost_le` (`:1164`),
  decoded twins `localBPSameBlockCloseDecodedCosted` (`:1145`) /
  `...WithRankSeed` (`:1154`, cost lemma `:1179`), exactness
  `...WithRankSeed_exact_of_query_same_block` (`:1561`).
- trace twins: `localBPSameBlockCloseSeededTraceResult`
  (`ConcreteDirectoryRAM.lean:334`, `_refines` `:350`, `_trace_forall`
  `:1668`), `localBPSameBlockCloseDecodedTraceResultWithRankSeed`
  (`:1559`, `_refines` `:1571`, `_trace_forall` `:1695`).
- WithStore twins: `localBPSameBlockCloseSeededTraceResultWithStore`
  (`ConcreteDirectoryRAMStoreParam.lean:4213`, `_eq_of_agree` `:4229`,
  `_store_parametric` `:4246`, `_matchesReadStore` `:4260`,
  `_no_syntheticCostOnlyPrimitive` `:4274`),
  `localBPSameBlockCloseDecodedTraceResultWithRankSeedWithStore` (`:4289`,
  same four lemmas at `:4302/:4322/:4338/:4362`); final-rank-seed store twin
  `SuccinctFinalStoreParam.lean:539` (`:549/:569/:599`).
- accepted dispatchers (the swap sites, names/statements to be preserved):
  `canonicalLcaCloseCostedWithRankSeed` (`ChargedFringeWiring.lean:31`),
  `lcaCloseTraceResultWithRankSeedAllSizeStructural` (`:49`, ALREADY
  carries an unused `_sameBlockSegment : Nat` parameter at `:54`),
  `...WithStore` (`:419`); route entry
  `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural`
  (`SuccinctFinalRAM.lean:2330`), reached from
  `WholeQueryInstr.evalGlobalWordTrace` (`:3185-3191`).
- reusable B2 machinery (no new mathematics required):
  `bpFringeChunkFoldCosted_global_eq_localBPSeeded`
  (`ChargedFringeChunks.lean:1694`), side condition discharged all-size by
  `four_machineWordBits_le_32_mul_bpFringeChunkBits` (`:49`);
  `bpFringeCandGlobal` (`:1617`); template leaf
  `bpChunkedLeftFringeCandidateSeededCosted` (`:1630`) with `_cost_le`
  (`:1668`) and `_value_eq` (`:1742`); window validity
  `bpFringeWindowValid_localBPSeedExcess` (`:1940`); window identity
  `localBPWindowBits_eq_flatten_localBPBlockWordsRead`
  (`LocalBPDecoder.lean:228`) — the same-block window is definitionally the
  SAME object as the B2 fringe window, so the segment-21 table applies
  unchanged.
- cost algebra: `bpChunkedEndpointFringeChargedTraceCost = 37`
  (`ChargedFringeSubstitution.lean:25`),
  `bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed rankCost
  = 2*rankCost + 2*37 + 30` (`:28`;
  `canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 30` at
  `InteriorDirectory.lean:1783`); branch cap proof
  `canonicalLcaCloseCostedWithRankSeed_cost_le_principled`
  (`ChargedFringeWiring.lean:150`, same-block arm at `:163-179` currently
  discharging `rankCost + 4 <= 2*rankCost + 104` by `omega`).
- route literal: `wholeQuery = 2*35 + (2*11 + 2*37 + 30) + 11 = 207`;
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`,
  `SuccinctClassic.queryCost_eq : queryCost = 207`; consumers
  `Headlines/RMQ.lean:70/:497/:529`, `Validation/SuccinctClassic.lean:266`,
  `Validation/SuccinctClassicCostHarness.lean:118` (`canonicalBoundIs207`),
  `RMQExamples/Concrete.lean:84`, `scripts/paper_topology_lint.ps1`
  (`SumLe207`), `scripts/headline_axiom_check.lean`.
- vocabulary theorem:
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`.

## Load-bearing arithmetic finding (recorded at freeze time)

The delegation prompt predicts the literal moves "to at most 240". Read at
source, the close/LCA principled cap is a MAX over the two branches, not a
sum: the cross-block arm already pays `2*rankCost + 2*37 + 30` (= 126 at
`rankCost = 11`), while the charged same-block arm will pay
`rankCost + 4 + 33 = rankCost + 37` (= 48). Since
`rankCost + 37 <= 2*rankCost + 104` for every `rankCost`, the existing
`bpChunkedPrincipledBPCloseChargedTraceCostWithRankSeed` cap absorbs the
charged same-block arm with no algebra field changed, so the derived route
literal is expected to RE-DERIVE TO 207 UNCHANGED.

REQ-B6-05 is therefore recorded verbatim but its evidence column will
record the derivation OUTCOME as authoritative (the prompt's own rule:
"DERIVE it, never assert; if the derivation lands elsewhere, the derived
value wins"). If the derivation confirms 207, no historical constant is
minted, no frozen identity moves, and no topology-anchor rename occurs —
this is strictly less public-surface disruption than authorized, not more.
The authorization to move the literal is left UNUSED. Coordinator should
confirm this disposition.

| ID | Exact frozen requirement (verbatim) | Scope | Evidence needed (exact proposition/check) | Named consumer and identity/composition chain | Anti-vacuity challenge | Evidence obtained | Status / residual gap |
| --- | --- | --- | --- | --- | --- | --- | --- |
| REQ-B6-01 | "charged same-block fold with literal cap" — "The charged same-block leg: replace the silent argmin with the chunk fold (reusing B2's machinery ...)". | Local | A `Costed` same-block leaf whose recursion is the B2 chunk fold over at most a literal number of chunks (`Nat.min (relHi / c + 1) 33`), with a checked all-size literal cost bound and NO size hypothesis or readiness guard; the per-position scan absent from the charged path. | Feeds REQ-B6-02/03 and the swapped dispatcher (REQ-B6-09). | Confirm the cost bound has no size hypothesis and covers tiny shapes; confirm the charged definition contains no recursion over window positions (the per-position scan may appear only in the spec/proof layer). | (pending) | Open |
| REQ-B6-02 | "value equivalence to the accepted silent computation under the route's own hypotheses". | Local | Checked theorem: charged same-block leaf `.value = (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose seed).value`, universally quantified over shape/blockSize/leftClose/rightClose/seed under hypotheses discharged at every accepted call site (window validity, count positivity, coverage) — not on sampled inputs. | Route exactness `canonicalLcaCloseCostedWithRankSeed_exact_of_query` (`ChargedFringeWiring.lean:187`) re-proved through this substitution. | P = value equality of the full `Option Nat` result for all reachable invocations. Reject Q1 (agreement on sampled inputs), Q2 (agreement of the min component only, before `bpCandidateClose?`), Q3 (rightmost-tie argmin policy). Name the checked theorem rejecting each. | (pending) | Open |
| REQ-B6-03 | "positional receipt/trace equality". | Local | TraceResult and WithStore same-block twins whose trace is the 4 accepted window-word reads plus one `readWord sameBlockSegment slot` per visited chunk; checked `_refines` (`toCosted` = the REQ-B6-01 leaf), `_matchesReadStore`, `_no_syntheticCostOnlyPrimitive`, `_trace_forall`, `_eq_of_agree`, `_store_parametric`, mirroring the B2 fringe trace surface. | Swapped trace dispatchers (REQ-B6-09) and the whole-query `_trace_forall` regeneration. | The trace must contain the actual per-chunk `readWord` events produced by the store computation, never `ofCosted` synthetic markers; the no-synthetic lemma must be checked, and the refined value must depend on the read words. | (pending) | Open |
| REQ-B6-04 | "store/provenance coverage for any new reads" — "extend provenance/store coverage for any new reads to the W19 standard already used for segments 21/22 (see `ReviewerReachability*.lean` and the B4 packet fields)". | Local+roadmap | If the same-block reads land at the existing segment 21 table: the reads are covered by the existing `.fringeChunkTable` source, and the provenance packets (`every_emitted_read_has_listed_region`, `..._occurrence_provenance`, `..._eventValue_producer_provenance`) are regenerated to include a same-block producer read path; W19 successful-occurrence witness exhibited on a SAME-BLOCK execution. If a new table/segment is introduced instead, the full store/erasure/capacity/o(n)/provenance treatment plus a DD is required. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy`; chain: same-block chunk read -> segment -> source -> region -> physical address -> counted payload. | Provenance must cover the ACTUAL emitted same-block events (producing instruction + occurrence position), not merely assert segment membership; deleting the same-block case from the regenerated induction must break adequacy. The W19 witness must be a same-block query, not the existing cross-block one. | (pending) | Open |
| REQ-B6-05 | "derived new route literal with 207 frozen" — "Re-derive the route literal from the named component algebra; freeze the old 207 as a named historical constant with its `_eq` theorem and guards, exactly as `concreteBPNativeSuccinctRMQSilentWordRankSelectChargedTraceCost_eq = 142` freezes 142. Update every Lean consumer (grep `207`), the cost harness expectation, validation/examples guards, and the topology CURRENT anchor". | Local+public | The route literal RE-DERIVED (by `rfl` from the component algebra, never asserted) over the amended route. If the derived value differs from 207: freeze 207 by the 142 pattern and update every consumer enumerated in the anchors above. If the derivation yields 207 unchanged: record the derivation, leave the public identity and all consumers untouched, mint no historical constant, and record that the authorization to move the literal was not needed. | `SuccinctClassic.queryCost_eq` -> paper main theorem conjunct -> headline abbrevs -> harness/validation/examples guards -> topology anchor. | The literal must be DERIVED from the algebra (`rfl`), not asserted against an independent numeral; mutating a component constant must break the `_eq` right-hand side. If the value is unchanged, verify that it is unchanged because the branch cap genuinely absorbs the new reads (exhibit the checked branch bound), not because the new reads were left out of the cost accounting. | (pending) | Open |
| REQ-B6-06 | "Repair the charge-policy section of `docs/PAPER_MODEL_ADEQUACY.md` so it is TRUE: after this rung, state precisely what remains uncharged and why it is bounded per step. Sync any doc/claim surface that cites 207." | Public surface | The charge-policy paragraph (`PAPER_MODEL_ADEQUACY.md:139-153`) amended so its claim ("after B2/B3 every uncharged step is a BOUNDED-PER-STEP register computation ... not an unbounded scan") is true of the amended route; the same-block leg named; residual uncharged work enumerated precisely. Doc surfaces citing 207 synced only as the derived value requires. | Paper adequacy doc; `claim_drift_scan.ps1`, `paper_topology_lint.ps1`. | The repaired text must be checkable against source: every "bounded per step" claim must name the checked cap. A repair that merely deletes the false sentence without stating the new truth is insufficient. | (pending) | Open |
| REQ-B6-07 | "library green at EVERY commit"; "no dead sources"; parallel-then-swap. | Process | Per-commit `lake build RMQ` (or the full battery at commit boundaries) exit 0, recorded in the `B6_WORKLOG.md` ledger; the swap is atomic within one commit; no commit introduces a counted-but-unread source. | Coordinator audit of branch history. | `git log` + ledger cross-check at final report. | (pending) | Open |
| REQ-B6-08 | "committed hygiene" — "no sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib"; `git diff --check`; `design_decision_check.ps1 -Strict`; `claim_drift_scan.ps1`; `paper_topology_lint.ps1`. | Verification | Hygiene `rg` shows no NEW forbidden-token hits in touched files; native_decide scan clean; `git diff --check` and `git diff --check d90b062..HEAD` clean; the three scripts exit 0. Do NOT run `gate.ps1`. | Hygiene. | Deliberately grep touched modules for introduced threshold/readiness guards on the public route. | (pending) | Open |
| REQ-B6-09 | "Swap it into the accepted route atomically (library green at every commit, parallel-then-swap), preserving the dispatcher's name/statement identity exactly as B2's M9 did." Plus: "Re-establish the vocabulary theorem (`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`) over the amended route". | Roadmap+public | The accepted dispatchers (`canonicalLcaCloseCostedWithRankSeed`, `lcaCloseTraceResultWithRankSeedAllSizeStructural(+WithStore)`) call the charged same-block leg with their names and statement shapes preserved; the whole-query route consumes them unchanged; route exactness re-proved; `..._readWord_only` re-checked over the amended route. | Chain: charged same-block leaf -> swapped dispatcher -> `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructural` -> whole-query program -> `SuccinctClassic.queryCosted`/`queryCost`. | The swap must preserve the exact public answer on every valid query (re-proved exactness, same quantifiers), and the vocabulary theorem must be re-proved over the AMENDED route, not inherited from the pre-swap object. | (pending) | Open |
| INV-STORE-IDENTITY | Inherited: "the exact payload/store executed is the payload/store counted by the public space theorem". | Inherited | Same-block chunk reads execute against the same counted table store as the cross-block reads (flatten/erasure chain unchanged if segment 21 is reused). | REQ-B6-04 chain. | Two-payload trap: the counted table component must be the same object the same-block execution reads. | (pending) | Open |
| INV-VALUE-DEPENDENCY | Inherited: "returned values and routing decisions depend on actual charged reads, not a semantic answer computed before the reads". | Inherited | The charged same-block value is computed from the `Costed`/trace read results through the fold's bind chain; a corruption witness at a slot the same-block execution actually reads changes the returned close value. | REQ-B6-01/02. | The corruption conclusion must be about the returned `Option Nat` close, not the trace log; the corrupted slot must be in the same-block read footprint. | (pending) | Open |
| INV-NO-SYNTHETIC | Inherited: "synthetic events, decorative rereads, and post-hoc replay do not support the execution claim". | Inherited | `_no_syntheticCostOnlyPrimitive` checked for the new same-block trace objects; every charged unit is a window tick or a table read. | REQ-B6-03. | Decorative-read challenge: every charged read's value must flow into the result. | (pending) | Open |
| INV-ALL-SIZE | Inherited: "exactness covers all assigned sizes and edge cases without hidden readiness or compatibility dispatch". | Inherited | All new equivalence/cost theorems quantified over all shapes/sizes; the only cap is the uniform `Nat.min _ 33`, proven identity on the reachable domain; no `Ready`/threshold predicate. | REQ-B6-01/02. | Grep the new code for readiness predicates; check the degenerate same-block case `leftClose = rightClose` and the maximal `count = blockSize`. | (pending) | Open |
| INV-PUBLIC-COMPOSITION | Inherited: a theorem combining space, exactness, cost, provenance, or machine claims proves them about the same construction and execution. | Inherited | The capstone/profile theorems re-proved over the amended route (same payload, same execution), not conjoined across pre- and post-swap objects. | REQ-B6-09. | Check the capstone's `rfl` conjunct still holds against the amended route. | (pending) | Open |
| CHK-01 | "Final battery: `lake build RMQ RMQPaper RMQExamples`". | Verification | Exit 0. | — | — | (pending) | Open |
| CHK-02 | "hygiene `rg` (no NEW hits) + native_decide scan". | Verification | No new forbidden-token hits in touched files. | — | — | (pending) | Open |
| CHK-03 | "cost harness (expect the new literal + frozen 207/142/76/328 guards)". | Verification | Harness run recorded; guards consistent with the DERIVED literal (see REQ-B6-05 disposition). | — | — | (pending) | Open |
| CHK-04 | "`git diff --check` + `git diff --check d90b062687fd8e32f5c6f0120bf21f4e56666f4b..HEAD`". | Verification | Exit 0. | — | — | (pending) | Open |
| CHK-05 | "`design_decision_check.ps1 -Strict -Base d90b062687fd8e32f5c6f0120bf21f4e56666f4b`". | Verification | Exit 0. | — | — | (pending) | Open |
| CHK-06 | "`claim_drift_scan.ps1`; `paper_topology_lint.ps1`". | Verification | Exit 0. | — | — | (pending) | Open |
