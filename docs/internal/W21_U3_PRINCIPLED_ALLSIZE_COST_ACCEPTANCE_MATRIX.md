# W21 U3 Principled All-Size Charged-Trace Cost Acceptance Matrix

Branch: `codex/rmq-u3-principled-allsize-cost`

Base: `45e2f0d87fa28b8a1a92e570662767e191c2e987`

Operational-bridge continuation base:
`c2694b7156f5e8ad321e16e3f36bc57284d55820`.

Paper-topology correction base:
`2405fbbc29ead446d8fdcf3285045435102779f9`.

Self-contained topology-closure continuation base:
`229607f7db28184b262fdc50c806c41a38d474bf`.

Blind A05 report read directly, without merge:
`64cfd2dae2de9b8402fd5601b0e6d0b146a0ca61` on
`codex/a05-u3-blind-acceptance-audit`.

Status: `CANDIDATE_COMPLETE` for the self-contained topology-closure repair;
coordinator reconstruction and fresh blind exact-commit audit remain required.

## Frozen Self-Contained Topology-Closure Contract

The following rows freeze the coordinator's post-`229607f7...` reconstruction
requirements before implementation.  Requirement wording is preserved; only
the evidence and status columns may change during this repair.

| ID | Frozen requirement | Intended checked evidence and identity chain | Anti-vacuity / boundary challenge | Status |
| --- | --- | --- | --- | --- |
| U3-SC-01 | Repair every stale or dead `RMQ.Headlines` reference, especially the removed transitional aliases in `docs/PAPER_THEOREM_MAP.md` and `FAMILY_SUMMARY.md`. Search the entire repository for every removed spelling. | Repository-wide removed-name scan plus checked resolution of every documentary `RMQ.Headlines.*` identifier under either `RMQPaper` or the broad `RMQ.Headlines` import, according to the document's role. | Inject a removed spelling into prose and fenced code; both must fail the production topology verdict. | Satisfied: no unauthorized removed spelling remains; 80 broad and 48 canonical paper identifiers resolve. |
| U3-SC-02 | Strengthen `concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile` so its checked type itself contains the canonical flat-payload execution/backing packet, `nonSyntheticWeight` sum = trace length, `nonSyntheticWeight` sum = `Costed.cost`, the `76` bound, and the existing exactness/space/erasure clauses. | The theorem's literal proposition uses the permitted equivalent direct backing: every successful read in the same canonical trace maps to an in-bounds address whose word is present in `concreteBPNativeSuccinctRMQReviewerPhysicalWords`; the adjacent erasure conjunct identifies those words with the canonical counted payload. The same proposition contains both weight equalities, `<= 76`, and existing space/exactness clauses. | Delete any one required conjunct from the capstone type: documentary prose and nearby theorems must not count as closure. | Satisfied in the literal checked proposition; focused and paper builds pass. |
| U3-SC-03 | Move aliases explicitly documented as compatibility-only W18 projections out of `RMQ.Headlines.RMQ` and into `RMQ.Headlines.RMQCompatibility` under names containing `Compatibility` or `Legacy`. Preserve the stronger current indexed provenance and semantic-adequacy aliases in the canonical module. | Canonical module retains indexed occurrence/invocation provenance, successful-occurrence, and semantic-adequacy aliases; compatibility module alone exposes event-value/component-path W18 projections with explicit names. | Reintroduce an old W18 projection name or an unqualified compatibility declaration in the paper module; topology lint must reject it. | Satisfied; canonical and compatibility modules plus inventories compile together. |
| U3-SC-04 | Harden `paper_topology_lint.ps1`: detect retired/transitional aliases in prose and fenced inventories; validate that every documented `RMQ.Headlines.*` identifier resolves under the appropriate broad or paper import; reject dead names, renamed-name remnants, and compatibility names presented as current paper anchors; add mutations for fenced-code, prose, dead-alias, and renamed-alias cases. | Production lint performs whole-text retired-name checks and generated Lean `#check` resolution for paper and broad documentation sets; a dedicated mutation regression calls the production verdict. | Fenced retired alias, prose transitional alias, invented dead alias, renamed remnant, and compatibility-as-current-paper-anchor fixtures must all fail while canonical and broad compatibility references pass. | Satisfied; five reject mutations and one canonical accept mutation pass without changing tracked state. |
| U3-SC-05 | Record the reusable failure mode in `KNOWN_FAILURE_MODES`/completion guidance: lexical claim scans do not establish public-symbol migration closure. A rename/removal requires repository-wide old-name search plus checked resolution of documentary theorem references. Amend `WDD-20260714-003` and the code-design decision as appropriate. | Branch-local known-failure and completion-gate references, workflow decision, and code-design decision all state the structural migration rule and its gate evidence. | A prose-only rename that passes token policy but leaves one dead fenced `RMQ.Headlines` reference must remain non-complete. | Satisfied in both skill references, WDD-20260714-003, and DD-20260714-008. |
| U3-SC-06 | Correct the W21 acceptance matrix and completion report. Do not claim that a theorem contains a conjunct unless that conjunct appears in its checked type. | This matrix quotes the strengthened capstone proposition and final command results; roadmap/digestion completion wording follows the checked type. | Compare every advertised capstone clause against `#check`/source type, not theorem neighborhood or worker narrative. | Satisfied by the literal capstone-type audit and corrected public descriptions. |
| U3-SC-07 | Run focused builds, `RMQPaper`, `RMQExamples`, full `lake build`, all axiom inventories, both validators, WordRAM review, topology-lint mutations, strict design/claim checks, `git diff --check`, and `gate.ps1`. Commit and push to the same branch. | Exact command ledger on the completed tree, exact staged path set, pushed commit, and matching remote tip. | Any post-gate edit invalidates the command ledger and requires the affected checks to be rerun. | Satisfied by the verification ledger and exact staged/pushed commit reported below. |
| U3-SC-INV | Preserve `INV-STORE-IDENTITY`, `INV-READ-BACKING`, `INV-TRACE-EXECUTION`, `INV-PUBLIC-COMPOSITION`, `INV-NO-SYNTHETIC`, and `INV-CATEGORY-SEPARATION`. | The strengthened capstone names one canonical reviewer payload, its physical erasure, the canonical trace's execution/backing packet, the two certificate equalities, exactness, and the charged-trace-only `76` bound. | A sibling payload, nearby backing lemma, synthetic marker, or controller-cost claim cannot satisfy the capstone row. | Satisfied; no execution, payload, route, trace, compatibility semantics, or model boundary changed. |

## Literal Capstone-Type Audit

The strengthened proposition itself, before its proof begins, contains these
load-bearing conjuncts over the same canonical objects:

- `flattenPayloadWords (concreteBPNativeSuccinctRMQReviewerPhysicalWords shape)
  = concreteBPNativeSuccinctRMQCanonicalReviewerPayload shape`;
- for every successful `readWord segment index (some word)` in
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult shape left right`,
  the translated physical address is in bounds and the physical word at that
  address is `some word`;
- every event has one of the three genuine constructors and the synthetic
  marker is absent;
- the trace's `nonSyntheticWeight` sum equals that trace's length, equals
  `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted ... .cost`, and is
  at most `76`;
- the same theorem retains the little-o overhead, doubled-Catalan envelopes,
  canonical payload-length bound, modeled-cost bound, and exact valid-query
  answer.

No row relies on a nearby theorem to supply one of these advertised conjuncts.

## Requirement-to-Theorem Matrix

| ID | Requirement | Checked consumer |
| --- | --- | --- |
| U3-01 | Reconstruct named primitive composition. | `CanonicalRMQChargedTraceCostAlgebra.closeLCA`, `.wholeQuery`; `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra` |
| U3-02 | Tighten every conservative `328` contribution. | `sparseExceptionSelectSource_selectPositionCosted_cost_le_thirteen`; `rankCosted_cost_le_four`; `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded` |
| U3-03 | Prove one canonical numeric equality. | `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 76` |
| U3-04 | Bound the unchanged executable trace and expose exact accounting. | `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect`; `..._syntheticCostOnlyPrimitive_not_mem`; `..._nonSyntheticWeight_sum_eq_trace_length`; `..._nonSyntheticWeight_sum_eq_cost`; `..._nonSyntheticWeight_sum_le_76` |
| U3-05 | Consume final adequacy and supplied-store footprints. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy.event_readWord_or_wordRank_or_wordSelect`; `.nonSyntheticWeight_sum_eq_trace_length`; `.nonSyntheticWeight_sum_eq_cost`; `.nonSyntheticWeight_sum_le_76`; `concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace` |
| U3-06 | Consume ordinary `List Int`, headlines, and paper root. | `SuccinctClassic.queryCosted_cost_le`; `listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal`; `Headlines.succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`; `Headlines.listIntSuccinctRMQPaperMainTheorem` with `queryCost = 76`; `RMQPaper` |
| U3-07 | Preserve U2 payload, route, physical erasure, store dependence, footprints, provenance, width, and invalid semantics. | No execution/payload definition is replaced; existing final adequacy, exactness, physical, provenance, and invalid-range theorems remain consumers beside the new cost field. |
| U3-08 | Connect the cost inventory to actual emitted events without a parallel operation vocabulary. | `WordRAM.TraceEvent.nonSyntheticWeight`; actual three-constructor classification; actual no-synthetic theorem; canonical certificate-weight sum = trace-length = `Costed.cost` = at most `76`; `syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect`; `sum_nonSyntheticWeight_ne_length_of_synthetic_mem` |
| U3-09 | Keep conventional word-RAM / serialization / preprocessing outside U3. | Theorem names contain `ChargedTrace`; design decision, family summary, paper maps, claim policy, and roadmap state the nonclaims. |
| U3-10 | Preserve transitional evidence without artificial work. | Source theorems remain checked; curated compatibility aliases live only in `RMQ.Headlines.RMQCompatibility` under explicit `Compatibility`/`Legacy` names. No padding or decorative event is introduced. |

## Old And Final Derivations

| Contribution | U2 transitional | U3 principled | Removed slack |
| --- | ---: | ---: | ---: |
| Two close selects | `2 * 16 = 32` | `2 * 13 = 26` | `6` |
| Two close rank seeds | `2 * 16 = 32` | `2 * 4 = 8` | `24` |
| Endpoint fringes | `8` | `2 * 4 = 8` | `0` |
| Interior directory | `240` | `30` | `210` |
| Final answer rank | `16` | `4` | `12` |
| Whole query | `328` | `76` | `252` |

The old expression was `3*16 + (8 + 2*16 + 240)`. The new expression is
`2*13 + (2*4 + 2*4 + 30) + 4`. Both refer to the same accepted U2 execution;
the latter uses tighter theorems for the operations that execution emits.

## Cost-Model Boundary

`TraceResult.toCosted` charges `trace.length`, so it counts a synthetic
compatibility marker if one is present. The separate
`WordRAM.TraceEvent.nonSyntheticWeight` certificate assigns unit weight to
attempted payload-word reads, word-rank primitives, and word-select primitives,
and assigns zero to the synthetic marker. The old broad name `chargedWeight`
was rejected because it obscured that distinction.

Checked execution chain: every event in the actual canonical whole-query trace
is one of the three genuine constructors; the synthetic fallback is absent; the
`nonSyntheticWeight` certificate sum therefore equals trace length and the
`Costed` cost of the same execution; the sum is at most `76`.
Counterfactually, a synthetic event cannot meet the genuine-event
classification, and its presence anywhere makes the certificate sum strictly
smaller than trace length.

Currently uncharged: instruction dispatch; input and register access;
option tests and branching; natural-number arithmetic, address and slot
calculation; fixed-width decoding; local BP scanning; candidate comparison and
merge; trace assembly; and the public valid-range guard. This list is
documentary: U3 does not expose a checked controller-operation vocabulary. E1
must define the richer instruction semantics and prove that it simulates the
same execution.

Therefore U3 does not prove `query(serializedPayload,left,right)`, full
preprocessing complexity, compiled Lean time, or conventional word-RAM time.

## A05 Publication-Topology Correction Matrix

| ID | Frozen correction requirement | Checked evidence |
| --- | --- | --- |
| A05-01 | Inventory every current query capstone. | The before/after inventory below covers `RMQPaper`, `RMQ.Headlines.RMQ`, README, artifact claims, correspondence, theorem map, family/what-is-proved surfaces, and the headline inventory. |
| A05-02 | Every current paper query theorem names the canonical physical payload/execution and `76` route. | `concreteBPNativeSuccinctRMQCanonicalReviewerPayload_globalWordTrace_two_sided_profile`; `succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`; `listIntSuccinctRMQPaperMainTheorem` with literal `queryCost = 76`. |
| A05-03 | Combine construction space and query clauses for the same object. | The shape-level profile names `CanonicalReviewerPayload`, `ReviewerPhysicalWords_erases`, direct successful-read backing in `ReviewerPhysicalWords`, `WholeQueryGlobalWordTraceResult`, `WholeQueryGlobalWordTraceCosted`, non-synthetic weight equality to trace length and cost, `<= 76`, and exact answers in one theorem. |
| A05-04 | Re-home six historical profiles. | `RMQ.Headlines.RMQCompatibility` retains six aliases beginning with `succinctRMQLegacy196727`; `RMQPaper` does not import that module. |
| A05-05 | Remove old current capstones/constants/regimes from paper surfaces and headline inventory. | `RMQ.Headlines.RMQ`, `RMQPaper`, and `scripts/headline_axiom_check.lean` contain none of the retired alias names or old cost/regime tokens; public current tables contain only canonical rows. |
| A05-06 | Preserve source theorems as compatibility results. | No construction theorem was deleted. The broad `RMQ.Headlines` barrel explicitly imports both canonical and compatibility modules; general and WordRAM inventories may check source/history theorems under explicit roles. |
| A05-07 | Add blocking regression. | `scripts/paper_topology_lint.ps1`; policy version 12 strict retired-alias term; six production-scanner mutation fixtures; aggregate gate runs the headline inventory and topology lint. |
| A05-08 | Preserve the U3 model boundary. | The new profile comment, paper docs, design decision, and compatibility boundary retain the charged-trace/non-controller/non-serialized/non-preprocessing/non-conventional-word-RAM scope. |

## Exact Public-Surface Inventory

| Surface | Before A05 correction | After A05 correction |
| --- | --- | --- |
| `RMQPaper` import closure | Canonical list/trace consumers plus six unqualified historical query profiles. | Imports only `RMQ.Headlines.RMQ`; one canonical construction profile plus canonical list/trace/adequacy consumers. |
| `RMQ.Headlines.RMQ` | Six active-looking direct/interpreted/leaf/word aliases, two size-premised, alongside canonical `76` aliases. | `succinctRMQCanonicalReviewerPayloadGlobalWordTraceTwoSidedProfile`, canonical list/main/trace/adequacy aliases only; no historical query capstone or old cost/regime token. |
| Construction-facing theorem | Old payload paired with direct query and legacy aggregate budget. | Canonical reviewer payload + exact physical erasure + direct positional backing for every successful read + canonical global trace + exactness + non-synthetic weight equal to trace length and `Costed.cost` + literal `76`, in one checked theorem. |
| README | Four historical profiles presented as current rows. | One canonical construction row and canonical execution/cost rows. |
| `artifact/CLAIMS.md` | Five historical profiles presented as current claims. | Canonical construction profile, canonical List Int, physical, provenance, store, and `76` operational rows only. |
| Paper correspondence / theorem map | Old direct profile was the construction-facing upper-bound row. | New canonical reviewer-payload/global-trace profile is the sole construction-facing row. |
| Family summary / what-is-proved | Historical and canonical capstones appeared in one current alias list. | Current alias list contains the canonical profile; history is described only through the explicit compatibility module. |
| Headline axiom inventory | Printed five historical query aliases plus transitional/regime constants. | Prints the canonical combined profile and canonical `76` chain only. |
| Compatibility reachability | Historical aliases lived in the paper module under unqualified names. | Six retained aliases and old cost/regime companions live in `RMQ.Headlines.RMQCompatibility` with `Legacy`/`Compatibility` names; broad barrel imports it explicitly. |
| W18 projections | Event-value and component-may-path projections remained in `RMQ.Headlines.RMQ` beside current occurrence-level and semantic-adequacy evidence. | Five W18 projections plus the legacy-tail theorem live only in `RMQ.Headlines.RMQCompatibility` under `CompatibilityW18`/`Legacy` names; current indexed provenance and adequacy aliases remain canonical. |
| Construction capstone type | Space, erasure, exactness, cost, and one weight/cost equality were conjoined, while successful-read backing and weight/length equality were only nearby theorems. | The checked proposition itself contains direct successful-read physical backing, weight sum = trace length, weight sum = the same `Costed.cost`, and weight sum `<= 76`, beside the existing clauses. |
| Documentary names | Selected table/token scans passed while stale transitional names remained and documentary identifiers were not elaborated. | Every non-frozen documentary headline resolves under the broad barrel; canonical paper identifiers also resolve under `RMQPaper`; removed names survive only as exact enforcement data or explicit frozen history. |

## Verification Ledger

| Check | Result |
| --- | --- |
| Focused Lean builds for `SuccinctFinalRAM`, `RMQ.Headlines.RMQ`, `RMQ.Headlines.RMQCompatibility`, the broad `RMQ.Headlines` barrel, `RMQPaper`, and `RMQExamples` | Pass; strengthened canonical two-sided profile and the canonical/compatibility import split compile together |
| Separate `lake build RMQPaper` and `lake build RMQExamples` | Pass |
| Full `lake build` | Pass |
| `lake env lean scripts/headline_axiom_check.lean` | Pass; canonical two-sided profile and direct actual-event bridge inventoried, with no compatibility alias or retired cost/regime capstone |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass; direct `nonSyntheticWeight` certificates, actual trace chain, and explicitly labeled compatibility history inventoried |
| `lake env lean scripts/axiom_check.lean` | Pass; full source inventory includes the canonical profile and operational bridge |
| `lake exe rmq_succinct_classic_validate` | Pass; 498 windows across 43 inputs, principled bound `76` |
| `lake exe rmq_succinct_classic_cost_harness` | Pass; invalid/same/cross costs `0`/`36`/`44`/`60`, all at most `76` |
| Forbidden-token and `native_decide`/`Lean.ofReduceBool` hygiene scans | Pass; no matches |
| Strict design-decision check relative to self-contained continuation base `229607f7...` | Pass; both code and workflow decisions are present for all design-sensitive changes |
| `scripts/paper_topology_lint.ps1` | Pass; 80 broad documentary identifiers and 48 canonical paper identifiers resolve; repository-wide removed-name and compatibility-current checks are clean |
| `scripts/paper_topology_lint_regression.ps1` | Pass; five reject mutations (prose, fence, dead, renamed, compatibility-current) and one canonical accept mutation; tracked state unchanged |
| Claim-policy mutation regression | Pass; 37 reject, 17 accept, 5 path/context verdicts |
| Strict claim-drift scan | Pass; 740 classified hits, 0 strict failures |
| `scripts/review_wordram.ps1` | Pass; `WORDRAM REVIEW PASS` |
| `git diff --check` | Pass before the ledger update; repeated on the completed tree before commit |
| `scripts/gate.ps1` | Pass on the completed paper-topology correction tree before commit |

All Lean invocations used the repository's pinned toolchain. The resolver-backed
topology checks required the approved execution context for toolchain access;
no proof or source change was made to work around that environment boundary.
