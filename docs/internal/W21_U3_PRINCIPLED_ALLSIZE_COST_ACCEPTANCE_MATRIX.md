# W21 U3 Principled All-Size Charged-Trace Cost Acceptance Matrix

Branch: `codex/rmq-u3-principled-allsize-cost`

Base: `45e2f0d87fa28b8a1a92e570662767e191c2e987`

Operational-bridge continuation base:
`c2694b7156f5e8ad321e16e3f36bc57284d55820`.

Paper-topology correction base:
`2405fbbc29ead446d8fdcf3285045435102779f9`.

Blind A05 report read directly, without merge:
`64cfd2dae2de9b8402fd5601b0e6d0b146a0ca61` on
`codex/a05-u3-blind-acceptance-audit`.

Status: `CANDIDATE_COMPLETE` after the A05 publication-topology correction;
fresh blind exact-commit audit remains coordinator-owned.

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
| A05-03 | Combine construction space and query clauses for the same object. | The new shape-level profile names `CanonicalReviewerPayload`, `ReviewerPhysicalWords_erases`, `WholeQueryGlobalWordTraceResult`, `WholeQueryGlobalWordTraceCosted`, non-synthetic weight equality, `<= 76`, and exact answers in one theorem. |
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
| Construction-facing theorem | Old payload paired with direct query and legacy aggregate budget. | Canonical reviewer payload + exact physical erasure + canonical global trace + exactness + non-synthetic weight equality + literal `76`, in one checked theorem. |
| README | Four historical profiles presented as current rows. | One canonical construction row and canonical execution/cost rows. |
| `artifact/CLAIMS.md` | Five historical profiles presented as current claims. | Canonical construction profile, canonical List Int, physical, provenance, store, and `76` operational rows only. |
| Paper correspondence / theorem map | Old direct profile was the construction-facing upper-bound row. | New canonical reviewer-payload/global-trace profile is the sole construction-facing row. |
| Family summary / what-is-proved | Historical and canonical capstones appeared in one current alias list. | Current alias list contains the canonical profile; history is described only through the explicit compatibility module. |
| Headline axiom inventory | Printed five historical query aliases plus transitional/regime constants. | Prints the canonical combined profile and canonical `76` chain only. |
| Compatibility reachability | Historical aliases lived in the paper module under unqualified names. | Six retained aliases and old cost/regime companions live in `RMQ.Headlines.RMQCompatibility` with `Legacy`/`Compatibility` names; broad barrel imports it explicitly. |

## Verification Ledger

| Check | Result |
| --- | --- |
| Focused Lean builds for `SuccinctFinalRAM`, `SuccinctFinalModelAdequacy`, `SuccinctRMQClassic`, `RMQ.Headlines.RMQ`, `RMQ.Headlines.RMQCompatibility`, the broad `RMQ.Headlines` barrel, `RMQPaper`, and `RMQExamples` | Pass; strengthened canonical two-sided profile and the canonical/compatibility import split compile together |
| Separate `lake build RMQPaper` and `lake build RMQExamples` | Pass |
| Full `lake build` | Pass |
| `lake env lean scripts/headline_axiom_check.lean` | Pass; canonical two-sided profile and direct actual-event bridge inventoried, with no compatibility alias or retired cost/regime capstone |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass; direct `nonSyntheticWeight` certificates, actual trace chain, and explicitly labeled compatibility history inventoried |
| `lake env lean scripts/axiom_check.lean` | Pass; full source inventory includes the canonical profile and operational bridge |
| `lake exe rmq_succinct_classic_validate` | Pass; 498 windows across 43 inputs, principled bound `76` |
| `lake exe rmq_succinct_classic_cost_harness` | Pass; invalid/same/cross costs `0`/`36`/`44`/`60`, all at most `76` |
| Forbidden-token and `native_decide`/`Lean.ofReduceBool` hygiene scans | Pass; no matches |
| Strict design-decision check relative to paper-topology base `2405fbbc...` | Pass; 31 changed files checked, coequal historical topology rejected, and workflow boundary recorded |
| `scripts/paper_topology_lint.ps1` | Pass; canonical-only paper import/current surfaces and explicit compatibility naming enforced |
| Claim-policy mutation regression | Pass; 32 reject, 17 accept, 5 path/context verdicts |
| Strict claim-drift scan | Pass; 731 classified hits, 0 strict failures |
| `scripts/review_wordram.ps1` | Pass; `WORDRAM REVIEW PASS` |
| `git diff --check` | Pass before the ledger update; repeated on the completed tree before commit |
| `scripts/gate.ps1` | Pass on the completed paper-topology correction tree before commit |

The first focused build attempt did not reach Lean because the restricted
network sandbox blocked access to the pinned toolchain download. The approved
network-enabled rerun and every subsequent build/check completed successfully;
no proof or source change was made to work around the sandbox.
