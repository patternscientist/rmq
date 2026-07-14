# W21 U3 Principled All-Size Charged-Trace Cost Acceptance Matrix

Branch: `codex/rmq-u3-principled-allsize-cost`

Base: `45e2f0d87fa28b8a1a92e570662767e191c2e987`

Operational-bridge continuation base:
`c2694b7156f5e8ad321e16e3f36bc57284d55820`.

Status: `CANDIDATE_COMPLETE`; the exact commit and push are recorded at handoff.

## Requirement-to-Theorem Matrix

| ID | Requirement | Checked consumer |
| --- | --- | --- |
| U3-01 | Reconstruct named primitive composition. | `CanonicalRMQChargedTraceCostAlgebra.closeLCA`, `.wholeQuery`; `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra` |
| U3-02 | Tighten every conservative `328` contribution. | `sparseExceptionSelectSource_selectPositionCosted_cost_le_thirteen`; `rankCosted_cost_le_four`; `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded` |
| U3-03 | Prove one canonical numeric equality. | `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 76` |
| U3-04 | Bound the unchanged executable trace and expose exact accounting. | `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect`; `..._syntheticCostOnlyPrimitive_not_mem`; `..._chargedWeight_sum_eq_trace_length`; `..._chargedWeight_sum_eq_cost`; `..._chargedWeight_sum_le_76` |
| U3-05 | Consume final adequacy and supplied-store footprints. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy.event_readWord_or_wordRank_or_wordSelect`; `.chargedWeight_sum_eq_trace_length`; `.chargedWeight_sum_eq_cost`; `.chargedWeight_sum_le_76`; `concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace` |
| U3-06 | Consume ordinary `List Int`, headlines, and paper root. | `SuccinctClassic.queryCosted_cost_le`; `listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal`; `Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe`; `RMQPaper` |
| U3-07 | Preserve U2 payload, route, physical erasure, store dependence, footprints, provenance, width, and invalid semantics. | No execution/payload definition is replaced; existing final adequacy, exactness, physical, provenance, and invalid-range theorems remain consumers beside the new cost field. |
| U3-08 | Connect the cost inventory to actual emitted events without a parallel operation vocabulary. | `WordRAM.TraceEvent.chargedWeight`; actual three-constructor classification; actual no-synthetic theorem; actual weight-sum = trace-length = `Costed.cost` = at most `76`; `syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect`; `sum_chargedWeight_ne_length_of_synthetic_mem` |
| U3-09 | Keep conventional word-RAM / serialization / preprocessing outside U3. | Theorem names contain `ChargedTrace`; design decision, family summary, paper maps, claim policy, and roadmap state the nonclaims. |
| U3-10 | Preserve transitional evidence without artificial work. | `concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq = 328` remains separately named; no padding or decorative event is introduced. |

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

Charged at unit weight: attempted payload-word reads, word-rank primitives,
and word-select primitives.

Checked execution chain: every event in the actual canonical whole-query trace
is one of those three constructors; the synthetic fallback is absent; direct
event weights sum to trace length and to the `Costed` cost of the same
execution; the sum is at most `76`. Counterfactually, a synthetic event cannot
meet the genuine-event classification, and its presence anywhere makes the
weight sum strictly smaller than trace length.

Currently uncharged: instruction dispatch; input and register access;
option tests and branching; natural-number arithmetic, address and slot
calculation; fixed-width decoding; local BP scanning; candidate comparison and
merge; trace assembly; and the public valid-range guard. This list is
documentary: U3 does not expose a checked controller-operation vocabulary. E1
must define the richer instruction semantics and prove that it simulates the
same execution.

Therefore U3 does not prove `query(serializedPayload,left,right)`, full
preprocessing complexity, compiled Lean time, or conventional word-RAM time.

## Verification Ledger

| Check | Result |
| --- | --- |
| Focused Lean builds for `GenericSelect.Source`, `InteriorDirectory`, `ConcreteDirectoryRAM`, `WordRAM`, `SuccinctFinalRAM`, `SuccinctFinalModelAdequacy`, `SuccinctRMQClassic`, and `RMQ.Headlines.RMQ` | Pass |
| `lake build RMQPaper RMQExamples` | Pass |
| `lake build RMQ` and fresh-worktree inventory prerequisites | Pass |
| Full `lake build` | Pass |
| `lake env lean scripts/headline_axiom_check.lean` | Pass; direct actual-event bridge and counterfactual aliases inventoried |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass; direct weights, actual trace chain, and expected Lean logical axioms inventoried |
| `lake env lean scripts/axiom_check.lean` | Pass; full barrel inventory includes the operational bridge |
| `lake exe rmq_succinct_classic_validate` | Pass; 498 windows across 43 inputs, principled bound `76` |
| `lake exe rmq_succinct_classic_cost_harness` | Pass; invalid/same/cross costs `0`/`36`/`44`/`60`, all at most `76` |
| Forbidden-token and `native_decide`/`Lean.ofReduceBool` hygiene scans | Pass; no matches |
| Strict design-decision check relative to continuation base `c2694b7...` | Pass; rejected parallel abstraction and workflow boundary recorded |
| Claim-policy mutation regression | Pass; 26 reject, 15 accept, 5 path/context verdicts |
| Strict claim-drift scan | Pass; 706 classified hits, 0 strict failures |
| `scripts/review_wordram.ps1` | Pass after permitting its GitHub cache access; `WORDRAM REVIEW PASS` |
| `git diff --check` | Pass before the ledger update; repeated on the completed tree before commit |
| `scripts/gate.ps1` | Pass on the completed operational-bridge tree before commit |

The first `review_wordram.ps1` attempt was blocked only because its cache step
could not reach GitHub inside the restricted network sandbox. The approved
network-enabled rerun completed successfully. No proof or source change was
made between those attempts.
