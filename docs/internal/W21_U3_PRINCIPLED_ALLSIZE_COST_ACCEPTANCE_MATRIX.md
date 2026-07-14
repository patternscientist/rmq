# W21 U3 Principled All-Size Charged-Trace Cost Acceptance Matrix

Branch: `codex/rmq-u3-principled-allsize-cost`

Base: `45e2f0d87fa28b8a1a92e570662767e191c2e987`

Status: `CANDIDATE_COMPLETE`; the exact commit and push are recorded at handoff.

## Requirement-to-Theorem Matrix

| ID | Requirement | Checked consumer |
| --- | --- | --- |
| U3-01 | Reconstruct named primitive composition. | `CanonicalRMQChargedTraceCostAlgebra.closeLCA`, `.wholeQuery`; `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCostAlgebra` |
| U3-02 | Tighten every conservative `328` contribution. | `sparseExceptionSelectSource_selectPositionCosted_cost_le_thirteen`; `rankCosted_cost_le_four`; `canonicalRelativeRmmInteriorRangeMinCosted_cost_le_thirty_of_size_ge_four_of_bounded` |
| U3-03 | Prove one canonical numeric equality. | `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : ... = 76` |
| U3-04 | Bound the unchanged executable trace and expose exact accounting. | `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace`; `...cost_eq_trace_length` |
| U3-05 | Consume final adequacy and supplied-store footprints. | `ConcreteBPNativeSuccinctRMQFinalTraceModelAdequacy.cost_le`; `concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace` |
| U3-06 | Consume ordinary `List Int`, headlines, and paper root. | `SuccinctClassic.queryCosted_cost_le`; `listIntPrincipledAllSizeChargedTraceCostLeOfFootprintGlobal`; `Headlines.succinctRMQWholeQueryGlobalWordTraceCostedCostLe`; `RMQPaper` |
| U3-07 | Preserve U2 payload, route, physical erasure, store dependence, footprints, provenance, width, and invalid semantics. | No execution/payload definition is replaced; existing final adequacy, exactness, physical, provenance, and invalid-range theorems remain consumers beside the new cost field. |
| U3-08 | Inventory charged and uncharged operations for E1. | `CanonicalRMQCostOperation`; `canonicalRMQCurrentTraceWeight`; checked charged and zero-weight list equalities |
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

Currently uncharged: instruction dispatch; input and register access;
option tests and branching; natural-number arithmetic, address and slot
calculation; fixed-width decoding; local BP scanning; candidate comparison and
merge; trace assembly; and the public valid-range guard.

Therefore U3 does not prove `query(serializedPayload,left,right)`, full
preprocessing complexity, compiled Lean time, or conventional word-RAM time.

## Verification Ledger

| Check | Result |
| --- | --- |
| Focused Lean builds for `GenericSelect.Source`, `InteriorDirectory`, `ConcreteDirectoryRAM`, `SuccinctFinalRAM`, and `SuccinctRMQClassic` | Pass |
| `lake build RMQPaper RMQExamples` | Pass |
| `lake build RMQ` and fresh-worktree inventory prerequisites | Pass |
| Full `lake build` | Pass |
| `lake env lean scripts/headline_axiom_check.lean` | Pass; current numeric equality is axiom-free |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass; expected Lean logical axioms only |
| `lake env lean scripts/axiom_check.lean` | Pass; full barrel inventory |
| `lake exe rmq_succinct_classic_validate` | Pass; 498 windows across 43 inputs, principled bound `76` |
| `lake exe rmq_succinct_classic_cost_harness` | Pass; invalid/same/cross costs `0`/`36`/`44`/`60`, all at most `76` |
| Forbidden-token and `native_decide`/`Lean.ofReduceBool` hygiene scans | Pass; no matches |
| Strict base-relative design-decision check | Pass; code and workflow decisions recorded |
| Claim-policy mutation regression | Pass; 26 reject, 15 accept, 5 path/context verdicts |
| Strict claim-drift scan | Pass; 691 classified hits, 0 strict failures |
| `scripts/review_wordram.ps1` | Pass after permitting its GitHub cache access; `WORDRAM REVIEW PASS` |
| `git diff --check` | Pass before the ledger update; repeated on the completed tree before commit |
| `scripts/gate.ps1` | Pass on the completed source tree in 320.4 seconds; repeated after this ledger update before commit |

The first `review_wordram.ps1` attempt was blocked only because its cache step
could not reach GitHub inside the restricted network sandbox. The approved
network-enabled rerun completed successfully. No proof or source change was
made between those attempts.
