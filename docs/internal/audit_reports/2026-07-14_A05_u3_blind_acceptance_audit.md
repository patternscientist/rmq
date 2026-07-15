# A05 — blind acceptance audit: principled all-size RMQ cost

- Auditor: A05; mode: FRESH BLIND DELTA; permission: report-only
- Accepted base: 45e2f0d87fa28b8a1a92e570662767e191c2e987
- Audited target: 2405fbbc29ead446d8fdcf3285045435102779f9
- Candidate branch: codex/rmq-u3-principled-allsize-cost
- Report branch: codex/a05-u3-blind-acceptance-audit
- Decision: REJECT — P1 public-consumer/publication-topology blocker

## Findings first

### P0 — none

The U3 core is not a theorem wrapper around another costed object. The canonical
global result is projected directly to Costed, and that result is proved equal
to the canonical interpreted whole-query evaluator. The 76 theorem has a
same-object path.

### P1 — RMQPaper still exports active-looking 196727 capstones for different computations

RMQPaper.lean imports all of RMQ.Headlines.RMQ. That module still exports these
unqualified BP-native capstones, although their checked types use pre-U3
computations and the old 196727 budget:

| Public alias | Checked object / premise |
| --- | --- |
| succinctRMQTwoNPlusOConstantQuery | concreteBPNativeSuccinctRMQQueryCosted … <= 196727 |
| …Interpreted | WholeQueryInterpretedCosted … <= 196727 |
| …LeafTrace | WholeQueryLeafTraceCosted … <= 196727 |
| …WordTrace | WholeQueryWordTraceCosted … <= 196727 |
| …WordTraceLargeRegime | WholeQueryWordTraceCostedOfSizeGe, 2^128 <= shape.size, <= 196727 |
| …GlobalWordTraceLargeRegime | WholeQueryGlobalWordTraceCostedOfSizeGe, 2^128 <= shape.size, <= 196727 |

The first is the direct alias at RMQ/Headlines/RMQ.lean:28-29. Its source
theorem builtGenericSparseExceptionBPNativeSuccinctRMQFamily_total_two_sided_doubled_catalan_slack_profile
has the concreteBPNativeSuccinctRMQQueryCosted/196727 conclusion in
RMQ/Core/SuccinctFinal.lean:2497-2535; concreteBPNativeSuccinctRMQQueryCost_eq
reduces that budget at :16-24. The remaining active capstones are at
RMQ/Headlines/RMQ.lean:430-476; their source profiles are also curated in the
headline and WordRAM axiom inventories.

This fails U3-10: the paper root does not contain only consumers of the
canonical global 76 trace. It also fails U3-12 in letter and spirit: separate
legacy aliases are labelled compatibility, but these six paper-root aliases and
public tables still present other computations as current capstones.
README.md:68-71, artifact/CLAIMS.md:68,73-76, and
docs/PAPER_CLAIM_CORRESPONDENCE.md:54 reinforce that active presentation.

This is P1, not P0: the old theorems may be sound, but their current public
topology is incompatible with the requested one-canonical-execution claim. The
minimum coherent repair is either to replace the paper-facing capstones with
canonical-76 versions, or to remove the six old aliases from RMQPaper and
re-home them as explicitly archival compatibility declarations, including the
public tables and axiom-inventory roles. A prose disclaimer cannot change an
exported theorem type.

### P2 — none

No proof, trust-base, executable, hygiene, cost-model, or supplied-store defect
was found in the canonical U3 route.

### P3 — broad primitive classification is insufficient by itself, but U3 does not rely on it

The older predicate event.isReadWord \/ event.isWordPrimitive includes the
synthetic constructor. It would be insufficient evidence for U3-07/U3-08. The
target adds and consumes the stronger
concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_event_readWord_or_wordRank_or_wordSelect,
so this is an audit note rather than a blocker.

## Independently reconstructed canonical chain

The named algebra in RMQ/Core/SuccinctFinalRAM.lean:8635-8670 is

    wholeQuery = 2 * selectClose + closeLCA + rankClose
    closeLCA   = 2 * rankClose + 2 * endpointFringe + interiorDirectory

with the actual component caps

    selectClose = 13
    rankClose = 4
    endpointFringe = canonicalEndpointFringeChargedTraceCost = 4
    interiorDirectory = canonicalRelativeRmmPrincipledInteriorChargedTraceCost = 30

Therefore

    closeLCA = 2*4 + 2*4 + 30 = 46
    wholeQuery = 2*13 + 46 + 4 = 76.

concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq : … = 76 is
by rfl. The 13 cap refines the built sparse-exception select operation; the
4 cap refines built rank data. The LCA cap is consumed by
canonicalLcaCloseCostedWithRankSeed_cost_le_principled, then by
concreteBPNativeSuccinctRMQCanonicalQueryInterpretedCosted_cost_le_principledAllSizeChargedTrace.

The identity chain is checked, not inferred from names:

    SuccinctClassic.queryTraceResult (valid range)
      = WholeQueryGlobalWordTraceResult (cartesianShape xs)
      --toCosted-->
    WholeQueryGlobalWordTraceCosted
      = WholeQueryCanonicalInterpretedCosted
      <= named 76 component algebra.

…GlobalWordTraceCosted_eq_traceResult_toCosted is definitional and
…GlobalWordTraceCosted_refines_canonicalInterpretedCosted unfolds the same
global program then applies WholeQueryProgram.evalGlobalWordTrace_refines_eval
(SuccinctFinalRAM.lean:5323-5340). SuccinctClassic.queryTraceResult_valid
selects exactly that global trace; invalid ranges use the empty/none branch;
queryCosted_cost_le invokes the canonical 76 theorem
(SuccinctRMQClassic.lean:960-973). Neither the public theorem nor its
component path has Ready, Active, 2^128, or compatibility dispatch.

## Requirement matrix

| ID | Result | Independent evidence |
| --- | --- | --- |
| U3-01 | Pass | Named select/rank/endpoint/interior algebra above is directly used by the canonical query proof. |
| U3-02 | Pass | 13, 4, 4, and 30 are component caps on the select/rank/fringe/interior computations used by the direct-bind route. |
| U3-03 | Pass | …ChargedTraceCost_eq : … = 76 is rfl; arithmetic is reconstructed above. |
| U3-04 | Pass | …WholeQueryGlobalWordTraceCosted_cost_le_principledAllSizeChargedTrace (shape) (left) (right) is unconditional and refines the canonical interpreted evaluator. |
| U3-05 | Pass | ConcreteDirectoryRAM.lean:2476-2551 charges actual leftBlock + 1 < rightBlock. Its positive branch derives the bounded interior range, two blocks, and then 4 <= shape.size before applying the 30 theorem. Same-block/adjacent-cross-block paths take actual local/zero-middle branches; no Ready/Active/2^128 dispatch is used. |
| U3-06 | Pass | …GlobalWordTraceCosted_cost_eq_trace_length is rfl (SuccinctFinalRAM.lean:9194-9202) because the costed object is the actual trace result’s toCosted. |
| U3-07 | Pass | The exact three-constructor theorem at SuccinctFinalRAM.lean:7168-7195 excludes synthetic fallback; …syntheticCostOnlyPrimitive_not_mem states its absence. |
| U3-08 | Pass | Actual-event classification -> unit nonSyntheticWeight -> sum = trace length -> sum = the same Costed.cost -> <= named cap = 76 (:7198-7214, :9206-9270). toCosted always charges length; the certificate is deliberately distinct. |
| U3-09 | Pass | syntheticCostOnlyPrimitive_not_readWord_or_wordRank_or_wordSelect, sum_nonSyntheticWeight_ne_length_of_synthetic_mem, and syntheticCostOnlyPrimitive_cons_weight_sum_ne_length make classification or equality fail after synthetic insertion (WordRAM.lean:280-313). |
| U3-10 | Fail (P1) | List Int adequacy/supplied-store/headline consumers use 76, but RMQPaper simultaneously imports the six active 196727/different-execution capstones. |
| U3-11 | Pass | U3 retains canonical trace refinement, payload/store/footprint/provenance/width and guarded invalid-range consumers. The same list queryTraceResult/queryCosted is used by adequacy and supplied-store equality; builds and validators passed. |
| U3-12 | Fail (P1) | 328 is same-trace transitional, 4144 compatibility, and 118 Ready-premised pre-canonical source-only; the six exported 196727 profiles remain active-looking and two retain 2^128. |
| U3-13 | Pass | WordRAM.lean:159-168 and docs/PAPER_MAIN_THEOREM.md:92-96 scope 76 to charged trace events and exclude controller work, serialized-payload querying, preprocessing, Lean runtime, and conventional word-RAM complexity claims. |

## Consumers, preservation, and stale objections

Correct canonical consumers exist and type-check:

- SuccinctFinal.concreteBPNativeSuccinctRMQFinalFullModelSoundness_cost_le_of_footprint_global_principledAllSizeChargedTrace transfers 76 to an agreeing supplied store (SuccinctFinalModelAdequacy.lean:613-624).
- SuccinctClassic.queryCostedWithStore_eq_queryCosted_of_footprint, listIntFinalFullModelCostLeOfFootprintGlobal, and its explicit U3 alias retain the same list-facing query and footprint premise (SuccinctRMQClassic.lean:977-1055).
- Headlines.listIntSuccinctRMQPaperMainTheorem consumes the list no-synthetic profile.

The stale objection that 328 is the current canonical theorem is retired: it is
a same-trace transitional corollary below 76. Ready/118, 4144, zero-block, and
bare 2^128 activation are not used by U3’s canonical proof. The live issue is
public: 196727 and two 2^128-gated profiles remain paper-root capstones.

## Evidence tiers and verification

### Tier 1 — source and checked theorem types

The decision rests on the definitions/types and import topology cited above,
not theorem names or worker narrative. I did not open worker chats, completion
reports, coordinator verdicts, or earlier audit reports. The required broad
claim-drift tool mechanically listed pre-existing audit-report paths in its
output; those entries were not opened or used as audit evidence.

### Tier 2 — local mechanical verification

All final checks passed at the exact target:

- focused rebuild of SuccinctFinalRAM, model adequacy, classic surface,
  headlines, RMQPaper, and RMQExamples;
- lake build (203 targets) and explicit lake build RMQ.Core.GenericSelectBPCompat;
- scripts/axiom_check.lean, scripts/headline_axiom_check.lean, and
  scripts/wordram_axiom_check.lean (only standard axioms displayed);
- lake exe rmq_succinct_classic_validate (498 windows over 43 deterministic
  inputs) and lake exe rmq_succinct_classic_cost_harness (0–60 charged ticks,
  all <= 76 and exact List Int answers);
- scripts/review_wordram.ps1, strict claim_drift_scan.ps1, strict
  design_decision_check.ps1 -Base 45e2f0d…, both hygiene scans, and
  scripts/gate.ps1 (GATE PASS).

The first focused build had missing intermediate .olean files while an
independent check was compiling in the shared worktree; its serial retry
passed. The first WordRAM-script attempt was blocked by sandboxed dependency
download; the approved retry passed. Neither was a Lean proof diagnostic.

### Tier 3 — exact-commit CI/artifact evidence (secondary)

GitHub reports successful Lean gate (actions/runs/29375838268) and Reproduce
artifact (actions/runs/29375838231) checks for 2405fbbc…. The latter has
non-expired audit-packet and artifact-reproduction-log artifacts. This
corroborates reproducibility; it does not replace Tier 1.

## Roadmap alignment and proof digestion

In substance U3 advances the roadmap: it gives one all-size charged-trace bound
for the unchanged execution, with a genuine-event certificate and a real
synthetic-mutation falsifier. It does not finish the publication node because a
reader importing RMQPaper can still cite incompatible active-looking capstones.
The next acceptance target is a canonical-76 paper-facing profile/export
migration, followed by another fresh blind delta audit.

Conceptually, 76 is not an asserted label; it is the sum of the exact select,
rank, fringe, and interior operations in one canonical trace. In plain English,
a synthetic cost-only event cannot silently contribute to 76 because it breaks
the certificate equality. The live assumptions are the component caps and the
charged-trace model, not controller time, serialized-payload querying,
preprocessing, Lean runtime, or conventional word-RAM complexity. A skeptical
graduate student should ask which theorem in the paper import root they should
cite. Until P1 is repaired, the answer is not uniquely the canonical 76
execution.
