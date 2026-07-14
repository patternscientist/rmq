# A04 — Blind U2 exact-commit acceptance audit

Date: 2026-07-14
Repository: `C:\Users\poin\Documents\RMQ`
Base: `0c5d4224f158e9aa9a757f51789790dc04ffa264`
Target: `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`
Audited target branch: `codex/rmq-u2-positional-provenance`
Report branch: `codex/a04-u2-blind-acceptance-audit`
Permitted edit: this report only

## Findings first

### P0

None.

### P1

None.

### P2

None.

### P3 — stale comments falsely describe synthetic fallback on the active path

`RMQ/Core/SuccinctFinalRAM.lean:3838-3843`, `:4400-4405`, and
`:7529-7532` still say that tiny/inactive fallback work is retained as
synthetic word primitives in the all-size global execution. That is no longer
true of the definitions immediately below the comments.

The executable path is `WholeQueryInstr.evalGlobalWordTrace` ->
`WholeQueryProgram.evalGlobalWordTrace` ->
`concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult`, and the kernel
checks the opposite claim in:

- `WholeQueryInstr.evalGlobalWordTrace_no_syntheticCostOnlyPrimitive`
  (`RMQ/Core/SuccinctFinalRAM.lean:3428`);
- `WholeQueryProgram.evalGlobalWordTrace_no_syntheticCostOnlyPrimitive`
  (`:4045`);
- the final trace use at `:7159`; and
- `concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore_no_syntheticCostOnlyPrimitive`
  (`RMQ/Core/SuccinctFinalStoreParam.lean:3320-3339`).

This is comment-only drift. It does not alter a definition, theorem type,
import, payload, trace, cost, or public claim, so it is a follow-up rather than
an acceptance blocker. The comments should be corrected in a separate change.

## Verdict

**Merge-ready with follow-up.**

U2 satisfies REQ-01 through REQ-08 in both letter and spirit. The target
supplies one all-size execution route whose public `List Int` payload, physical
word list, supplied-store evaluator, positional trace, occurrence provenance,
word model, paper theorem, and headline aliases are one checked chain. The
canonical public modeled bound is uniformly `328`. The P3 comment drift above
is the only finding.

## Blind protocol and exact delta

This audit was performed in a fresh worktree created directly at the target
commit. The repository worker ledger and prior audit reports were not opened or
used as technical evidence; documentation, theorem names, and green scripts
were not accepted without expanding the definitions and following the actual
consumer chain. Read-only subaudits independently challenged payload/provenance,
positional/word-model, and public/cost/policy surfaces. The lead audit then
reconstructed their join and ran the final gate.

Exact-object checks established:

- the base and target objects exist;
- `codex/rmq-u2-positional-provenance` resolves to the target;
- the base is an ancestor of the target and is their merge base;
- the audit worktree began clean at the target; and
- `BASE..TARGET` is 71 files, 24,172 insertions, and 1,604 deletions.

No Lean source, public claim, policy, roadmap, skill, ledger, or audited branch
was modified by this audit.

## Frozen-requirement decision matrix

| Requirement | Decision | Load-bearing evidence |
|---|---|---|
| REQ-01 | Pass | `SuccinctClassic.buildPayload` is definitionally the canonical reviewer payload (`RMQ/Core/SuccinctRMQClassic.lean:113-118`). `concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases` proves literal flattening of the physical words to that payload (`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean:762-792`). `buildPayload_length` and `overhead_littleO` prove the same object's length is at most `2*n + overhead n`, with `overhead = o(n)` (`RMQ/Core/SuccinctFinal/RAM/FlatPayload.lean:1805-1815`, `:1906-1931`). |
| REQ-02 | Pass | One 20-constructor `ReviewerSource` and one exhaustive source list/map describe the live sources (`ReviewerPhysical.lean:24-68`, `:82-106`). Load-bearing liveness is a successful indexed occurrence in an actual closed valid top-level query, not `ReviewerSource.Live`, enumeration, a may-read label, or event-value membership (`RMQ/Core/SuccinctFinalRAM.lean:6707-6757`; `ReviewerReachability.lean:14-53`). |
| REQ-03 | Pass | Segment-to-region offsets, in-range reads, one-past-end dead translation, and exact store equality are checked in `ReviewerPhysical.lean:925-1001`, `:1087-1139`, and `:1166-1257`. The physical evaluator installs the adapter before evaluation and preserves value, cost, exact ordered trace, and footprint, including failed/repeated reads (`RMQ/Core/SuccinctFinalStoreParam.lean:2894-2960`, `:3009-3036`, `:3094-3225`, `:3259-3275`). |
| REQ-04 | Pass | One query-independent `reviewerWordBits n` bounds input operands, segment encodings, the dead address, every translated physical address, every stored/returned word, primitive operands/results, and all footprint addresses (`ReviewerPhysical.lean:1413-1490`, `:1812-1858`, `:1974-2119`; `SuccinctFinalStoreParam.lean:3300-3369`). |
| REQ-05 | Pass | Capacity is concrete: `reviewerCapacity n = 400000 * (n + 1)`. Physical length is bounded by it and `reviewerWordBits n = log2(capacity)+1` is then bounded logarithmically by input length (`ReviewerPhysical.lean:1413-1467`, `:1771-1810`). The capacity proof uses direct component bounds, including the close store's linear bound; it is not inferred from `LittleOLinear`. |
| REQ-06 | Pass | Final trace adequacy consumes the physical erasure, evaluator/refinement/footprint, provenance, capacity, and width fields in one structure (`RMQ/Core/SuccinctFinalModelAdequacy.lean:25-370`). `SuccinctClassic.FlatPayloadStoreNoSyntheticExecutionStory` consumes that route (`RMQ/Core/SuccinctRMQClassic.lean:597-777`); the List theorem and paper theorem retain the same `xs`, payload, physical words/store, execution, and width (`:1099-1208`; `RMQ/Headlines/RMQ.lean:62-187`). `RMQPaper.lean:1` imports that headline root. |
| REQ-07 | Pass | The direct canonical trace theorem is `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceCosted_cost_le_canonicalTransitional`; the checked equality `concreteBPNativeSuccinctRMQCanonicalTransitionalQueryCost_eq : ... = 328` is by `rfl` (`RMQ/Core/SuccinctFinalRAM.lean:8937-8957`). List transfer and public aliases are `SuccinctRMQClassic.lean:931-949`, `:1019-1035`, and `RMQ/Headlines/RMQ.lean:561-612`. `4144` and `196727` are explicitly compatibility/legacy; `118`, zero-block, and `2^128` survive only on old/proof-only surfaces. |
| REQ-08 | Pass | Active supplied-store close evaluation has same-block/cross-block structural dispatch only. Ready/Active and zero-block branches are retained only in explicitly legacy definitions (`RMQ/Core/SuccinctClose/RelativeRmmMacro/ConcreteDirectoryRAMStoreParam.lean:3624-3646`, `:4578-4620`, `:5307-5332`). The answer is computed by the supplied-store evaluator, every successful read is charged/backed, and no synthetic event remains (`SuccinctFinalStoreParam.lean:2931-3007`, `:3279-3339`). Symbolic reachability witnesses enter the proof headline, not native validator/harness imports. |

## Exact identity and execution chain

The checked chain is:

1. `SuccinctClassic.buildPayload xs` unfolds to
   `concreteBPNativeSuccinctRMQCanonicalReviewerPayload
   (Cartesian.cartesianShape xs)`.
2. That payload is the literal concatenation of the BP code, all counted access
   sources, and the consolidated canonical-close source
   (`FlatPayload.lean:1838-1882`). There is no padding constructor or sibling
   appendix.
3. `concreteBPNativeSuccinctRMQReviewerPhysicalWords` is exactly the 20-source
   manifest mapped to source words and flattened into one physical store
   (`ReviewerPhysical.lean:509-604`).
4. `concreteBPNativeSuccinctRMQReviewerPhysicalWords_erases` identifies the
   flattened physical words with the public payload. Since
   `flattenPayloadWords` is literal list concatenation
   (`RMQ/Core/SuccinctSpace/WordStore.lean:75-78`), this is object identity, not
   length equality manufactured by padding.
5. `concreteBPNativeSuccinctRMQReviewerPhysicalStoreAdapter` translates each
   logical read to an offset-checked physical address before calling
   `physicalStore.readWord?` (`SuccinctFinalStoreParam.lean:2894-2923`).
6. `concreteBPNativeSuccinctRMQWholeQueryFlatPhysicalTraceResultWithStore`
   evaluates the ordinary supplied-store machine against that adapter; its
   answer is `logicalResult.value`, not an independently supplied witness
   (`:2931-2960`).
7. Refinement, exact ordered footprint determinism, successful-read backing,
   no-synthetic execution, and value dependency connect that evaluator to the
   canonical logical route (`:2989-3369`).
8. Final adequacy, the List story, the paper theorem, and headlines project the
   same objects rather than pairing old wrappers with a new appendix.

## Source manifest and operational provenance

### Exhaustive physical sources

`ReviewerSource` contains exactly:

1. `sharedBPCode`
2. `finalRankSuperFalse`
3. `finalRankBlockFalse`
4. `selectSuperBaseOccurrence`
5. `selectSuperBaseWordIndex`
6. `selectSuperRankBefore`
7. `selectSuperFirstOffset`
8. `selectLocalBaseOccurrence`
9. `selectLocalBaseWordIndex`
10. `selectLocalRankBefore`
11. `selectLocalFirstOffset`
12. `selectLongFlagRankSuperTrue`
13. `selectLongFlagRankBlockTrue`
14. `selectLongFlagBits`
15. `selectLongRelative`
16. `selectSparseRankSuperTrue`
17. `selectSparseRankBlockTrue`
18. `selectSparseFlagBits`
19. `selectSparseRelative`
20. `canonicalClose`

The list is duplicate-free, includes every constructor, maps injectively to
physical regions, and covers precisely logical segments `0..20`
(`ReviewerPhysical.lean:181-190`, `:259-265`, `:797-856`). Legacy close siblings
are explicitly excluded (`:489-507`).

### Positive P, mutation Q, and checked bridge

The load-bearing positive predicate is:

```lean
def ReviewerProducerClaim.HasSuccessfulClosedValidOccurrence
    (claim : ReviewerProducerClaim) : Prop :=
  ∃ word, claim.HasClosedValidOccurrence (some word)
```

The mutation predicate is:

```lean
def ReviewerProducerClaim.HasOperationalProducer
    (claim : ReviewerProducerClaim) : Prop :=
  ∃ word?, claim.HasClosedValidOccurrence word?
```

The checked bridge is
`ReviewerProducerClaim.hasOperationalProducer_of_successful`
(`RMQ/Core/SuccinctFinalRAM.lean:6738-6757`).

Expanding `HasClosedValidOccurrence` (`:6707-6736`) requires an ordinary
`List Int` query satisfying the exact public validity boundary; an indexed
top-level event occurrence; its folded pre-state, instruction index, and local
event position; `WholeQueryProgram.ProducesEventAt`; an actual
`WholeQueryInstr.InvokesReviewerRead`; the matching read leaf; and the same
component-local occurrence. Thus P and Q cannot be proved by a source name,
event-value membership, enumeration, or a component's possible-read set.

Manifest liveness is correctly global existential evidence: every counted
source has some successful closed valid query occurrence
(`ReviewerReachability.lean:14-53`). Current-query adequacy remains
parameterized by the exact `xs`, `left`, `right`, and indexed occurrence of
that query in
`concreteBPNativeSuccinctRMQWholeQueryOccurrenceProvenance_checked`
(`SuccinctFinalRAM.lean:6868-6948`) and its List projection
(`SuccinctRMQClassic.lean:788-798`). The theorem does not pretend that every
query reads every source.

## Adversarial tests

| Challenge | Result and exact evidence |
|---|---|
| Add a dead source | Rejected. A new constructor breaks exhaustive constructor/list coverage. More strongly, fresh segment 21 with the plausible `.canonicalClose` label is rejected by `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource_no_producer` under Q itself (`SuccinctFinalRAM.lean:6808-6848`). |
| Remove an operational source | Rejected by every-constructor listing, segment coverage, and counted-source successful occurrence. The older static `ReviewerSource.Live` removal lemma (`ReviewerPhysical.lean:436-450`) is compatibility evidence only and was not used as the acceptance argument. |
| Forge a consumer without an evaluator edge | Rejected because `HasClosedValidOccurrence` requires `InvokesReviewerRead`, the matching leaf, and `ProducesEventAt` at the same indexed top-level occurrence. A hand-written consumer label cannot inhabit P or Q. |
| Replace liveness by `True`, membership, or another tautology | Such mutants are explicitly exposed at `ReviewerPhysical.lean:386-434`, but the decisive reason is that final semantic adequacy requires P and current-query occurrence provenance, neither of which unfolds to enumeration or `True`. |
| Repeat equal event values | Preserved by position. `repeated_equal_read_occurrences_have_distinct_receipts` gives distinct indexed receipts despite equal events (`SuccinctFinalRAM.lean:6950-6975`). |
| Confuse component attempts, successful reads, and closed reachability | Kept separate. Compatibility may-path facts are named as such; P requires a successful `some word`; Q allows failed/dead reads but still requires an actual closed valid occurrence. Per-query provenance quantifies every emitted occurrence. |
| Make liveness query-local | Rejected by the type split: counted-source P is global existential evidence, while current-query provenance carries that exact query's parameters and occurrence position. |
| Add canonical segment 21 | Rejected by `...FreshUnusedCanonicalSource_no_producer`, using the same Q relation as accepted sources and the checked theorem that emitted canonical reads have segment `< 21`. |
| Compute the answer independently of supplied storage | Rejected structurally. The physical evaluator runs the supplied-store evaluator after installing the adapter. `...value_eq_suppliedStoreEvaluator` and `...value_ne_of_suppliedStoreEvaluator_value_ne` expose the value chain; full trace disagreement on a consumed physical address is checked at `SuccinctFinalStoreParam.lean:3094-3162`. |
| Drop failed/dead or repeated reads | Rejected. Every logical event, including `none`, is translated; the physical footprint is the ordered trace projection, not a set (`SuccinctFinalStoreParam.lean:3009-3036`, `:3208-3225`, `:3357-3369`). |
| Let proof-only symbolic witnesses enter executables | Rejected by imports. `RMQ/Core/SuccinctRMQClassic.lean` imports the implementation/model adequacy, and the validator/harness import it. `ReviewerReachability*` enters only through `SuccinctFinalSemanticProvenanceAdequacy` -> `SuccinctRMQClassicProvenance` -> the theorem headline. |
| Preserve the old defect behind a technically correct wrapper | Rejected. The delta changes the public `buildPayload`, `queryCost`, guarded trace result, actual store adapter, physical evaluator, adequacy structure, List story, and paper theorem. The consumer chain terminates in the new definitions rather than merely exporting aliases of an old route. |

## Physical segments, offsets, failures, and word bounds

| Logical segment | Physical region | Source | Positional behavior |
|---:|---:|---|---|
| 0 | 0 | `sharedBPCode` | Guarded BP-prefix alias into the one stored shared BP region |
| 1 | 3 | `selectSuperBaseOccurrence` | Region offset plus checked local index |
| 2 | 4 | `selectSuperBaseWordIndex` | Region offset plus checked local index |
| 3 | 5 | `selectSuperRankBefore` | Region offset plus checked local index |
| 4 | 6 | `selectSuperFirstOffset` | Region offset plus checked local index |
| 5 | 7 | `selectLocalBaseOccurrence` | Region offset plus checked local index |
| 6 | 8 | `selectLocalBaseWordIndex` | Region offset plus checked local index |
| 7 | 9 | `selectLocalRankBefore` | Region offset plus checked local index |
| 8 | 10 | `selectLocalFirstOffset` | Region offset plus checked local index |
| 9 | 11 | `selectLongFlagRankSuperTrue` | Region offset plus checked local index |
| 10 | 12 | `selectLongFlagRankBlockTrue` | Region offset plus checked local index |
| 11 | 13 | `selectLongFlagBits` | Region offset plus checked local index |
| 12 | 14 | `selectLongRelative` | Region offset plus checked local index |
| 13 | 15 | `selectSparseRankSuperTrue` | Region offset plus checked local index |
| 14 | 16 | `selectSparseRankBlockTrue` | Region offset plus checked local index |
| 15 | 17 | `selectSparseFlagBits` | Region offset plus checked local index |
| 16 | 18 | `selectSparseRelative` | Region offset plus checked local index |
| 17 | 1 | `finalRankSuperFalse` | Region offset plus checked local index |
| 18 | 2 | `finalRankBlockFalse` | Region offset plus checked local index |
| 19 | 0 | `sharedBPCode` | Full sentinel-capable view of the same stored BP region |
| 20 | 19 | `canonicalClose` | Consolidated canonical-close region |
| >= 21 | none | none | Unique dead address, one past `reviewerPhysicalWords.length` |

`RegionOffset` is the flattened length of preceding physical regions;
`SegmentOffset?` applies the segment/region map. An unmapped segment or an
out-of-range local index translates to the unique one-past-end dead address,
which reads `none` and cannot alias the next component
(`ReviewerPhysical.lean:925-1001`). The exact slice/get theorems are
`:1087-1139`; the universal logical-to-physical read-store equality, including
failed reads, is `:1166-1241`.

The common width model is independent of the query:

```text
capacity(n) = 400000 * (n + 1)
wordBits(n) = Nat.log2(capacity(n)) + 1
wordBits(n) <= 20 * (Nat.log2(n + 2) + 1)
```

Checked consumers cover input indices, segment encodings including dead
segments, region/local encodings, the one-past-end address, every translated
physical address, every stored and successfully returned word, every primitive
operand/result, and every footprint address. The proof uses physical-store
capacity and direct component bounds, so the logarithmic conclusion does not
come from a little-o statement.

## Uniform cost and route retirement

The public cost is not a wrapper around the old constants. At the target,
`SuccinctClassic.queryCost` unfolds to the canonical formula
(`RMQ/Core/SuccinctRMQClassic.lean:98-104`): three select calls of cost 16 plus
canonical close cost `8 + 2*16 + 240`, hence `328`. The global trace theorem
proves this direct evaluator is bounded by that expression, and the equality to
`328` is checked by reduction.

Active whole-query evaluation calls the all-size structural canonical LCA
route and then rank/output. Its only data-dependent close split is same-block
versus cross-block; this is algorithmic control inside one canonical route, not
a Ready/Active/public-size dispatch. The same-block route uses rank-seeded local
BP reads; the cross-block route uses the canonical interior store.

The following remain visible only for compatibility/history:

- `118`: old fast-regime theorem;
- `4144`: explicitly named compatibility clean-all-size cost;
- `196727`: explicitly named legacy bound;
- zero-block/Ready/Active/inactive branches: legacy definitions/theorems; and
- `2^128`: large-regime compatibility and the proof-only sparse reachability
  witness, never an activation premise of the canonical List/paper route.

## Claim-policy audit

`docs/internal/CLAIM_DRIFT_POLICY.json` v10 treats a canonical `2^128`
activation claim as forbidden. Its allowances are narrow and conjunctive:
exact policy paths; the exact matrix path with exact policy-row context; or
structured negation/history/compatibility/proof-only language. Merely inserting
a role word, changing exponent spacing/order, using a Windows absolute path, or
naming a file like the matrix does not bypass the detector.

`scripts/claim_drift_policy_regression.ps1` creates isolated temporary/shadow
roots, snapshots raw worktree/index state and the real matrix SHA-256, asserts
that state is unchanged around mutation cases, and cleans its temporary root.
The live run passed 26 must-reject, 15 must-accept, and 5
path/context/bypass verdicts. The target worktree was clean immediately after
the regression. The production strict scan completed with 581 hits and zero
strict failures.

This policy evidence is regression/process evidence, not a substitute for the
source and theorem chains above.

## Positive evidence tiers

### Tier 1 — exact definitions and kernel-checked public consumption

- Exact payload erasure, no padding, and `2*n + o(n)` bound.
- Actual supplied-store physical evaluation and full positional refinement.
- Indexed operational source provenance and current-query occurrence coverage.
- Capacity-derived logarithmic word width.
- Direct canonical `328` theorem.
- One adequacy/List/paper/headline consumer chain.

This tier is sufficient for the acceptance decision.

### Tier 2 — adversarial theorem evidence

- Dead/tautological/enumeration mutations are not load-bearing.
- Fresh canonical segment 21 has no operational producer.
- Repeated equal events retain distinct occurrence receipts.
- Consumed-address disagreement changes full execution.
- Legacy close sources/tail are excluded or `none`.
- Symbolic proof witnesses are excluded from native executable imports.

### Tier 3 — independent executable evidence

- The validator checked 498 valid/invalid windows across 43 deterministic
  inputs, including same/cross routes, exact 328 bound, physical erasure and
  backing, and supplied-store dependency.
- The cost harness reported only `sameBlock`, `crossBlock`, and `invalid`; its
  observed modeled costs 36, 44, and 60 were all at most 328, while invalid
  ranges cost zero and agreed with the public `List Int` reference.

This is concrete corroboration, not the proof of the universal theorem.

### Tier 4 — process and claim hygiene

- All requested builds, inventories, policy checks, aggregate gate, whitespace
  check, and hygiene scans passed.
- Axiom inventories reported only the project's expected `propext`,
  `Classical.choice`, and `Quot.sound`; no `sorryAx` or forbidden trust marker
  appeared.

## Stale objections

| Objection | Audit disposition |
|---|---|
| The physical trace is post-hoc relabeling. | Stale. The physical adapter is installed before the supplied-store evaluator computes the result. |
| The public space theorem counts a different payload or a padded equality. | Stale. Literal flattening of the only physical word list equals `buildPayload`; the bound and execution name that object. |
| Manifest liveness is only enumeration or a hand-written consumer label. | Stale. P requires a successful closed valid indexed occurrence and an evaluator invocation edge. |
| Component may-read or event-value membership is being sold as liveness. | Stale. Those compatibility facts are separate; P/Q and current-query occurrence provenance are load-bearing. |
| Equal events collapse provenance. | Stale. Occurrence receipts carry global/instruction/local positions. |
| The reviewer path still dispatches on readiness, zero block, or the historical large-size threshold. | Stale. Such surfaces are legacy/proof-only; the active route is all-size structural. |
| `328` merely aliases `4144` or `196727`. | Stale. The public definition and direct evaluator theorem changed; old numbers are explicitly compatibility/legacy. |
| A proof-only answer or uncounted live store survives. | Stale. The answer comes from the supplied physical-store evaluation, successful reads are charged/backed, and physical erasure equals the one public payload. |
| Proof-only giant sparse witnesses enter native binaries. | Stale. The import seam keeps them on the theorem/provenance side. |
| Source comments accurately describe synthetic fallback. | **Not stale; P3 confirmed.** The comments are wrong, while definitions and theorems are correct. |

## Roadmap alignment: letter and spirit

In letter, U2 closes the frozen requirements: one public payload, one exhaustive
manifest, positional physical reads, one query-independent word model grounded
in input capacity, one consumer chain, uniform public cost 328, and no active
old dispatch/synthetic/proof-only storage defect.

In spirit, this is not an acceptance-shaped wrapper. The machine packs the
reviewer data once, translates logical reads to positions in that physical
store, computes the answer from the supplied store, records every attempted
read in order, derives ownership from actual successful closed queries, and
projects that same machine to the ordinary List API and paper theorem. The
result advances the repository's `2n + o(n)` upper-bound story under an explicit
RAM/indexed-access model without conflating payload bits, proof-only witnesses,
modeled ticks, or Lean runtime.

The natural next skeptical question is a later optimization question: whether
the conservative transitional constant 328 can be tightened or decomposed more
elegantly without weakening the single-store provenance chain. That is not a
reason to withhold U2 acceptance.

## Command evidence

| Command | Result |
|---|---|
| `git status --short --branch` | Clean audit branch at target before the report edit; clean again after policy regression and all source/build gates. |
| `git diff --stat BASE..TARGET` | 71 files changed, 24,172 insertions, 1,604 deletions. |
| `git diff --check BASE..TARGET` | Pass. |
| `git diff --check` | Pass before the report edit; rerun as the report-only integrity gate. |
| `lake build RMQPaper` | Pass; 137-target paper closure built. |
| `lake build` | Pass; full `RMQ` default build completed. |
| `lake build RMQExamples` | Pass. |
| `lake env lean scripts/headline_axiom_check.lean` | Pass; expected standard Lean axioms only. |
| `lake env lean scripts/wordram_axiom_check.lean` | Pass; expected standard Lean axioms only. |
| `lake env lean scripts/axiom_check.lean` | Initial fresh-worktree attempt lacked `RMQ.Core.GenericSelectBPCompat.olean`; after the explicit `lake build RMQ.Core.GenericSelectBPCompat` warm-up, pass with expected standard Lean axioms only. |
| `lake exe rmq_succinct_classic_validate` | Pass: 498 windows over 43 deterministic inputs. |
| `lake exe rmq_succinct_classic_cost_harness` | Pass: all reference answers/routes agree; canonical bound is 328. |
| `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_policy_regression.ps1` | Pass: 26 reject, 15 accept, 5 path/context/bypass; tracked state unchanged. |
| `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | The audited source tree passed with 581 hits and 0 strict failures before the report was written. Initial report commit `f5c2ab0` then failed CI because one stale-objection quotation restated a forbidden current claim. Coordinator integration paraphrased that quotation and reran the strict scan on the final report tree successfully. |
| `powershell -ExecutionPolicy Bypass -File scripts/gate.ps1` | The audited target passed after network permission. Initial report commit `f5c2ab0` later failed inside its strict claim scan because the report had not been included in the pre-report run. Coordinator integration reran the full gate on the corrected final tree successfully. |
| Required trust hygiene `rg` scan | No matches. |
| `rg -n "native_decide|Lean\.ofReduceBool" RMQ` | No matches. |

## Proof digestion

Conceptually, U2 turns the succinct RMQ story into one reviewer-auditable
machine rather than a conjunction of neighboring certificates. The physical
words erase to the public payload; the evaluator reads those words through
checked offsets; provenance is tied to indexed successful executions; the
answer depends on the supplied store; and a single width/cost story reaches the
paper theorem.

Live assumptions are the repository's explicit model boundary: Lean/Std plus
the expected logical axioms reported by the inventories; the abstract
WordRAM/event-cost model rather than compiled Lean runtime; and the public
half-open, leftmost `List Int` RMQ contract. The physical word count and payload
bit count remain distinct but connected by exact erasure.

A skeptical graduate student should next ask whether every conservative factor
in the 328 accounting is necessary, and whether the capacity constant can be
tightened, while insisting that any optimization preserve exact ordered
footprints, failed reads, supplied-store dependency, and the one-payload public
chain.

## Coordinator disposition

Disposition date: 2026-07-14.

- The report and its `merge-ready with follow-up` verdict are accepted.
- REQ-01 through REQ-08 are accepted for exact audited target
  `4f7ec8be47ecd65b2859a3784fadeab48a629e4e`; U2 is recorded as `ACCEPTED`.
- Initial report commit `f5c2ab03a064e56f90a17574041cd116568416d8`
  failed CI because its stale-objection table quoted a forbidden current claim
  after the auditor's last strict scan. The coordinator repaired the report and
  reran report-sensitive checks on the final tree. This process miss does not
  alter the independently checked Lean verdict.
- The P3 finding is closed by the immediately following integration change,
  which corrects the three stale comments without changing executable or
  theorem content.
- U3, not another U2 repair, is the next proof campaign.
