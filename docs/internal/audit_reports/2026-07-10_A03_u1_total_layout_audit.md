# A03 — U1 Total Relative-RmM Layout Interface Audit

- Auditor handle: `A03-u1-total-layout`
- Chat/thread title: `(A03-u1-total-layout) Audit total relative-rmM layout`
- Mode: Fresh Blind Delta (report-only)
- Date: 2026-07-10
- Report path: `docs/internal/audit_reports/2026-07-10_A03_u1_total_layout_audit.md`

## 1. Scope

- **Base:** `f7a844e78fcdb52cfc0b07cc5ffd941cdcb6540c` ("Harden RMQ scout and
  model-routing decisions").
- **Target:** `b5d0512043730deec05daaa1369fafcedf5844a7`, head of
  `origin/codex/add-audit-decision-log` (verified by fetch + checkout).
- **Delta:** exactly two commits. `03043fe` "Implement total relative-rmM
  layout" touches `RMQ/Core/SuccinctClose/RelativeSummary.lean` (+373) and
  `RMQ/Core/SuccinctClose/RelativeRmmMacro/LocalBPDecoder.lean` (−19);
  `b5d0512` "Record total-layout implementation outcome" touches only
  `docs/internal/DESIGN_DECISIONS.md`, `RELATIVE_RMM_LAYOUT_DESIGN.md`, and
  `RMQ_FINAL_ROADMAP.md`. `git diff --stat f7a844e..b5d0512`: 5 files,
  +399/−27. `git diff --check`: clean.
- **Roadmap node:** U1 (implement total layout parameters) per
  `RMQ_FINAL_ROADMAP.md`, `RELATIVE_RMM_LAYOUT_DESIGN.md`, DD-20260709-007,
  DD-20260709-008, DD-20260710-001.
- **Acceptance criteria:** the twelve U1 criteria in the audit packet
  (unconditional geometry, no readiness-gated projections, canonical validity
  on all shapes, exact Active/Ready equivalences, fieldwise agreement,
  truthful empty counts, threshold classifier from the real 2^15 theorem,
  upstream-unique upper-cover relocation, no behavior/claim change, genuine
  U2 preparation, publication-grade decision record).
- **Independence:** no prior verdicts, worker chats, or transcripts for this
  delta were read. Disclosure: the header of the A02 report (an audit of the
  earlier `37abaf8` frontier, not of this delta) was opened solely to copy
  report formatting conventions; it contains no U1 finding or verdict.

## 2. Verdict

**MERGE-READY WITH FOLLOW-UP.**

The delta is a pure-addition interface milestone that does exactly what the
frozen U1 design says and nothing else. The four-field computational
`RelativeRmm.Layout` is unconditional geometry; validity, summary-fit, and
compact readiness are separate predicates never consulted by any projection;
both legacy equivalences and all eleven shape-dependent agreement lemmas are
kernel-checked; the upper-cover theorem moved upstream verbatim with no
duplicate and no import cycle; every required gate passes; no query route,
payload, trace, cost constant, headline alias, or public claim changed. The
follow-ups are small interface-polish items (a named `macroSize` positivity
accessor and fieldwise agreement corollaries), none blocking.

## 3. Findings (P0 → P3)

### P0 — none

Hygiene scan (`sorry|admit|axiom|unsafe|opaque|implemented_by|partial|extern|
noncomputable|import Mathlib` over `RMQ` and `lakefile.toml`) and
native-decision scan (`native_decide|Lean.ofReduceBool`) both return no
matches. All four principal U1 theorems check with axioms
`[propext, Quot.sound]`; the threshold classifier additionally uses
`Classical.choice` (from `by_cases`), identical to the standard headline
trust base. (Tier 1.)

### P1 — none

No overclaim, no failed gate, no misleading theorem surface, no
letter-satisfies-spirit-violates work. The adversarial checks that could have
produced a P1 and their outcomes are in §4 and §6.

### P2

1. **Missing named positivity access for `Layout.macroSize`.**
   `Layout.macroSize` ([RelativeSummary.lean:1292](../../RMQ/Core/SuccinctClose/RelativeSummary.lean))
   is a routing divisor (denominator of `macroSampleCount`, line 1295), and
   the design doc's own acceptance line says "Every routing divisor and width
   has a positivity theorem." `Valid.blocksPerSuper_pos` exists and
   `0 < layout.macroSize` follows in one line
   (`Nat.mul_pos h.blocksPerSuper_pos h.blocksPerSuper_pos` — probe-verified,
   Tier 1), but there is no named `Valid.macroSize_pos`/`Layout.macroSize_pos`
   lemma, while the legacy side has the named
   `concreteBPRelativeRmmInteriorMacroSize_pos` (line 2909). Every other
   divisor/width has named access: `Valid.blockSize_pos`,
   `Valid.blocksPerSuper_pos`, `Valid.relativeWidth_pos`, sample counts are
   `… + 1` (succ-positive), and all five width projections are
   `SuccinctRank.machineWordBits` applications covered by the existing
   `SuccinctRank.machineWordBits_pos` (`RMQ/Core/SuccinctRank.lean:41`).
   Recommendation: add the one-line named lemma when U2 first consumes
   `macroSampleCount`, or in a trivial follow-up. Non-blocking.

### P3

2. **Aggregate conjunction agreement theorems.**
   `legacy_parameters_eq_canonical_of_legacyActive` (five-way `∧`, line 2641)
   and `legacy_ready_parameters_eq_canonical` (six-way `∧`, line 2804) force
   consumers into positional `.2.2.1`-style projections. This matches the
   design doc's own sketch (a single fieldwise-equality theorem), so it is
   compliant, but U2 ergonomics and reviewer legibility would benefit from
   named per-field corollaries (or a `structure` of equalities). Friction,
   not defect.

3. **`Layout.superWidth` ignores its receiver.**
   `superWidth (_layout : Layout) (shape) := machineWordBits
   shape.bpCode.length` (line 1288) is frozen verbatim by
   `RELATIVE_RMM_LAYOUT_DESIGN.md`, so this is an accepted design, not a
   worker deviation. The cost: `layout.superWidth shape` returns the same
   value for any layout, including arbitrary non-canonical ones, so the dot
   notation suggests a dependence that does not exist. The benefit claimed by
   the design (uniform dot-notation surface, room for a future
   layout-dependent width) is real but thin. Worth revisiting at A1 module
   extraction; harmless now.

4. **`Decidable ((canonicalLayout shape).CompactReady shape)` does not
   synthesize** (probe: `failed to synthesize`, Tier 1), because `Valid` and
   `SummaryFits` are `Prop` structures without instances. Assessment: this is
   acceptable and arguably protective. U2's mandated single uniform route
   must not dispatch on readiness, so routine decidability would mostly
   invite the forbidden split. Where construction-time selection legitimately
   needs it, one line recovers it through the checked equivalence —
   `decidable_of_iff _ (canonicalLayout_compactReady_iff_legacyReady
   shape).symm` (probe-verified against the existing
   `concreteBPRelativeRmmInteriorReady_decidable`, Tier 1). Not a U1 blocker;
   do not add a direct instance without a consuming theorem that needs it.

5. **Strict design-decision check advisory.**
   `design_decision_check.ps1 -Base f7a844e -Strict` exits 1:
   `RMQ_FINAL_ROADMAP.md` changed without a
   `WORKFLOW_DESIGN_DECISIONS.md` update. The roadmap edit is a pure status
   flip (U1 next→complete, U2 blocked→next) with no process decision, so no
   workflow entry is warranted; the non-strict invocation passes with an
   advisory. Coordinator should note the exception rather than add a filler
   entry.

6. **Documentation polish.** In `RELATIVE_RMM_LAYOUT_DESIGN.md` the new
   "## Implementation Outcome" section is missing a blank line after the
   preceding paragraph and is inserted between the intro and "## Problem"
   while later sections retain prospective phrasing ("U1 should prove…"),
   which now reads as unresolved intent against the "implemented" status
   line. Cosmetic; a one-paragraph tense pass at U2 kickoff suffices.

## 4. Acceptance criteria, one by one

1. **Layout contains only unconditional computational geometry — PASS
   (Tier 1).** `Layout` is four `Nat` fields (line 1270); `canonicalLayout`
   (line 1276) uses only the `…Raw` formulas; the eight derived projections
   (lines 1285–1308) contain no `if` and no predicate reference.
2. **No projection branches on Active/Ready/SummaryFits/CompactReady — PASS
   (Tier 1).** Verified by reading every projection and by rg census: the
   only mentions of the three predicates in the new namespace are the
   predicate definitions, their accessors, and the equivalence theorems.
3. **Canonical Valid genuinely true for every shape, including empty — PASS
   (Tier 1).** `canonicalLayout_valid` (line 2587) is universally quantified
   with no side condition; probe instantiated it at
   `CartesianShape.empty` and separately kernel-checked
   `(canonicalLayout empty).blockCount = 0` with
   `(canonicalLayout empty).blockSize = 2` and `blocksPerSuper = 1`. `Valid`
   nowhere assumes positive `blockCount`: validity and a zero count coexist
   at the empty shape, exactly as DD-20260709-007 requires.
4. **SummaryFits ⇔ legacy Active, no dropped premise — PASS (Tier 1).**
   Compared field-by-field against
   `canonicalBPRelativeMinMaxArgSummaryTableActive` (lines 1437–1455): Active
   is six conjuncts; `SummaryFits` carries exactly the three storage conjuncts
   (super payload, block payload, one-word width) with identical right-hand
   sides (`sampledDirectoryOverhead` with `SuperSlots`,
   `logLogSampledDirectoryOverhead` with `BlockSlots`, machine width); the
   three omitted geometric conjuncts are unconditional theorems packaged in
   `Valid` and are re-supplied from `canonicalLayout_valid` in the `mp`
   direction of `canonicalLayout_summaryFits_iff_legacyActive` (line 2608).
   Both directions are explicit constructions; kernel-checked; axioms
   `[propext, Quot.sound]`.
5. **CompactReady ⇔ legacy Ready — PASS (Tier 1).**
   `canonicalLayout_compactReady_iff_legacyReady` (line 2776). Legacy Ready
   (line 2756) is Active ∧ `interiorMacroSize ≤ gated blockCount`;
   `interiorMacroSize = base²  = (canonicalLayout).macroSize` and the gated
   `blockCount` rewrites to raw under the Active certificate; both directions
   constructed explicitly.
6. **Fieldwise agreement under stated certificates — PASS (Tier 1).**
   Summary side: block size, blocks-per-super, block count, super sample
   count, relative width (`legacy_parameters_eq_canonical_of_legacyActive`,
   line 2641; `…_of_summaryFits`, line 2660). Interior side: macro size,
   macro sample count, offset width, level count, global level count, block
   address width (`legacy_ready_parameters_eq_canonical`, line 2804;
   `…_of_compactReady`, line 2829). A consumer census of the gated wrappers
   across `RelativeRmmMacro/`, `InteriorCandidate/`, and `SuccinctFinal`
   found no shape-dependent geometric or derived scalar consumed by the Ready
   route outside these eleven plus the ungated
   `canonicalBPRelativeSummarySuperWidth`, which agrees definitionally via
   the `@[simp]` lemma `canonicalLayout_superWidth` (line 1388). Slot and
   cost constants are shape-independent and untouched.
7. **Empty and small counts truthful — PASS (Tier 1).**
   `blockCount = 0` at empty is data, not a gate (kernel probe); sentinel
   slot counts are named `superSampleCount`/`macroSampleCount` per the
   design's SampleCount naming rule, and no new declaration calls a sentinel
   slot count a semantic count.
8. **Threshold classifier follows from the real 2^15 theorem — PASS
   (Tier 1).** `canonical_compactReady_or_below_threshold` (line 3292) is
   proved by `by_cases` plus the pre-existing
   `concreteBPRelativeRmmInteriorReady_of_size_ge_readyThreshold`
   (line 3279) through the CompactReady equivalence. No new threshold, no
   new axiom, no dense-answer authorization.
9. **Upper-cover theorem uniquely upstream, no cycle — PASS (Tier 1/4).**
   `canonicalBPRelativeSummaryBlockCountRaw_upper_cover` now lives at
   line 1570 of `RelativeSummary.lean`, deleted from `LocalBPDecoder.lean`
   with byte-identical statement and proof (diff inspection); single
   definition repo-wide (rg); `RelativeSummary.lean` imports only
   `RangeSummary` (no downstream import); the downstream consumer
   (`LocalBPDecoder.lean:2577`) and the `SuccinctCloseProposal` export list
   resolve the unchanged name; full build passes.
10. **No route/payload/trace/cost/headline/claim change — PASS (Tier 1/4).**
    The Lean delta is pure addition plus the verbatim relocation; no existing
    definition or theorem was modified; `lcaCloseCosted` dispatch, cost
    constants (e.g. `ReadyQueryCost = 30`, `SmallScanQueryCost`), headline
    aliases, `README`, `FAMILY_SUMMARY` untouched (diff file list); full
    build, `RMQPaper`, and the 64-surface headline axiom check all pass with
    the standard axiom set.
11. **Meaningfully prepares U2 — PASS (Tier 1/5).** This is not gate
    renaming: geometry became a first-class data record with unconditional
    validity, the storage predicates are proofs about the record rather than
    value-erasing wrappers, and the agreement surface is complete enough for
    U2 to rewrite every Ready-route parameter through `canonicalLayout`
    without re-deriving arithmetic. The gated wrappers do remain
    authoritative in the live route — that is mandated (U1 must not touch
    dispatch) and is precisely the U2 work item, not a U1 defect.
12. **Decision record supports publication exposition — PASS (Tier 5).**
    DD-20260710-001 names the scout's shape-indexed proof-carrying record and
    the `max 1` scattering as rejected alternatives with reasons, states the
    data/proof separation rationale, scopes what it supersedes in
    DD-20260709-007, and records the relocation rationale. Adequate for
    future paper exposition.

## 5. Adversarial probes and outcomes

- **Wrappers leaving gated geometry authoritative:** present in the live
  route by design mandate; the new surface is sufficient to displace them in
  U2 (see criterion 6 census). Rejected as a finding.
- **Valid silently assuming nonempty blockCount:** rejected by kernel probe
  (`Valid` holds at empty with `blockCount = 0`).
- **Conjunction nesting / one-directional equivalences:** both `Iff`
  directions are explicit `And.intro` constructions against the six-conjunct
  Active and the three-conjunct Ready shapes; kernel accepts the stated
  `Iff`, which fixes the nesting by type. No `sorry`-shaped gaps, no
  `Decidable`-based shortcuts.
- **Decidable CompactReady:** does not synthesize (probe); recoverable in one
  line via the equivalence (probe); classified acceptable-by-design (§3.4).
- **macroSize / width positivity access:** widths covered by
  `machineWordBits_pos`; `macroSize` named accessor missing though one-line
  derivable — the single P2 (§3.1).
- **superWidth receiver and aggregate agreement conjunctions:** reviewer
  friction, not defects; both match the frozen design (§3.2, §3.3).
- **Theorem-name satisfaction with preserved abstraction defect:** checked by
  comparing each new statement to the design's semantic intent, not its name;
  the layout record genuinely removes readiness from geometry. No instance
  found.
- **Different-roadmap-goal work smuggled in:** none; the delta contains no
  dispatch, payload, cost, or headline change at all.

## 6. Commands run and outcomes

| Command | Outcome |
| --- | --- |
| `git status --short --branch` | clean at target |
| `git log --oneline --decorate -20` | delta = `03043fe`, `b5d0512` on `origin/codex/add-audit-decision-log` |
| `git diff --stat f7a844e..b5d0512` | 5 files, +399/−27 |
| `git diff --check f7a844e..b5d0512` | clean |
| `lake build RMQ.Core.SuccinctClose.RelativeSummary` | exit 0 |
| `lake build RMQPaper` | exit 0 |
| `lake build` | exit 0 (194 jobs) |
| `lake env lean scripts/headline_axiom_check.lean` | exit 0; all 64 surfaces `{propext, Classical.choice, Quot.sound}` |
| AGENTS.md hygiene scan | no matches |
| `native_decide` / `ofReduceBool` scan | no matches |
| `design_decision_check.ps1` (bare) | "no changed files" (clean tree; script diffs worktree by default) |
| `design_decision_check.ps1 -Base f7a844e` | pass with workflow advisory (§3.5) |
| `design_decision_check.ps1 -Base f7a844e -Strict` | exit 1 on the same advisory (§3.5) |
| rg declaration census (all new names + relocated theorem) | each declared exactly once; no collisions; no stale duplicate |
| Lean probe: `#print axioms` of principal U1 theorems | `[propext, Quot.sound]`; classifier adds `Classical.choice` |
| Lean probe: `Decidable CompactReady` synthesis | fails (expected); recoverable via `decidable_of_iff` (passes) |
| Lean probe: empty `blockCount = 0`, `blockSize = 2 > 0`, `blocksPerSuper = 1`, `Valid` at empty | all kernel-accepted |
| Lean probe: `0 < macroSize` from `Valid` alone | kernel-accepted one-liner |

Skipped: none of the required checks were skipped. `scripts/axiom_check.lean`
(the full acceptance gate) was not run; the required headline subset was.

## 7. Stale or rejected objections

- "The relocation could flip import direction or leave a duplicate" — stale:
  verbatim single upstream copy, imports unchanged.
- "SummaryFits is weaker than Active" — rejected: the omitted conjuncts are
  unconditional theorems; the equivalence is kernel-checked in both
  directions.
- "Zero counts mean the interface is still gated" — rejected: zero
  `blockCount` on the empty shape is truthful arithmetic
  (`0 / base = 0`), coexisting with a valid, positive-divisor layout.
- "Missing Decidable instance blocks U2" — rejected (§3.4).

## 8. Roadmap alignment

**Letter:** every U1 acceptance bullet in `RMQ_FINAL_ROADMAP.md` and
`RELATIVE_RMM_LAYOUT_DESIGN.md` is satisfied except the strictest reading of
"every routing divisor … has a positivity theorem" for `macroSize` (§3.1,
one-line follow-up). **Spirit:** the delta removes readiness from geometry as
DD-20260709-007 demands, resists the temptation to touch dispatch or
constants, and leaves the zero-block replay's removal to U2 exactly as
DD-20260709-008 sequences it. The doc-only second commit correctly records
the outcome and re-gates U2 on this audit.

## 9. Best next theorem-shaped U2 target

Totalize the interior directory over the new layout and prove agreement plus
unconditional exactness. Concretely, pre-register:

```
def canonicalRelativeRmmInteriorDirectory (shape) : … -- built from canonicalLayout shape, total
theorem canonicalRelativeRmmInteriorDirectory_eq_legacy_of_compactReady :
    (canonicalLayout shape).CompactReady shape →
      canonicalRelativeRmmInteriorDirectory shape = concreteBPRelativeRmmInteriorDirectory shape
theorem canonicalRelativeRmmInteriorDirectory_exact_of_query : … -- no readiness hypothesis
```

starting from `concreteBPRelativeRmmInteriorDirectory`
(`EndpointFringe/InteriorCandidate/InteriorDirectory.lean:936`) with the
eleven agreement lemmas discharging the Ready-regime proofs. The join theorem
is the unconditional `exact_of_query`; the classifier
`canonical_compactReady_or_below_threshold` bounds the only regime where the
degenerate hierarchy must be shown to cover queries directly. Only after that
lands should the all-size cost constant be rederived (per DD-20260709-008).

## 10. Coordinator disposition

(Left for the coordinator: accepted/rejected findings and next action.)
