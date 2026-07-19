# A08-R1 continuation audit of the B7 charged sparse level

Date: 2026-07-19

Auditor: A08

Mode: CONTINUATION

Original audited base: `f6564ec`

Audited B7 target: `6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25`

Rejected report amended here: `1bc6b3597b97720c5c5dad0a2e87277cf28fd7ea`

Governance protocol inspected: `bd854edaa65944d5a7fa0fac5667e9572c370bbb:docs/internal/AUDIT_PROTOCOL.md`

Audited branch: `claude/b7-charged-sparse-level`

Report branch: `codex/a08-b7-sparse-level-audit`

Permission: REPORT-ONLY. This report is the only edited file.

## Correction scope

This continuation corrects A08's first report; it does not re-audit the B7
implementation from scratch. The exact target remains `6ad4198...`. Accurate
positive source evidence from the first pass is retained, while the frozen
matrix reconstruction, literal gate record, evidence-tier labels, public-surface
inventory, route-inventory conclusion, and protocol verdicts are replaced.

The first report's P1 based on blank cells and `Open` statuses is withdrawn.
The matrix schema permits evidence in its row-keyed append-only ledger, and
coordinator-owned `Open` status is not evidence absence. The first report also
cited nonexistent matrix identifiers. Those identifiers are removed. The
actual 25 frozen IDs are enumerated below.

## Protocol evidence tiers

This report uses the five tiers from `AUDIT_PROTOCOL.md` exactly:

1. **Kernel theorem** — a Lean theorem checked by the kernel.
2. **Explicit-model theorem** — a checked theorem about the explicit
   store/trace/execution model.
3. **Executable validation** — a harness or executable result.
4. **Artifact/CI evidence** — a reproducible build, lint, axiom inventory, or
   other artifact gate.
5. **Process evidence** — Git history, comments, matrices, worklogs, design
   logs, and audit reports.

Git history, comments, matrix prose, and worklogs are never classified as
kernel evidence here. Tier 5 can establish a process record; it cannot prove
mathematics, liveness, model adequacy, or executable behavior.

## Protocol verdicts

- **A08 report quality after this correction: merge-ready.** This is a verdict
  on the report-only artifact, contingent on the final report-tree gates below;
  it is not coordinator acceptance of B7.
- **B7 local-rung verdict at exact `6ad4198...`: blocked.** Two literal frozen
  gates fail, a frozen historical contract changes under the same name, and
  load-bearing tightness/value-dependency obligations are not established.
- **Broader charged-query roadmap node: needs another worker pass.** B7 makes
  real progress toward an explicit charged upper-bound story, but neither the
  complete accepted-route inventory nor the frozen acceptance surface closes.

No P0 finding was found.

## Findings

### P1 — CHK-02 literally fails on a removed theorem name

The frozen row `CHK-02` requires exactly:

```text
lake env lean scripts/wordram_axiom_check.lean
```

with exit 0. At the audited target,
`scripts/wordram_axiom_check.lean:197` contains:

```lean
#print axioms RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_76
```

The live theorem is
`...nonSyntheticWeight_sum_le_210` at
`RMQ/Core/SuccinctFinalRAM.lean:9510`; the `_76` declaration is absent. The exact
gate was rerun in this continuation and exited 1 after 255 seconds. The fact
that this stale reference was known-red or owned by another branch does not
satisfy `CHK-02`, and no frozen amendment waived it.

Evidence tier: 4 for the literal gate result; 1 for the live `_210` declaration.

### P1 — REQ-B7-10 and CHK-06 literally fail on the tracked WIP patch

The frozen rows require both working-tree `git diff --check` and
`git diff --check f6564ec..HEAD` to exit 0. Reconstructed against the exact B7
target:

```text
git diff --check f6564ec..6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25
```

exits 2. Every diagnostic is a single-space blank context line in the tracked
`docs/internal/B7_STEP2_WIP.patch`, beginning at lines 13, 14, 19, and 92.
That may explain why the artifact was committed, and it is not a Lean source
defect, but the frozen requirement is an exact command/exit condition. The
first report incorrectly reinterpreted the exception as a pass. It is a literal
gate failure.

Evidence tier: 4.

### P1 — Upper-bound closure does not establish cost tightness

The sound upper-bound surface is:

- local two-span `cost <= 11` at
  `InteriorDirectory.lean:5259-5260`;
- global two-span `cost <= 11` at `:5314-5315`;
- cross-macro `cost <= 33` at `:5418-5419`; and
- whole interior `cost <= 33` at `:5461-5467`.

The cross-macro dispatcher closes with direct `exact` at
`InteriorDirectory.lean:5516-5517`. That shows an available `cost <= 33` fact
matches the goal without a transitivity step. It does not prove an equality,
lower bound, reachable witness of cost 33, or negation of `cost <= 30`.

The old slack conjunction had the shape
`cost <= 30 /\ 30 < cap /\ cap = 33`. The claim that `30 < 33` became
unprovable is arithmetically false; `30 < cap` is the conjunct that remains
immediate once `cap = 33`. The conjunct that would have to fail is the first,
`cost <= 30`, and the target supplies no checked lower bound or counterexample
over the same reachable object/domain.

Deletion of
`canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_...`
is confirmed. The finding concerns the stronger attainment/impossibility
claim, not the validity of the 210 upper-bound algebra.

Evidence tiers: 1 for the upper-bound theorems; 5 only for comments and matrix
claims of attainment.

### P1 — The same-name historical 328 contract changes to 352 without a frozen amendment

At the base, `f6564ec:RMQ/Core/SuccinctRMQClassic.lean:135-138` states:

```lean
theorem canonicalTransitionalQueryCost_eq :
    canonicalTransitionalQueryCost = 328 := by
  rfl
```

At the target, the same public theorem name at
`RMQ/Core/SuccinctRMQClassic.lean:147-150` states `= 352`. The frozen
`REQ-B7-05` text at
`docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md:108` explicitly uses the
`142/76/328` pattern and says frozen legacy anchors are untouched.

This change was not wholly silent:
`docs/PAPER_MODEL_ADEQUACY.md:129-135` discloses that 328 was implemented as a
live symbolic abbreviation and therefore moved. That worker-authored
explanation is useful process evidence, but it does not amend the frozen
historical-contract requirement. The public surface needed either a pinned 328
compatibility identity plus a distinctly named live 352 identity, or an
approved frozen amendment. It has neither.

Evidence tier: 1 for the theorem statements; 5 for history and explanatory
prose.

### P1 — Current public and policy surfaces contradict the target's 210/33 story

The current theorem surface uses 210 and interior cap 33, but several documents
still present older values as current:

- `README.md:70-82`, `:140`, and `:334` present 207, interior 30, or the old
  `13/4/4/30` algebra as current.
- `docs/FAMILY_SUMMARY.md:9`, `:32-48`, `:133`, `:446`, and `:1041` present the
  207/30 route and continue to describe the sparse logarithm as uncharged.
- `docs/PAPER_MODEL_ADEQUACY.md:229-256` names the deleted
  `...announced_slack...` theorem and old `...thirty_literal...` bridge as live,
  checkable support, and asserts unsupported tightness.
- `docs/internal/CLAIM_DRIFT_POLICY.md:127-133` says 76 is the **current**
  principled canonical charged-trace bound. Its statement that 328 is
  historical is not enough to repair the same-name numeric drift above.
- `docs/PAPER_THEOREM_MAP.md:60`, `:141-164` says the current final route is 76
  and uses the old `13/4/4/30` algebra.
- `docs/TRUST_AUDIT_PACKET.md:24`, `:84-96` likewise presents 76 and
  `13/4/4/30` as the current paper/trust boundary.

This is not repository-wide uniform drift: `docs/WHAT_IS_PROVED.md:34,72-84`
and `docs/PAPER_CLAIM_CORRESPONDENCE.md:7-9,54-56` correctly present 210 and the
`35/11/37/33` algebra. The coexistence of incompatible current surfaces is the
finding.

Evidence tier: 5. These are documentary/public-claim failures, not kernel
failures.

### P1 — INV-VALUE-DEPENDENCY lacks its required decisive corruption witness

The implementation has strong positive value flow: the packed level cell is
decoded and feeds the addresses of the subsequent sparse-span reads, and the
full-value refinement theorems preserve the returned
`Option (Nat × Nat)`. However, the frozen invariant specifically requires a
corruption at an actually read level slot that changes the returned interior
candidate, not merely the trace, cost, or decoded local variable.

The checked surfaces found at `InteriorDirectory.lean:2025-2077` establish
full-value equivalence on the canonical store, while `:3440-3480` establishes
Computation/Costed refinement and `:3621-3668` establishes agreement
parametricity. Those are one-direction preservation results. No level-table
corruption theorem or concrete decisive-corruption witness changing the
returned candidate was found. Therefore the structural dependence is
plausible and directly visible, but the row's specified anti-vacuity witness is
not established.

Evidence tiers: 1 and 2 for the positive refinements; no qualifying tier 1/2/3
evidence for the required negative/corruption witness.

### P2 — STRETCH-01 is open, so the universal route-inventory claim must be qualified

The first report correctly resolved the two named candidate families:

1. runtime-derived `Nat.log2`/`bpSparseLogSpan` is gone from the inspected
   accepted sparse-level caller chain; surviving occurrences are construction,
   specification, or compatibility surfaces; and
2. the old recursive same-block decoder is compatibility/spec code, while the
   accepted branch uses the charged, fixed 33-chunk fold in
   `ChargedSameBlockChunks.lean:49-75`.

That does not satisfy `STRETCH-01`. The target contains no auditable complete
reachability derivation from the whole-query root, no mechanized enumeration,
and no exhaustive entry-by-entry bridge/charge classification. Therefore the
correct conclusion is: **no named input-growing uncharged candidate remains in
the sparse-level and same-block families A08 inspected.** This report does not
certify that the accepted route contains no such work anywhere.

Evidence tiers: 1 and 2 for the two inspected families; missing evidence for
the universal quantifier.

### P2 — REQ-B7-09's atomicity is confirmed, but per-commit green is only process evidence

History reconstruction confirms the substantive no-dead-region design:
generic table storage and its generic reader land together; instantiated level
tables remain outside the public counted component store until `c45e62c`; and
that atomic commit adds both counted store regions and the accepted readers.
No intermediate integrated counted region without a reader was found.

The separate “library-green-per-commit” clause is evidenced only by the
worker-authored per-commit ledger. This continuation deliberately did not
rebuild every historical commit, and a final-target build cannot prove every
intermediate commit was green. The row is therefore not fully established by
independent artifact evidence even though its atomic-storage claim is
confirmed.

Evidence tier: 5 for history/ledger; 2 for the target's integrated store/read
object identity.

### P3 — Smaller vocabulary drift remains

- `InteriorDirectory.lean:5529-5539` retains a theorem name containing
  `cost_le_thirty`, while its statement uses the live cap 33.
- `RMQ/Headlines/RMQ.lean:502-508` says “readWord of the counted store layout,”
  while the named theorem itself proves `event.isReadWord`; backing is supplied
  by separate explicit-model adequacy/provenance theorems.

Evidence tiers: 1 and 2.

## Reconstruction of all 25 frozen rows

`SATISFIED` means the proposition requested by that row is supported at the
target. `FAILED` means a literal requirement is false. `NOT ESTABLISHED` means
the target may be directionally correct but lacks the row's required evidence.
These are audit dispositions, not coordinator-owned matrix status changes.

| Frozen ID | Disposition | Independent basis and evidence tier |
|---|---|---|
| `REQ-B7-00` | SATISFIED | Mechanism decision `DD-20260718-012` precedes implementation and records address-order, bit-width, and space rejection arguments. Tier 5 for ordering/decision; the cited table/address definitions are tier 1/2. |
| `REQ-B7-01` | SATISFIED | `bpSparseLevelDomain_covers`, tightened `bpSparseLevelCell_lt`, the local/global width theorems, and separate local/global little-o envelopes cover reachable indices without a public threshold. Tiers 1 and 2. |
| `REQ-B7-02` | SATISFIED | Local/global full-result equivalence at `InteriorDirectory.lean:2025-2077`, accepted call-site discharge, and Computation refinement at `:3440-3480` cover both packed level and span. Tiers 1 and 2. |
| `REQ-B7-03` | SATISFIED | The amended store computations read the packed level cell before the two span reads at `:2351-2398`; Computation/Costed refinements, store matching, footprint agreement, and whole-trace `readWord_only` preserve ordered real reads without synthetic replay. Tier 2, supported by tier 1 refinement theorems. |
| `REQ-B7-04` | SATISFIED IN SUBSTANCE | The frozen prediction that a new reviewer source/segment was necessary is refuted by the construction: the level tables are counted subregions of existing `.canonicalClose`/segment 20. W19 successful occurrence and producer provenance cover the new read, and completeness remains `< 23`. Tier 2. |
| `REQ-B7-05` | FAILED | The 210 named-component algebra and pinned 207/126 identities are sound, but semantic attainment/negation of `cost <= 30` is not proved and the same-name 328 contract moves to 352 despite the frozen anchor clause. Tiers 1 and 5. |
| `REQ-B7-06` | SATISFIED | Actual local/global level payloads feed raw overhead, the width bridge, 527 linear capacity, different local/global envelopes, public `buildPayload.length <= 2*n + overhead n`, and `LittleOLinear overhead`. Tiers 1 and 2. |
| `REQ-B7-07` | SATISFIED | `...WholeQueryGlobalWordTraceResult_readWord_only` at `SuccinctFinalRAM.lean:9708-9725` is proved over the amended whole-query object consumed by the headline chain. Tiers 1 and 2. |
| `REQ-B7-08` | FAILED | The charge-policy document retains deleted bridge names, old branch caps, unsupported tightness, and no complete residual-work inventory. Tier 5. |
| `REQ-B7-09` | NOT ESTABLISHED | Atomic counted-store/read landing and no integrated dead region are confirmed, but the universal per-commit green claim rests on process ledger evidence not independently replayed. Tiers 2 and 5. |
| `REQ-B7-10` | FAILED | The exact base-to-target diff check exits 2. Other recorded hygiene/lint results do not override that conjunct. Tier 4. |
| `INV-STORE-IDENTITY` | SATISFIED | The exact level-table payloads appended to the canonical interior component store are the objects read by `offsets.localLevel/globalLevel`, and the same payload-length chain feeds public space. Tier 2. |
| `INV-VALUE-DEPENDENCY` | NOT ESTABLISHED | Canonical value flow/refinement is checked, but the required decisive level-slot corruption witness changing the returned candidate is absent. Tiers 1/2 positive; required counterfactual missing. |
| `INV-NO-SYNTHETIC` | SATISFIED | The accepted Computation-generated reads refine the Costed twins; whole-trace event classification and `readWord_only` exclude a synthetic cost-only substitute. Tier 2. |
| `INV-ALL-SIZE` | SATISFIED | No readiness/size threshold is added; macro crossing supplies its own reachability hypothesis, small cases use unconditional bounds, and count zero is covered by the same domain/refinement surface. Tiers 1 and 2. |
| `INV-PUBLIC-COMPOSITION` | SATISFIED AT THEOREM LEVEL | The live capstone consumes the amended payload, store, trace, and 210 algebra together. Documentary aliases are stale, which is separately a P1 finding. Tiers 1 and 2. |
| `CHK-01` | SATISFIED | Exact-target RMQ, RMQPaper, and RMQExamples builds were already recorded green by A08 and were not economically repeated. Tier 4. |
| `CHK-02` | FAILED | Exact command exits 1 at stale `_sum_le_76` line 197. Tier 4. |
| `CHK-03` | SATISFIED | Exact-target headline axiom inventory exited 0 with the 210 anchor. Tier 4. |
| `CHK-04` | SATISFIED | The 21-window harness passes; exactly the nine positive-interior windows move, and the n=24 fixture makes the interior minimum/leftmost tie load-bearing. Tier 3. |
| `CHK-05` | SATISFIED | No forbidden Lean/Mathlib declaration is found; native-decision matches are scan strings in scripts, not RMQ/RMQExamples uses. Tier 4. |
| `CHK-06` | FAILED | The exact base-to-target diff check exits 2 on tracked `B7_STEP2_WIP.patch`. Tier 4. |
| `CHK-07` | SATISFIED | The exact-target strict design-decision gate is recorded exit 0; no contrary source fact was found. Tiers 4 and 5. |
| `CHK-08` | SATISFIED | Exact-target claim drift and paper topology runs were recorded exit 0 with the 210 anchor. Tier 4. |
| `STRETCH-01` | NOT ESTABLISHED | Two named families were resolved, but no complete auditable/mechanized reachability inventory exists. Tiers 1/2 for inspected entries; completeness missing. |

## Positive B7 implementation findings retained

### Live charged sparse-level reads and identity chain

The accepted chain still reaches the amended objects:

1. `SuccinctFinalRAM.lean:4426-4432`, accepted whole-query result;
2. `SuccinctFinalRAM.lean:3265-3280`, accepted global evaluator branch;
3. `SuccinctFinalRAM.lean:2330-2340`, all-size LCA route;
4. `ChargedFringeWiring.lean:50-64`, charged fringe/interior dispatch;
5. `ConcreteDirectoryRAM.lean:1188-1193`; and
6. `InteriorDirectory.lean:2351-2398`, local/global level-cell reads.

The local/global Costed twins at `InteriorDirectory.lean:1824-1869` read one
packed cell carrying level and span; the executed twins read the corresponding
component-store offsets and decode with `/ domain` and `% domain`. Full value
refinement is checked at `:2025-2077`, and store Computation refinement at
`:3440-3480`. This supports value/trace/store identity on the canonical object;
it does not supply the separate corruption witness discussed above.

Evidence tiers: 1 and 2.

### Width, capacity, and space

The macro-crossing local/global one-word fits at
`InteriorDirectory.lean:4440-4509` use the dispatcher's actual reachability
hypothesis. `10 <= base` is derived at `:4339-4365`, and branches without macro
crossing use the unconditional bounds at `:4240-4301`. The size-4 raw fit may
fail, but macro crossing is impossible there; no public size threshold is
introduced.

The width bridge at `:5883-5898`, raw-overhead decomposition at `:5921-5982`,
527 linear capacity at `:5984-6170`, payload equality at `:6172-6196`, distinct
local cube/global sampled envelopes at `:6313-6363`, and little-o closure at
`:6429-6494` remain coherent. `FlatPayload.lean:1929-1933` and
`SuccinctRMQClassic.lean:958-966` preserve the exact public upper-bound shape.

Evidence tiers: 1 and 2.

### Provenance, harness liveness, and segment vocabulary

`SuccinctFinalRAM.lean:9708-9725` proves `readWord_only` over the amended
whole-query object. W19's successful local-level read and producer path are at
`ReviewerReachabilitySmall.lean:2028-2238,2240-2266,2671-2808`. The new tables
remain under the existing canonical-close source/segment, while
`ReviewerPhysical.lean:88-113,891-928` and the whole-trace theorems retain
`segment < 23`.

The exact-target harness confirms all 21 windows, including the n=24 fixture
whose minimum values occur only in interior blocks. The moved set is exactly the
nine windows with positive interior count; the other twelve do not reach the
new read. The +2 versus +1 delta is consistent with shape-dependent packed-read
geometry rather than a count-driven loop.

Evidence tiers: 2 and 3.

## Objections considered and rejected

1. **“Blank matrix cells and Open status prove 24 requirements failed.”**
   Rejected by the protocol's matrix reconstruction semantics. Substantive
   row evidence may be append-only; every real row is judged above.
2. **“The CHK-02 failure is irrelevant because another branch owns it.”**
   Rejected. Attribution and frozen gate satisfaction are different questions;
   the exact required command exits 1 and no amendment waives it.
3. **“Patch context whitespace is not a source defect, so CHK-06 passes.”**
   Rejected. It may not be a Lean defect, but the exact frozen command exits 2.
4. **“Bare exact proves the cross-macro branch costs 33.”** Rejected. It proves
   only an upper bound already matching the goal.
5. **“The 328→352 change was wholly silent.”** Rejected.
   `PAPER_MODEL_ADEQUACY.md:129-135` discloses it; the defect is lack of an
   approved frozen-contract change or pinned compatibility identity.
6. **“WordReads or the recursive local decoder still executes the silent log on
   the accepted route.”** Rejected for the inspected caller families: WordReads
   feeds compatibility/spec surfaces, and the accepted same-block path uses the
   charged capped chunk fold.
7. **“The shape-dependent +1/+2 harness delta indicates an unexamined
   count-dependent loop.”** Rejected. It follows fixed-width word geometry.
8. **“Every current document is stale.”** Rejected. `WHAT_IS_PROVED.md` and
   `PAPER_CLAIM_CORRESPONDENCE.md` correctly describe 210/33; the problem is
   contradictory current surfaces.

## Command and skipped-command ledger

### New continuation commands

| Command | Exit | Duration | Result |
|---|---:|---:|---|
| `git branch --show-current; git rev-parse HEAD; git cat-file -t 6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25; git cat-file -t bd854edaa65944d5a7fa0fac5667e9572c370bbb; git status --short` | 0 | 3,900 ms | Correct audit branch/head; both exact objects exist; tree initially clean |
| `git show bd854edaa65944d5a7fa0fac5667e9572c370bbb:docs/internal/AUDIT_PROTOCOL.md` | 0 | 3,500 ms | Protocol read in full |
| matrix-ID inventory `rg` shown below | 0 | 800 ms | Reconstructed 25 real frozen IDs |
| `lake env lean scripts/wordram_axiom_check.lean` | 1 | 255,000 ms | CHK-02 fails; line 197 names removed `_sum_le_76` |
| `git diff --check f6564ec..6ad4198cf09c0d4e103ae0e1c0a5c7a084d0ae25` | 2 | 315 ms | CHK-06 fails on tracked `B7_STEP2_WIP.patch` context whitespace |
| live/stale theorem inventory `rg` shown below | 0 | 1,100 ms | Script has `_76`; live source/headline have `_210` |

The exact two `rg` commands abbreviated in the table were:

```powershell
rg -n "^\| (REQ-B7-|INV-|CHK-|STRETCH-)" docs/internal/B7_SPARSE_LEVEL_ACCEPTANCE_MATRIX.md
rg -n "concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_nonSyntheticWeight_sum_le_(76|210)|nonSyntheticWeight_sum_le_76" RMQ scripts/wordram_axiom_check.lean
```

### Exact-target results retained, not rerun

These were already run and recorded by A08 against exact `6ad4198...`; the
continuation contract explicitly forbids repeating the multi-minute campaign
merely to edit the report:

- `lake build RMQ`: exit 0, 388,281 ms;
- `lake build RMQPaper RMQExamples`: exit 0, 51,955 ms;
- `lake exe rmq_succinct_classic_cost_harness`: exit 0, 45,036 ms, all 21
  windows agree and bound 210;
- `lake env lean scripts/headline_axiom_check.lean`: exit 0, 68,349 ms;
- direct-module axiom check for the final 210 and `queryCost_eq`: exit 0,
  3,803 ms, no axioms;
- `powershell -ExecutionPolicy Bypass -File scripts/paper_topology_lint.ps1`:
  exit 0, 127,207 ms;
- `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1`:
  exit 0, 10,169 ms; and
- the two hygiene `rg` scans: no forbidden RMQ/Mathlib use and no actual
  `native_decide`/`Lean.ofReduceBool` use in RMQ/RMQExamples.

Evidence tiers: 3 for the harness; 4 for builds, axiom inventories, lint, and
scans.

### Deliberately skipped

- No root rebuild, harness rerun, headline axiom campaign, or topology rerun:
  exact-target evidence already exists and the continuation contract says not
  to repeat it.
- `scripts/axiom_check.lean`, `lake exe rmq_succinct_classic_validate`, and the
  retired-name `scripts/wordram_axiom_check.lean` beyond the one required
  CHK-02 run were not treated as B7 implementation diagnostics.
- No historical per-commit rebuild campaign was attempted; this is why
  REQ-B7-09 remains `NOT ESTABLISHED` as a whole.

The post-report strict claim-drift, strict design-decision, report-diff, exact
changed-path, and clean-status checks are recorded in the final section.

## Roadmap alignment

In letter, B7 adds an explicit packed store/read/space layer without changing
the half-open RMQ contract, leftmost tie policy, value-level `List Int`
semantics, or Lean/Std plus `omega` footprint. It retains the public
`2*n + o(n)` payload upper-bound shape and a constant charged-query cap.

In spirit, the mechanism is aligned with the repository's highest-value
direction: replace an input-growing controller computation used for a read
address with accounted storage accessed through the accepted explicit store.
The mechanism therefore advances the succinct upper-bound story rather than
adding a decorative table.

The roadmap node is not closed because the frozen gate surface and public
history are inconsistent, semantic tightness/value-dependency anti-vacuity is
incomplete, and `STRETCH-01` supplies no complete reachability inventory.

## Best next target

The best proof target is a concrete **reachable exact-33 cross-macro execution
witness on the accepted explicit-store object**, together with a checked
corollary refuting the corresponding universal `cost <= 30` claim and a
decisive level-slot corruption witness that changes the returned candidate.
That closes the semantic anti-vacuity gap instead of inferring tightness from
proof syntax.

The same repair pass must make the two literal gates green, pin or rename the
328/352 historical surface, and repair the contradictory current documents.
After those material corrections, protocol requires a fresh acceptance audit;
this continuation cannot confer acceptance.

## Proof digestion

**Conceptual change.** B7 moves sparse level/span selection out of silent
runtime `Nat.log2`/power computation and into a count-indexed packed table read
through the accepted component store.

**Plain English.** The query now pays to learn which sparse-table level and
span it will use; the information is stored once and read when needed.

**Live assumptions.** The result is about the repository's charged trace
model, where attempted payload-word reads are charged and controller
arithmetic/div/mod/dispatch are not individually CPU-costed. One-word fit on
the maximizing shape uses the route's actual macro-crossing reachability
hypothesis; other branches use unconditional multiword bounds. Precomputed
table construction is outside query cost but inside payload space. This is not
a compiled-runtime theorem.

**Skeptical next question.** Can the repository mechanize reachability from the
whole-query root strongly enough to enumerate every uncharged controller
operation, while also exhibiting an actual accepted execution whose returned
candidate depends decisively on the level cell and whose cost reaches 33?

## Qualified answer about remaining uncharged input-growing work

For the families actually inspected, no named candidate remains: the
runtime-derived sparse logarithm/span is replaced by a charged packed-cell read,
and the recursive same-block decoder is not the accepted implementation. The
accepted same-block path uses the charged capped chunk fold.

A universal “no remaining input-growing uncharged computation anywhere on the
accepted route” conclusion is **not established at this target** because
`STRETCH-01` lacks a complete auditable reachability derivation. That is a
qualification of inventory completeness, not a retraction of the specific B7
mechanism finding.

## Final report-tree verification

The following commands were run on the tree containing this corrected report,
before commit:

| Command | Exit | Duration | Result |
|---|---:|---:|---|
| `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict` | 0 | 7,081 ms | 749 hits, 0 strict failures |
| `powershell -ExecutionPolicy Bypass -File scripts/design_decision_check.ps1 -Strict -Base 1bc6b3597b97720c5c5dad0a2e87277cf28fd7ea` | 0 | 1,216 ms | No design-sensitive paths detected; report-only correction is inapplicable to a new design decision |
| `git diff --check` | 0 | included in 303 ms pair | Clean unstaged delta |
| `git diff --cached --check` | 0 | included in 303 ms pair | Clean staged report delta |

After this result record was inserted, strict claim drift, strict design-decision
checking, and the staged diff check were rerun once more on the final report
text before commit. After commit, the exact base-to-HEAD report diff check,
changed-path inventory, and clean status were checked as the completion gate.
