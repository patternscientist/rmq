# A09 endgame-plan and governance-delta fresh-blind audit

Auditor: `A09-ENDGAME-AUD1`

Mode: FRESH BLIND DELTA

Base: `bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4`

Target: `0e71b828ae975ba42881edf4c023813e80f070a0`

Branch under audit: `claude/e1-strategy-memo`

Authorization: report-only. This report is the only tracked file written by the
auditor.

## Findings

### P0

None.

### P1 — the revised public cost-model sentence is false

The read-only part of the new public wording is unusually strong and is
proved. The rest of the same sentence is not.

`RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` is an
`abbrev` (`RMQ/Headlines/RMQ.lean:595-596`) for
`RMQ.SuccinctFinal.concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult_readWord_only`
(`RMQ/Core/SuccinctFinalRAM.lean:10136-10154`). Fully expanded, its proposition
is:

```text
∀ (shape : Cartesian.CartesianShape) (left right : Nat)
    (event : WordRAM.TraceEvent),
  event ∈
      (concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult
        shape left right).trace →
  event.isReadWord
```

There are no premises hidden by the headline alias: no `ValidRange`, readiness,
nonempty-shape, size-floor, or supplied-store hypothesis. `shape`, `left`,
`right`, and `event` are all universally quantified. The validity domain is
therefore every Cartesian shape and every pair of natural-number endpoints,
including guarded/invalid query inputs; the theorem is about the emitted-event
vocabulary, not query correctness or storage agreement. `TraceEvent.isReadWord`
is true only for `readWord` and false for `wordRank`, `wordSelect`, and the
synthetic marker (`RMQ/Core/WordRAM.lean:103-108,135-139`). Thus README
`README.md:223-230` and the first read-only clause of
`artifact/CLAIMS.md:43-52` do not need an omitted query guard.

The false clause is `artifact/CLAIMS.md:46-49`: after correctly saying that the
canonical route does not emit `wordRank` or `wordSelect`, it says those
constructors “are not charged primitives of the current cost model.”
`TraceResult.toCosted` charges `trace.length`
(`RMQ/Core/WordRAM.lean:560-572,761-763`), while
`TraceEvent.nonSyntheticWeight` assigns weight one to `readWord`, `wordRank`,
and `wordSelect` (`RMQ/Core/WordRAM.lean:162-175`). The legacy evaluator really
emits the latter two constructors
(`RMQ/Core/WordRAM.lean:944-966`). No canonical alias or wrapper was found that
evades the read-only theorem, but an arbitrary/legacy trace containing those
events is charged. The exact correction is: the canonical route does not emit
them; if another route emits them, `toCosted` still charges them through trace
length.

This is also inconsistent with two of the other 16 current-fact surfaces.
`docs/FAMILY_SUMMARY.md:36-49` says all three genuine constructors have weight
one and explicitly calls the controller inventory documentary rather than a
checked small-step inventory. `docs/WHAT_IS_PROVED.md:664-670` likewise retains
unit cost for the bounded word primitives. The policy’s
`currentFactSurfacePathRegex` does enumerate 18 paths
(`docs/internal/CLAIM_DRIFT_POLICY.json`, `currentFactSurfacePathRegex`), but
the syntactic policy does not establish semantic agreement among them.

The controller-work part is directionally accurate but over-certified. Since
cost is trace length, work not represented by an emitted event is uncharged.
That supports dispatch, boundary arithmetic, local decode/in-word work,
branches/comparisons, candidate/option selection, and witness assembly as
uncharged. It does not prove one checked bounded-controller theorem covering
the whole English inventory. The repository itself says that bounded-per-step
adequacy remains documentary (`docs/PAPER_MODEL_ADEQUACY.md:290-303`;
`docs/FAMILY_SUMMARY.md:46-49`). In addition, the two public enumerations are
not identical: `artifact/CLAIMS.md:49-52` names query/register input access,
while `README.md:227-230` omits it.

The stated reason for changing the old text is also wrong. At the base,
`README.md:223-225` described a model-relative substrate with unit-cost
word-level operations, branches, comparisons, and table accesses “where
explicitly modeled”; `artifact/CLAIMS.md:42-47` said that payload reads and
word-rank/select events were charged while controller work was uncharged.
Those statements were not mutually contradictory. The first was qualified by
what the model emits; the second described the actual current event boundary.
Consequently the contradiction asserted by `DD-20260725-006`
(`docs/internal/DESIGN_DECISIONS.md:5091-5119`) was not independently
reproduced.

This finding meets the prompt’s rejection condition: a changed public sentence
is false and stronger than the cost definition.

### P1 — the claimed `210` fresh-blind lineage is false

`docs/internal/E1_ENDGAME_WEEK1_GATE_RESULTS.md:13-19` says the `210` literal
has never received a fresh-blind positive verdict and that A04 at `328` was the
last such verdict. The repository contains a counterexample:
`docs/internal/audit_reports/2026-07-22_M1_R5_R9_fresh_blind.md:1-24` identifies
itself as a fresh-blind delta audit and gives a positive, candidate-scoped
verdict for `977a4df8b5d9e908fe66d012dd242006790ebaf3`. Its
`lines 103-128,223,269,318` independently expand and pass the same-execution
`129 + 81 = 210` derivation and identify the public `<= 210` surface.

That verdict is deliberately narrower than a release-commit audit. It does not
certify the whole `328 → 76 → 207 → 210` migration. The target text, however,
does not make that distinction; “never ... by any fresh blind audit” is false.
The defensible statement is that no fresh-blind report located here gives a
positive verdict to one release candidate containing the entire migration.

The remaining lineage was reproduced:

- A05 at `76`, A06 at `76`, and A07 at `207` are negative reports, and A08 at
  `210` records a block rather than a verdict.
- `git merge-base --is-ancestor` returned success for the A07 code target
  `bacd41b5...` and A08 code target `6ad4198...` against `main`; it also returned
  success for the scoped M1 candidate `977a4df8...` and its report commit
  `e7c936d8...`.
- The A07 report commit is not an ancestor of `main`; the A08 report commit is.

`docs/internal/RMQ_ENDGAME_PLAN.md:282-296` compounds the error by calling the
A05/A06/A07 records “acceptance records” and “accepted-but-unmerged evidence.”
They are negative evidence. The plan and gate-results document must distinguish
code ancestry, report ancestry, scoped candidate verdicts, and a whole-release
verdict.

This is the delta’s most consequential factual defect because
`E1_ENDGAME_WEEK1_GATE_RESULTS.md:21-26,187-190` and
`WORKFLOW_DESIGN_DECISIONS.md:6618-6620` use the false premise to change the
release-audit disposition.

### P1 — the week-1 gate results contain a false arithmetic blocker and an
overstated S1 conclusion

`docs/internal/E1_ENDGAME_WEEK1_GATE_RESULTS.md:196-201` says a width-`w`
all-ones dead cell decodes to exactly `2^w` and therefore violates `< 2^w`.
The cited B1 source at `1727de15f2030bfb9296a9b31508bc00581aa33a`,
`RMQ/Validation/E1FinalArchitectureAdjudication.lean:92-96`, defines the word
as `List.replicate width true`. The decoder at that commit,
`RMQ/Core/SuccinctSpace/WordStore.lean:15-28`, is ordinary little-endian binary
recursion. The value is `2^w - 1`, not `2^w`, and it satisfies the strict bound
for positive `w`. The same false arithmetic is present in the inherited
decision at `docs/internal/DESIGN_DECISIONS.md:4914`; repeating it in a new
gate-results document does not verify it.

The same document says shape dependence is “genuinely” established
(`E1_ENDGAME_WEEK1_GATE_RESULTS.md:56-65`) and then correctly admits that the
same-size, two-shape witness does not exist at any commit and is only “highly
likely” (`:80-85`). The formulas are kernel evidence:
`RMQ/Core/SuccinctClose/GenericSelect/RelativeTables.lean:16-30,36-47,83-89,267-283`
makes the long-table length depend on the number of long superblocks. A formula
with a shape parameter is not by itself a witness that two equal-size shapes
produce different lengths. The verified statement is the formula; the
non-constancy claim remains a research conclusion pending its named witness.

Probe (b) is also labeled `CLOSED-PASS`
(`E1_ENDGAME_WEEK1_GATE_RESULTS.md:124-132`) even though the cited B1 validation
file is absent from the target tree and `1727de15...` is not an ancestor of
target or `main`. The arithmetic on that branch is correct: its capacity
envelope is `800000*(n+1)+50`, giving width 20 at `n = 0`, sufficient for the
listed constants. This should be labeled branch arithmetic/probe evidence,
not exact-target kernel closure. The document does disclose the B1 ancestry
caveat at `:118-122`, so this is a tier-label correction, not a refutation of
the calculation.

These are factual/verification-label failures in one of the three new
documents. The dead-cell claim is outright false; the shape conclusion promotes
an expressly pending witness to established fact.

### P1 — the S1 amendment activates the right rung but leaves a refuted blocker
inside it

The activation itself is accurate. At the base,
`docs/internal/RMQ_FINAL_ROADMAP.md:270-284` records M1 closed, and both the M1
candidate and report hashes are ancestors of base `main`. The original S1 rung
(`RMQ_FINAL_ROADMAP.md:409-424` at the base) names only M1 as its sequencing
prerequisite. Therefore target `RMQ_FINAL_ROADMAP.md:411-419` truthfully changes
S1 from deferred to active on its only stated prerequisite.

The rung nevertheless retains, at `RMQ_FINAL_ROADMAP.md:427-433`, the assertion
that no explicit chunking decoder exists and that a uniform-width decoder is
needed. Both halves are refuted by the target repository and by the new
gate-results text:

- `RMQ/Core/SuccinctSpace/WordStore.lean:140-156` defines
  `chunkPayloadWords`; `:158-203` proves
  `flattenPayloadWords_chunkPayloadWords`, exact recovery after chunking.
- `BoundedPayloadWordStore.ofChunksWithSentinel`
  (`WordStore.lean:568-602`) appends `payload.length + 1` empty words. The live
  builder uses that sentinel construction
  (`RMQ/Core/SuccinctFinal.lean:832-848`;
  `RMQ/Core/SuccinctRank.lean:1331-1348`), while the checked physical theorem
  proves only `word.length ≤ reviewerWordBits`
  (`RMQ/Core/SuccinctFinal/ReviewerPhysical.lean:2078-2089`). Thus a positive
  uniform exact-width theorem is false for sentinel entries.

`E1_ENDGAME_WEEK1_GATE_RESULTS.md:30-49` and
`WORKFLOW_DESIGN_DECISIONS.md:6600-6604` explicitly say the roadmap blocker is
wrong in both directions. Leaving it in the amended rung creates an
intra-delta contradiction on the authoritative roadmap. The status is right;
the rung as amended is not.

### P1 — the target does not reproduce its claimed strict policy receipt

The target receipt at `docs/internal/DESIGN_DECISIONS.md:5139` says
`1,472` classified hits and zero strict failures. Exact policy emulation
produced:

| object | classified hits | strict failures |
|---|---:|---:|
| parent `761fcd2` | 1,472 | 0 |
| target `0e71b82` | 1,484 | 1 |

The one target failure is
`docs/internal/E1_ENDGAME_WEEK1_GATE_RESULTS.md:165`, where a retired
paper-query alias was spelled out in an audit-lineage discussion. This report
intentionally paraphrases that alias rather than repeating it. The target adds
11 classified hits in the gate-results document and one workflow-decision hit;
the stored receipt is therefore a true receipt for the parent and stale/false
for the final target.

The production script run on the target-descendant audit checkout initially
reproduced the same strict failure. Commit `411409a`, after the audit target,
paraphrases that occurrence; it is not evidence that target `0e71b82` passed.
The exact eight-path whole-delta design-decision emulation and six per-commit
emulations produced zero strict failures, so the defect is confined to the
claim-drift receipt rather than decision-ID/append policy.

This meets the explicit rejection condition for a “verified” result not
verified on the final target.

### P1 — the supersessions use a lawful instrument but are not fully factually
grounded

The strongest premise of `DD-20260725-005` is correct. The immutable PRELOGIC
blob `086abee6279cb0fa8ed01975abc5cdbd4e0dfb27` defines, for a fixed shared
input,

```text
P_current shared := Nonempty (BoundedReceipt .current shared)
```

and its exact negative as `¬ Nonempty (BoundedReceipt .current shared)`
(`blob lines 270-274`). Equivalently, every permitted current-route receipt for
that fixed shared input implies `False`. Its disposition table calls the
historical case contract-admissible but unresolved and requires a B3 positive
plus the exact B2 negative (`lines 537-544`); its handoff asks whether the
negative covers every permitted base receipt (`lines 667-668`). The handoff’s
three-arm summary was therefore derived drift: the accepted input has two
selection arms, with B4 as an adapter, not a third selected architecture.

Repository-wide decision/search evidence also supports two other premises:
no recorded decision requires the paper to contain an A4 selection, and
`DD-20260722-003` did not land on `main`. A repository owner decision may
supersede an earlier plan/ordering, the new IDs are unique and append-only, and
the exact whole-delta/per-commit decision-policy emulations passed.

Four statements nevertheless overreach:

1. The strategy memo calls the historical arm “structurally unreachable”
   (`docs/internal/E1_ARCH_STRATEGY_MEMO_2026-07-25.md:34-42`).
   PRELOGIC says contract-admissible and unresolved, not impossible. The
   runway may make the universal negative unrealistic; that is different.
2. `DD-20260725-005` says `DD-20260722-003` was adopted “in substance”
   (`DESIGN_DECISIONS.md:5056-5060`) without recording its historical source
   commit or making clear that this new decision is the first canonical record.
3. The standing rule that derived text always yields to its accepted input
   (`DESIGN_DECISIONS.md:5066-5073`) is too broad. The prior, narrower defect
   rule covered a frozen clause contradicting another requirement from the
   same accepted input (`DESIGN_DECISIONS.md:4930-4938` at the base). A
   legitimately owner-ratified later amendment must not be discarded merely
   because text is “derived.” Calling this the “fourth” instance is defensible
   only under a convention-dependent broad grouping, not as an objective count.
4. `DD-20260725-004` accurately identifies the historical plan at
   `25626847233db16c7dbae638f299f3807f648031`: its
   `docs/internal/RMQ_FINAL_PLAN_2026-07-07.md:69-79` makes word rank/select
   instruction kinds unit-cost. `DD-20260717-C05-001`
   (`DESIGN_DECISIONS.md:2446-2479` at the base) rejected those as the primary
   route, but retained that option as a pivot fallback. The new decision
   describes it as categorically rejected. The correct ground is that the
   successor ratification now retires the fallback.

The supersessions are procedurally lawful, but their recorded factual bases are
not fully correct. On the prompt’s conjunctive criterion, they do not pass
without correction.

### P2 — the ratified plan silently loses one of its own gate conditions

`docs/internal/RMQ_ENDGAME_PLAN.md:118-122` caps the whole E1 dry-run merge,
including known collision reconciliation, at three sessions. New
`WDD-20260725-009` moves ID reconciliation outside the cap
(`docs/internal/WORKFLOW_DESIGN_DECISIONS.md:6607-6613`) without amending the
ratified plan or recording a separate owner decision for that relaxation. This
is a governance-drift defect, even if the scheduling choice is sensible.

The same plan still says “ratifying-owner review pending” in its committed
header (`RMQ_ENDGAME_PLAN.md:3`) while decisions later in the delta call it
ratified. That stale status is a P3 presentation defect, recorded below.

### P2 — proposed publication claims exceed the evidence and the novelty search

The plan marks as “verified defensible” a claim of strictly more
between-events boundedness (`docs/internal/RMQ_ENDGAME_PLAN.md:249-251`); the
memo strengthens it to “than any cited precedent” and proposes shipping it
(`docs/internal/E1_ARCH_STRATEGY_MEMO_2026-07-25.md:74-86,116-121`). The
repository’s current policy charges attempted payload reads only and leaves
dispatch, decode, arithmetic, branching, and other controller work uncharged
(`docs/PAPER_MODEL_ADEQUACY.md:169-176`). It supplies no formal ordering that
makes this model strictly stronger than a compiler/ISA or LLVM cost theorem.

The cited primary sources make the comparison especially unsafe:

- Haslbeck–Lammich count LLVM-level operations broadly and describe the result
  as a hardware-time approximation
  ([TOPLAS paper](https://ris.utwente.nl/ws/files/297739784/3486169.pdf),
  pp. 13-14).
- Tockman et al. carry instruction/load/store/jump bounds through a verified
  compiler to RISC-V
  ([CPP 2026 paper](https://adam.chlipala.net/papers/MetricsCPP26/MetricsCPP26.pdf),
  pp. 1-4).
- Liu–Yu’s RMQ lower bound is indeed cell-probe: memory accesses count and
  other computation is free
  ([paper](https://www.cs.princeton.edu/~hy2/files/suc_rmq.pdf), pp. 2-3).

The memo’s universal statement that no verified word-RAM/ISA-level
data-structure cost theorem exists in any ITP
(`E1_ARCH_STRATEGY_MEMO_2026-07-25.md:78-79`) is also presented as fact even
though the plan says the novelty search has never been performed
(`RMQ_ENDGAME_PLAN.md:236-240`). No counterexample was established in this
focused audit, but a finite search cannot verify that universal absence claim.
It must be search-bounded and provisional.

Finally, `RMQ_ENDGAME_PLAN.md:241-248` says the delta over prior succinct
mechanization includes machine-checked `o(n)`. Affeldt et al. already report a
Coq formalization of a constant-time, `o(n)`-space rank structure
([ITP 2019 paper](https://www.math.nagoya-u.ac.jp/~garrigue/papers/compact-itp19.pdf),
p. 16). A defensible novelty statement must be a narrower conjunction—such as
RMQ-specific `2n+o(n)` plus the precisely qualified execution result—pending
the scheduled G7 search.

### P2 — the twelve-row publication checklist misses two physical-model attacks

The checklist in `docs/internal/RMQ_ENDGAME_PLAN.md:386-399` does not expressly
require either of the following:

1. **Physical allocation/capacity accounting.** README itself disclaims any
   bound on allocated cells or padded capacity (`README.md:238-240`), while
   `BoundedPayloadWordStore.ofChunksWithSentinel` allocates
   `payload.length + 1` empty sentinel words
   (`WordStore.lean:568-602`). Checklist row 2 asks for space/query-object
   identity, but not a packed, addressable representation whose allocated
   capacity is within the advertised succinct bound. A hostile succinct-data-
   structure reviewer can attack the gap between flattened logical payload
   bits and a physically allocated indexed store.
2. **Valid-query probe totality/accounting.** `Store.readWord?` returns `none`
   on an invalid segment/index (`RMQ/Core/WordRAM.lean:68-72`); the supplied-
   store trace retains and charges failed reads
   (`RMQ/Core/SuccinctFinalStoreParam.lean:3616-3654`;
   `docs/PAPER_MODEL_ADEQUACY.md:169-173`). The backing theorem covers events
   containing `some word`, not all attempted reads
   (`SuccinctFinalStoreParam.lean:3713-3734`;
   `SuccinctFinalRAM.lean:11022-11042`). Rows 2 and 5 do not require a theorem
   that every valid public query reads an in-range counted cell, or an explicit
   model justification/accounting rule for reachable failed/dead reads.

These are missing acceptance clauses inside the existing space/model work, not
proposals for new lanes. The second remains a P2 because this audit did not
establish a reachable failed read on a valid canonical query.

### P3 — stale and imprecise status text

- The ratified plan header still says owner review is pending
  (`docs/internal/RMQ_ENDGAME_PLAN.md:3`).
- `E1_ENDGAME_WEEK1_GATE_RESULTS.md:179-180` truncates the third ARCH2 collision
  ID. `docs/internal/E1_ARCH2_CONTRACT_REPAIR_PREP.md:331-336` identifies the
  pre-existing duplicate exactly as `WDD-20260719-001`; the other two pairs are
  `DD-20260723-001` and `WDD-20260723-001`.
- The prompt’s scope synopsis mentions only WDD-008/-009, but the actual
  eight-path delta also appends WDD-005 through WDD-007. This did not hide a
  changed path and did not affect the verdict.

## Required separate verdicts

1. **Changed public sentences true and supported: NO.** The universally
   quantified canonical read-only claim is true for all shapes and endpoint
   pairs. The statement that `wordRank`/`wordSelect` are not charged primitives
   is false, and the blanket checked-boundedness implication for controller
   work is unsupported.
2. **Supersessions lawful and factually grounded: NO, as a conjunction.** The
   owner-decision mechanism is lawful; the PRELOGIC universal quantifier, lack
   of a paper-selection mandate, non-main status of the earlier proposed
   decision, and historical plan contents were verified. The “structurally
   unreachable,” categorical-prior-rejection, adopted-in-substance, and
   unrestricted derived-text-rule grounds require correction.
3. **Roadmap amendments accurate: NO, as committed.** S1 activation and the E1
   status paragraph are accurate. The S1 rung retains a blocker refuted by
   checked target definitions and by this delta’s own gate-results document.
4. **`210` acceptance-chain claim correct: NO.** The negative A05-A08 lineage
   and the two named code-target ancestries are real; the “never any
   fresh-blind audit” and “last at 328” statements omit the scoped M1
   fresh-blind positive verdict over the `210` derivation.

## Positive checks and stale objections dismissed

- **“The headline theorem might be guarded or pinned.” Dismissed.** Its fully
  expanded type has four universal binders and no hypotheses.
- **“A legacy word-rank/select emitter refutes canonical read-only.”
  Dismissed.** It refutes only the decharging claim. Membership in the exact
  canonical trace implies `isReadWord`.
- **“M1 is not actually closed, so S1 must remain deferred.” Dismissed.** The
  base roadmap records closure, its only stated S1 prerequisite is M1, and the
  candidate/report hashes are ancestors of base `main`.
- **“The chunking decoder is absent.” Dismissed.** The definition and exact
  flattening theorem are at `WordStore.lean:140-203`.
- **“The E1 amendment names a nonexistent or obviously tainted theorem.”
  Dismissed.** At `648e51247f6c07663008ba2955a98e03b4a1ba4f`,
  `RMQ/Core/WordRAM/E1AmendedTarget.lean:620-636` contains the named theorem;
  its proposition is at `:359-436`, with valid/invalid clauses, six-category
  identity, the literal bound, and `ProgramFits`. A source-wide forbidden-token
  scan at that commit found no `sorry`, `admit`, `axiom`, `unsafe`, `opaque`,
  `implemented_by`, `partial`, `extern`, `noncomputable`, Mathlib import,
  `native_decide`, or `Lean.ofReduceBool`. This establishes source hygiene and
  existence only; it does not audit the unmerged lane’s substance.
- **“A4 supersession is inherently unlawful.” Dismissed.** No recorded paper
  requirement was found, and owner decisions can supersede prior scheduling
  text. The defects are factual scope and wording, not absence of authority.
- **“The strict-scan receipt was never true.” Dismissed.** It is exact for
  parent `761fcd2`; it was not rerun or refreshed after the final document.
- **“The roadmap’s E1 merge-collision count is invented.” Dismissed.** Comparing
  `648e512...` to target yields exactly seven conflicting DD IDs 002-008, with
  different titles/content at the branch and target line sets.
- **“G9’s retired-alias scanner problem is speculative.” Dismissed.** The
  target strict policy and topology linter both reject a non-allowed tracked
  occurrence, and the gate invokes both. The defect is that the target itself
  contained one.
- **“Narrative estimates are defects merely because they are estimates.”
  Dismissed.** The gate-results header distinguishes kernel, committed prose,
  and research narrative (`:3-9`). Session/agent estimates are not promoted
  here. Findings attach only where the document says verified/closed, asserts a
  false fact, or makes tiers internally misleading.
- **“No manuscript source on main” is stale. Dismissed.** `git ls-tree -r main`
  found no `.tex`, `.bib`, manuscript, or paper source path.
- **Primary-source comparison positives.** Haslbeck–Lammich’s LLVM/Level-2
  characterization, Tockman et al.’s verified RISC-V endpoint and non-data-
  structure case study, and Liu–Yu’s cell-probe RMQ model all survived. What
  failed was the stronger cross-model ordering/universal novelty inference.

## Governance preflight and scope identity

The session exposed exactly one RMQ project skill: `rmq-proof-sprint`. It was
reported as the nonempty runtime catalog, but no audit-worker role skill was
claimed. The exact preflight used:

```powershell
powershell -ExecutionPolicy Bypass -File scripts/project_skill_preflight.ps1 `
  -GovernanceRef f0c7232a8a52b8d61ead5e96d72a8a849bc094b5 `
  -AllowNoRequiredSkills `
  -RuntimeProjectSkills "rmq-proof-sprint"
```

It passed in the target-branch checkout in 4.596 s. Both governance
`f0c7232a...` and target `0e71b82...` are ancestors of that checkout. The same
command was first attempted in the invocation’s historical root checkout,
where the script was absent and the governance hash was not an ancestor; that
failed attempt did not certify anything. No `-RequiredSkills` argument was
supplied.

`git log --oneline bc5851a..0e71b82` returned the expected six commits.
`git diff --name-only bc5851a 0e71b82` returned exactly the eight scoped paths.
The proof/tooling path diff was empty. The audit checkout began with only the
pre-existing untracked `.claude/settings.local.json`; it was not read, changed,
staged, or committed.

## Command and verification ledger

Timings are wall-clock values reported by the command runner or, for the
object-level policy emulations, by the read-only audit worker. Failed diagnostic
attempts are included rather than silently discarded.

| # | Command or command group | Time | Outcome |
|---:|---|---:|---|
| 1 | Read `rmq-proof-sprint/SKILL.md` with `Get-Content` | 0.5 s | complete |
| 2 | Initial combined process launch | n/a | Windows `CreateProcessWithLogonW` failure; no command ran |
| 3 | `git status --short --branch` in invocation root | 0.9 s | dirty historical checkout identified |
| 4 | root `rev-parse`/governance ancestry group | 0.285 s internal (214.9 s tool round trip) | governance not ancestor there |
| 5 | `Get-Content scripts/project_skill_preflight.ps1` in root | 1.1 s | path absent |
| 6 | `git show 0e71b82:scripts/project_skill_preflight.ps1` | 1.3 s | script inspected |
| 7 | target `ls-tree` skill inventory | 1.3 s | repository skill catalog inspected |
| 8 | runtime `Get-ChildItem` skill inventory | 1.7 s | runtime RMQ catalog = `rmq-proof-sprint` |
| 9 | exact preflight in root | 0.208 s | expected failure: script absent |
| 10 | `git worktree list --porcelain` | 0.527 s | existing target-branch checkout found |
| 11 | worktree target-hash search | 2.1 s | target descendant located |
| 12 | branch search | 2.2 s | `claude/e1-strategy-memo` located |
| 13 | first worktree status attempt | 0.307 s | Git unsafe-ownership refusal; no mutation |
| 14 | safe-directory status/ancestry group | 0.390 s | clean tracked tree; both ancestors |
| 15 | mandated project-skill preflight | 4.596 s | PASS |
| 16 | required six-commit `git log` | 0.120 s | six commits |
| 17 | required `git diff --name-only` | 0.113 s | eight paths |
| 18 | required public-surface diff | 0.116 s | two substantive public edits |
| 19 | target endgame-plan read | 1.1 s | complete |
| 20 | target strategy-memo read | 1.3 s | complete |
| 21 | target week-1-results read | 1.1 s | complete |
| 22 | decision/roadmap delta read | 1.2 s | complete |
| 23 | base roadmap search | 1.6 s | S1/M1 locations |
| 24 | base roadmap excerpt | 1.2 s | only stated S1 prerequisite = M1 |
| 25 | M1 status excerpt | 1.1 s | closure record located |
| 26 | M1 ancestry checks | 0.237 s | candidate and report ancestors |
| 27 | WordStore decoder/sentinel excerpts | 1.2 s | decoder and sentinel verified |
| 28 | E1 theorem search at `648e512` | 0.6 s | theorem exists |
| 29 | E1 source/hygiene group | 1.3 s | source clean for forbidden tokens |
| 30 | E1 definition search | 0.5 s | load-bearing definitions located |
| 31 | E1 exact proposition read | 1.2 s | quantified statement expanded |
| 32 | first `lake env lean` on E1 source | 0.194 s | failed fetching toolchain in sandbox |
| 33 | escalated `lake env lean` retry | 1.2 s | toolchain ran; failed on missing built RMQ module |
| 34 | first `.lake` existence probe | 1.1 s | invalid PowerShell syntax |
| 35 | corrected `.lake` probe | 1.5 s | no usable target build artifacts |
| 36 | headline-alias excerpt | 1.7 s | exact abbreviation established |
| 37 | source-theorem search | 0.8 s | underlying theorem located |
| 38 | source-theorem excerpt | 1.9 s | all quantifiers/hypotheses expanded |
| 39 | TraceEvent/isReadWord excerpt | 2.4 s | exact four-constructor domain |
| 40 | controller-cost source search | 2.5 s | charged boundary located |
| 41 | boundedness occurrence search | 2.7 s | no whole-inventory theorem found |
| 42 | model-adequacy excerpts | 1.8 s | documentary limitation verified |
| 43 | production strict claim scan on pre-fix descendant | 12.135 s | FAIL, same target occurrence |
| 44 | strict-output filter | 13.7 s | failure isolated |
| 45 | captured filtered strict scan | 10.7 s | same one occurrence |
| 46 | pre-report `git diff --check` | 0.127 s | pass |
| 47 | proof/tooling diff check | 0.123 s | empty |
| 48 | scoped M1 report excerpts | 1.3 s | fresh-blind `210` verdict verified |
| 49 | base public wording excerpts | 1.5 s | asserted contradiction not reproduced |
| 50 | 18-surface policy inventory | 2.0 s | 18 exact paths |
| 51 | family-summary/WHAT-IS-PROVED excerpts | 1.3 s | semantic inconsistency found |
| 52 | governance-supersession search | 1.6 s | decision sources located |
| 53 | decision-ledger headings | 1.4 s | IDs/statuses inspected |
| 54 | authority/equivalent-requirement search | 1.5 s | no paper A4 mandate |
| 55 | first authority-range formatter | 1.1 s | invalid PowerShell interpolation |
| 56 | corrected authority excerpts | 1.6 s | searched evidence rendered |
| 57 | historical-plan search | 1.7 s | exact old plan located |
| 58 | historical-plan excerpts | 1.2 s | unit-cost rank/select verified |
| 59 | C05 decision search | 1.6 s | source decision located |
| 60 | C05 decision excerpt | 1.1 s | primary rejection plus fallback verified |
| 61 | E1 trust-base search | 2.0 s | no forbidden declaration found |
| 62 | exact historical E1 hygiene scan | 0.203 s | no matches (expected exit 1) |
| 63 | PRELOGIC blob excerpts | 1.4 s | exact receipt proposition read |
| 64 | PRELOGIC pattern/line search | 2.4 s | universal-negative and table located |
| 65 | target roadmap/WDD excerpts | 1.4 s | intra-delta S1 contradiction |
| 66 | target DD excerpts | 1.3 s | supersession wording and receipt |
| 67 | target plan excerpts | 1.5 s | gates/checklist/evidence wording |
| 68 | first FlatPayload path read | 1.2 s | wrong historical path; failed |
| 69 | correct FlatPayload path location | 1.6 s | source found |
| 70 | FlatPayload/RelativeTables excerpts | 1.6 s | live layout dependency verified |
| 71 | audit-branch report inventory | 2.1 s | A04-A08 reports located |
| 72 | audit verdict snippets | 1.9 s | negative/blocked lineage classified |
| 73 | ancestry group for lineage | 0.477 s | code/report ancestry results above |
| 74 | `git ls-tree -r main` paper-source search | 0.202 s | no manuscript source |
| 75 | allocation/padding search | 1.6 s | physical-accounting gap identified |
| 76 | report-path/status check | 1.5 s | authorized report absent; one unrelated untracked file |
| 77 | target key-line enumerator | 5.0 s | exact cited line map |
| 78 | current branch log/status | 1.7 s | descendant/fix identity established |
| 79 | prior audit-report style read | 1.5 s | read-only |
| 80 | target gate-results exact excerpts | 1.2 s | tier/dead-cell/S1 text pinned |
| 81 | policy/WordRAM focused excerpts | 1.9 s | one grep returned exit 1 after producing evidence |
| 82 | target claim-drift object emulation | 39.4 s | 1,484 hits, 1 failure |
| 83 | parent claim-drift object emulation | 29.8 s | 1,472 hits, 0 failures |
| 84 | focused new-results blob scan | 6.7 s | target-only failure localized |
| 85 | whole-delta decision-check emulation | 1.9 s | PASS |
| 86 | six per-commit decision emulations | 3.2 s total | all PASS |
| 87 | cost/S1 final target grep | 1.7 s | false dead-cell claim pinned |
| 88 | B1 definition/decoder excerpts | 1.1 s | all-ones word source pinned |
| 89 | expanded B1 decoder/definition read | 2.4 s | `2^w - 1` arithmetic established |
| 90 | related-work target-wide grep | 0.6 s | candidate claims located |
| 91 | seven related-work source excerpts | 9.3 s total | 1.1-1.5 s each |
| 92 | final plan-line check | 0.8 s | novelty-search admission pinned |
| 93 | create the authorized report with `apply_patch` | 3.8 s | one file created |
| 94 | pre-stage diff/status/scope check | 1.1 s | report plus pre-existing untracked settings file |
| 95 | first exact-path `git add` | 1.0 s | sandbox denied worktree index lock |
| 96 | approved exact-path `git add` retry | 0.3 s | report only staged |
| 97 | staged status/name/check group | 1.0 s | exactly one staged path; whitespace pass |
| 98 | report-only `git commit` | 0.3 s | exactly one file, 628 inserted lines |
| 99 | post-report `claim_drift_scan.ps1 -Strict` | 7.2 s | PASS: 1,496 hits, 0 strict failures |
| 100 | post-report `design_decision_check.ps1 -Strict -Base HEAD~1` | 1.8 s | FAIL: pre-existing untracked `.claude/settings.local.json` classified as code |
| 101 | post-report `git diff --check HEAD^..HEAD` | 0.9 s | PASS |
| 102 | read design-check implementation after failure | 0.3 s | confirmed it unconditionally adds all untracked files |

The primary-source web reads used for the related-work check are linked in the
P2 finding; the web tool did not expose wall-clock timings. `lake build` was not
run: no proof/source path changed, and the only requested unmerged-theorem check
was discharged by exact-object source expansion and hygiene. The attempted
narrow elaboration and its limitation are recorded above.

### Post-report final-tree certification

After the report commit existed, the strict claim scan passed with 1,496
classified hits and zero strict failures (7.2 s), and
`git diff --check HEAD^..HEAD` passed (0.9 s). The exact strict design command
did not certify the checkout: it included the pre-existing untracked
`.claude/settings.local.json`, classified that JavaScript-extension path as a
code change, and demanded a design-decision update (1.8 s). Inspection of
`scripts/design_decision_check.ps1:68-98` confirms that even with an explicit
base the checker unconditionally appends every untracked file from
`git ls-files --others --exclude-standard`.

The report commit itself changes exactly one neutral-evidence path, and the
same checker’s exact whole-delta/per-commit object emulations passed earlier.
I did not delete, move, read, ignore, stage, or commit the unrelated settings
file merely to manufacture a green checkout result. Therefore the honest
post-report outcomes are: claim drift PASS, whitespace PASS, exact worktree
design check FAIL for pre-existing unrelated untracked state.

## Required corrections

1. Replace the public decharging sentence with the exact trace-length rule:
   canonical non-emission does not make the compatibility constructors free.
2. Qualify the controller inventory as documentary boundedness and make the two
   public enumerations match.
3. Correct `DD-20260725-006`’s base-contradiction account and replace its
   parent-only strict-scan receipt with the final-target result.
4. Rewrite the `210` lineage and G9 labels to acknowledge the scoped M1
   fresh-blind positive verdict while distinguishing it from a whole-release
   audit; pin all code and report hashes.
5. Remove the false dead-cell blocker; label the shape-dependence witness
   pending and probe (b) as branch arithmetic.
6. Replace the S1 rung’s refuted decoder/uniform-width blocker with the actual
   descriptor/offset obstruction.
7. Narrow the derived-text precedence rule to fidelity artifacts with no later
   ratified amendment; replace “structurally unreachable” with the exact
   contract-admissible/unresolved status; identify the historical proposed
   decision source.
8. Correct `DD-20260725-004` to say the rank/select route was rejected as the
   primary route but retained as a fallback until this supersession.
9. Restore the plan’s three-session E1 gate or record an explicit owner
   amendment.
10. Mark the literature universal and cross-model superiority language as
    search-bounded; narrow the `o(n)` novelty statement.
11. Add physical allocation/capacity and valid-query probe
    totality/accounting to the existing checklist acceptance clauses.
12. Refresh the plan header and exact collision identifier, then rerun all
    strict checks on the resulting final tree.

## Best next target and recommendation

The single best next target is a correction commit that makes this endgame
governance delta internally and mechanically true before any further runway
work is scheduled. It should implement the twelve corrections above and then
receive a fresh final-tree audit of the same base-to-corrected-target range.

**Recommendation: REJECT.**

This report is an auditor recommendation only. It does not change project
disposition, merge status, branch status, or roadmap authority.
