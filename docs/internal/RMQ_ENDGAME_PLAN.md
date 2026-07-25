# RMQ Endgame Plan

Prepared: 2026-07-25 by C06, ratifying-owner review pending. Runway: ~4 weeks
to `V1` (independent verification and submission freeze).

**Supersedes** `docs/RMQ_UNIMPEACHABLE_COST_PLAN.md` (sole commit `2562684`,
2026-07-07, unmerged branch `docs/unimpeachable-rmq-plan`). The original is
archived verbatim at that ref and must not be edited. What survives it
unchanged: the operational definition of "unimpeachable" (referees
pattern-match, not audit), the executable-evidence centerpiece, the
machine-as-strengthening-layer structure, and the model/wall-clock firewall.
What forces supersession: its A3 ISA sketch ("word rank/select primitives" as
unit-cost instruction kinds) is the cost model the owner personally rejected
in `DD-20260717-C05-001` as "exactly the precedent-free justification the
project goal minimizes"; its 7-week two-lane schedule predates the fork, M1,
and all of ARCH2; and it sits on a branch two independent research passes
failed to find. Supporting research: `E1_ARCH_STRATEGY_MEMO_2026-07-25.md`
(31-agent verified corpus). Where that memo's S5 recommendation and this plan
differ, this plan governs: the owner's review found S5 under-weighted the
gap-closure obligations, and this plan repairs that.

## 0. Prime directive

**Every remaining week buys a named gap closed by a kernel theorem, or buys
the recorded proof that closing it was not reachable in the runway. Disclosure
is a stopgap while closure is in flight — never the deliverable.** A hedge is
a debt note, not a payment. Concretely: no workstream below is allowed to
terminate in "disclosed and shrugged"; each has an acceptance form (a theorem
shape) and a fallback whose text must be written the week the gate fails, not
at the freeze.

## 1. The one-object principle

The paper's core promise is about **one counted object**: `2n + o(n)` bits
suffice — meaning the space theorem counts it, the query reads it, and the
query's control information decodes from it. Today those are three different
objects joined by prose:

- the space bound is stated over the raw bit-list `buildPayload : List Bool`;
- the charged query executes against a word-addressed supplied store, and the
  flattening between them (`flattenPayloadWords`) is **not proven invertible**
  (roadmap S1: words carry only `length ≤ reviewerWordBits`, no uniform-width
  equality);
- the geometry steering the query (segment offsets, lengths — including
  data-dependent values like `sparseFlagLen = min(localCount, N)` at
  descriptor cells 34–44) enters as spec-side advice the executable path never
  reads from counted cells.

Four reviewer-facing surfaces currently disclaim the first gap
(`PAPER_MODEL_ADEQUACY.md:95`, `artifact/CLAIMS.md:26,148`, `README.md:367`).
The second gap concealed three real internal errors until B2 R3 kernel-refuted
the project's own frozen geometry clauses (G06, G10/G12, G14). These are not
presentation blemishes; they are the substantive remainder of the theorem, and
closing them is what this plan is for.

## 2. Gap register

Ranked by load-bearing-ness for the paper claim. Each entry: the gap, the
closing instrument(s) cheapest-first, the acceptance form, and the fallback.

### G1 — Space-object/query-object identity (roadmap S1, now unblocked)

The `2n + o(n)` object and the queried object are not the same Lean object.
**S1's stated prerequisite was M1, and M1 is closed and integrated — S1 is
unblocked today.** It is also not unexplored:
`BPCloseRMQNavigationDirectory.queryEncodedCosted`
(`RMQ/Core/SuccinctSpace/BPCloseRMQNavigation.lean:72`) already takes a
`List Bool` payload with an exactness theorem and an encoded `2n + o(n)`
profile at the family layer. The open work is the lift to the canonical
charged route: a uniform-width/chunking decoder plus the supplied-store
transfer lemma M1 made primary.

- Instruments: (i) direct S1 lift (one scoped worker round to size it; new
  construction is the decoder, not the query); (ii) reconciliation with the
  ARCH2 B1 image — B1's accepted package (commit `1727de1`) is an all-size
  counted image with **padded payload cells at one query-independent width**,
  i.e. exactly the uniform-width substrate S1 says does not exist on main.
  If (i) stalls, (ii) is the same theorem from the other end.
- Acceptance form: the canonical charged query stated against (a decoding of)
  the exact object the space theorem counts, with the existing cost constant
  preserved (the 210 theorem charges a logical read algebra in which payload
  length does not appear — a storage refinement can preserve it; verify, do
  not assume).
- Fallback if the gate fails: the four disclaimers stay, plus a committed
  obstruction note stating exactly which decoder theorem failed and why.

### G2 — Descriptor sufficiency (the o(n) bits must provably carry the geometry)

The o(n) descriptor exists to encode layout; nothing kernel-checked says the
layout the query uses is recoverable from it. B2 R3's triple refutation is the
proof this gap hides real errors.

- Instruments: (i) **B2DESC acceptance** — the corrected contract
  (`E1_ARCH2_CONTRACT_REPAIR_PREP.md` §5: G06 `N/b`, G10/G12 constant-1 with
  exact declaration cites, G14 alias/length split) is transcription-ready;
  the R4 worker round is simultaneously the closing instrument and the size
  probe, since no committed estimate exists. Acceptance form: every geometry
  value steering the route is loaded from counted descriptor cells by charged
  reads and proved equal to the canonical value, with the R1/R2/R3 named
  regressions wired into its replay. (ii) The full counted-image route (G4)
  subsumes this.
- Framing note (precedent-shaped): this certificate is the mechanized form of
  the standard succinct-index redundancy argument — "the advice is computable
  from the counted bits" — and should be written up in that vocabulary.
- Fallback: none acceptable short of a committed obstruction; this is the
  gap a hostile reviewer can already argue from our own records.

### G3 — The finished machine theorem, published at its honest granularity

`amendedFamiliarMachineTarget_holds` at `648e512` is kernel-complete for its
own contract (5,646-instruction familiar machine, six-category instruction
charging, read-count = modeled cost as kernel equality, answer agreement, no
sorry/axiom/native_decide) and has never been merged or externally audited.
Publishing a finished theorem is not hedging; the *caveat* (shape-derived
logical store, geometry as advice) is the hedge, and it is interim by
construction because G1/G2 are being closed in the same runway.

- Instrument: dry-run the merge in a scratch worktree (**gate: ≤ 3 sessions**,
  else defer to appendix prose and do not let it consume the runway); then
  the real merge (known collisions: 328/352, 207→210 cost spine — M1's
  five-round migration is the calibration), then the prepared fresh-blind
  audit at base `8e7e3ee`.
- Wording bound (fixed by accepted PREHIST and not negotiable until G4
  lands): "a fully charged familiar machine over the canonical logical store;
  geometry disclosed as model input" — never "word-RAM execution," never "the
  counted image."

### G4 — The counted-image machine route (B3 continuation; the unification)

B3-on-the-B1-image closes G1+G2+G3 in one object and is the genuinely
unprecedented result. Three rounds are banked (obstruction→monus; arithmetic
expressibility; operational block correspondence `B3-HIST-17`). Remaining:
ROM instance/codec, physical read lowering, width invariant, 5-phase
stuttering simulation, receipt, verdict, 42-case campaign — ~6–12 focused
engineer-days by the committed record, against a 4–8× calibration miss on the
one prior novel item.

- Instrument: run the two half-day probes **first and immediately** (they are
  the highest-information steps, not gates on whether to bother):
  (a) interior-geometry literal provenance — the five interior families have
  no established B1 descriptor slots; a bad answer here reopens architecture
  at owner level and must surface in week 1, not week 3; (b) the tiny-size
  width floor (`151 < 2^w`; ROM PCs/branch targets ≥ 5,644 vs
  `log2(envelope)+1` at the smallest sizes).
- Status: strengthening, not V1-gating — but per the prime directive it is
  scheduled work while capacity exists, not a someday item. If both probes
  pass and G1/G2 land by mid-runway, B3 R4 launches.
- Fallback: honest closure prose banking the three durable decisions, plus
  the probes' results as committed notes either way.

### G5 — Constants and envelope honesty (no silent classical-parity implication)

Committed facts (`rmq-on-overhead-gap` record, corrected 2026-07-20): the
overhead envelope admits `Θ(n / log log n)`; Fischer–Heun is
`O(n lg lg n / lg n)`; the envelope is **not proved tight** and no reachable
family is known to attain it; "exactly 2n" is true of the BP core only; **no
construction-time or construction-workspace theorem exists at all**.

Verified component shapes (`RMQ/Core/SuccinctSpace/Asymptotics.lean`), because
the envelope's *shape* determines how much of this matters:

- `idDivLogLogOverhead slots n = slots * (n / (log₂(log₂ n + 1) + 1))` —
  Θ(n / log log n), instantiated at **512 slots** for the sparse-exception
  relative table (`GenericSelect/RelativeTables.lean:1193`);
- `logLogCubedSampledDirectoryOverhead slots n =
  slots * (n / (log₂ n + 1)) * (log log n + 1)³` — Θ(n (log log n)³ / log n).

Against Fischer–Heun's O(n log log n / log n): the second family is worse by
(log log n)², the first by ~log n / (log log n)². The `littleO` theorem is
real and machine-checked; the bound is genuinely sublinear.

**The sharper issue is not tightness — it is the crossover.** At n = 2²⁰ the
512-slot term alone contributes ≈ 512·n/5 ≈ 102n, and the logLogCubed terms
add multiples of ≈ 5.95·slots·n. The proved envelope exceeds n by orders of
magnitude at every instantiable size; it becomes sublinear only at
astronomically large n (consistent with the recorded `n < 2^96` zero-range
threshold). A reviewer who instantiates the bound will ask "in what sense is
this succinct?", and "asymptotically, and that is what is machine-checked" is
technically correct but is exactly the brainpower tax this project minimizes.

Non-tightness, by contrast, deserves little worry and mildly helps: an upper
bound is an upper bound, nobody proves their own space bound tight, and the
slack (visible in the crude `≤ 19906·n + 561` proof step at
`SuccinctFinal.lean:1240`) means nobody can assert the structure *is* that
large — only that we have not proved it smaller.

- Instruments: (i) prose discipline — never "classical parity"; state up front
  that the dominant term is Θ(n / log log n), asymptotically weaker than
  Fischer–Heun, and that the bound is asymptotic with no practical-size
  crossover; scope "exactly 2n" to the BP core; disclose construction cost as
  explicit non-scope in all four claim surfaces; (ii) **measured overhead**
  via the harness — see G6, the highest-value cheap action here; (iii) the
  zero-range/piecewise theorem (`n < 2^96`) if U-lane capacity exists;
  (iv) *optional strengthener, only after G1/G2*: a construction
  read/write-count theorem — genuinely basic relative to classical
  implementations and currently absent, but new territory and not
  runway-gating.
- Acceptance form for (i): claim-drift rules updated so the forbidden
  phrasings are policed, not merely avoided.
- **Explicitly not in scope:** proving the envelope tight, or redesigning to
  shrink it. The corrected 2026-07-20 record gates redesign behind first
  exhibiting a reachable Cartesian/BP family attaining Θ(n / log log n); no
  such family is known, and that question is out of runway.

### G6 — Executable evidence at scale (the original centerpiece, unfinished)

`rmq_succinct_classic_cost_harness` exists with theorem-equal Array-backed
prepared mirrors, but only at fixture sizes 64–128 against the plan's
`n ≥ 2^15` goal, and Linux CI timings/DOI wiring from the original Workstream
C4 are absent.

- Instrument: pure engineering on existing theorem-equal mirrors — extend
  fixtures/generators to `2^15` (target `10^5–10^6`), assert the fast-regime
  and all-size caps differentially, print model-cost vs wall-clock in
  separate columns, record CI timings.
- **Measured-overhead column (serves G5, added 2026-07-25).** Report actual
  `(buildPayload xs).length` against `2 * n` across the fixture ladder, i.e.
  the real auxiliary overhead as a fraction of the payload, beside the
  model-cost and wall-clock columns under the same firewall discipline.
  `buildPayload` is executable and the quantity is directly computable, so
  this carries zero proof risk. Rationale: the proved envelope is loose and
  vacuous at practical n (G5); the actual structure is very likely far
  smaller, and *measuring* it converts the weakest-looking part of the space
  claim into demonstrated evidence — "proved o(n); measured auxiliary
  overhead at n = 2¹⁵ is X% of the payload" is a categorically different
  reviewer experience from an unaccompanied asymptotic bound carrying
  512-slot constants. This is what the superseded plan's Workstream B1 was
  reaching for when it asked to make the uniform constant "presentable".
  If the measurement comes back large, we learn it before the freeze rather
  than after, and G5's prose absorbs it honestly.
- Acceptance form: committed harness run in CI with stored logs; no new
  trust surface (no `native_decide`, no `implemented_by`).

### G7 — Precedent surface and the manuscript

- **The novelty search has never been performed** (open since the original
  plan's C1; any "first mechanized asymptotic o(n)" wording is exposure until
  it is). Protocol per the original plan: AFP + Coq/Rocq package index + Lean
  libraries + ITP/CPP/JAR/JFP back catalogs + the Affeldt lineage, with a
  written per-venue log.
- Related work with real citations, updated by this campaign's verified
  findings: Charguéraud–Pottier level taxonomy (self-classify), Haslbeck–
  Lammich ESOP 2021 (the hedged Level-2 ceiling), **Tockman et al. CPP 2026**
  (Bedrock2/RISC-V — the new ISA-level precedent; scope our machine claims
  against it), Liu–Yu STOC 2020 (cell-probe lower bounds for this exact
  problem — the model our charged-read count pattern-matches), Affeldt et al.
  (prior succinct mechanization; our delta is the machine-checked *asymptotic*
  o(n) and the charged execution story).
- Headline wording, verified defensible form: the story "mechanizes
  **strictly more** of the between-events boundedness step than the published
  ceiling" — not "fully mechanizes."

### G8 — The manuscript does not exist

Verified 2026-07-25: **there is no paper source anywhere on `main`** — no
`.tex`, no `.bib`, no `paper/` or `manuscript/` directory. What exists is the
claim-and-correspondence apparatus (`docs/PAPER_MAIN_THEOREM.md`,
`PAPER_CLAIM_CORRESPONDENCE.md`, `PAPER_THEOREM_MAP.md`,
`PAPER_MODEL_ADEQUACY.md`, `PAPER_RELATED_WORK.md`,
`RELATED_WORK_AND_LIMITATIONS.md`, `WHAT_IS_PROVED.md`, `artifact/CLAIMS.md`)
— excellent raw material, and deliberately maintained, but not a submission.
The superseded plan carried this as Workstream C3 and it was never started.

An "endgame" that ends with a perfect artifact and no paper is not an endgame.
Flagged prominently because every other gap in this register is about
*strengthening* a claim, while this one is about *making the claim at all*.

- Instrument: assemble the manuscript from the existing correspondence
  documents, which were written to be assembled — ITP/CPP submission shape:
  the two-sided theorem plus the executable-cost story as co-headline, the
  ADD process as a methods section, `artifact/CLAIMS.md` as the claim-map
  appendix. This is a writing task, not a research task, and it is the one
  workstream that can proceed in parallel with every proof round.
- Acceptance form: a complete draft whose every claim resolves through
  `PAPER_CLAIM_CORRESPONDENCE.md` to a named Lean theorem at the release
  commit, with venue chosen and length conformed.
- Dependency note: G5/G7 wording and G1/G2 outcomes land *into* the draft;
  the draft should be written to absorb them, not started after them.

### G9 — Evidence consolidation: the artifact must be self-contained on `main`

The release commit is the artifact. Several acceptance records that the claim
chain depends on are **not on `main`** and exist only on branches — verified:
`docs/internal/audit_reports/` on `main` holds A01, A02, A03, A04, A08, the
M1 fresh-blind, and the three C06 E1 reports, but **A05 (U3 blind
acceptance), A06 (U3 docs clean reset), and A07 (Option B charged route) are
absent**, while their branches exist. The roadmap itself records that the A05
report commit "was read directly and was not merged."

Relatedly, **U3 — the principled all-size cost bound giving the `210`
decomposition, one of the paper's two headline numbers — is recorded as
candidate-complete with its fresh blind exact-commit audit still owed and
coordinator-owned.** Its Lean landed; its independent acceptance did not.

- Instruments: (i) inventory every branch carrying accepted-but-unmerged
  evidence, and land the audit reports and acceptance records on `main`;
  (ii) settle U3's audit — either by a dedicated fresh blind audit or by
  scoping it explicitly into V1's release-commit audit, recorded either way;
  (iii) resolve the accumulated ledger hygiene the campaign generated
  (duplicate `DD-20260723-001` / `WDD-20260723-001` across lineages, the
  stale 207-era matrix header, the `_MATRIX.md` classifier deadlock).
- Acceptance form: a reviewer at the release commit can reconstruct every
  public claim's acceptance chain without visiting a branch.
- Why this is a gap and not bookkeeping: the project's whole evidentiary
  posture is "reconstruct from Git." Evidence reachable only from an unmerged
  branch is, for the artifact, evidence that does not exist.

## 3. Sequencing (4 weeks, Friday gates)

**The manuscript lane (G8) runs continuously from week 1 and is never
displaced by a proof round.** It is the only workstream whose absence makes
every other success unpublishable, and it absorbs outcomes rather than
waiting on them.

**Week 1 — every unknown gets touched.**
S1-lift scoping round (G1-i) and B2DESC R4 (G2-i) launch as the two primary
worker rounds; B3's two probes run as half-days (G4); the 648e512 dry-run
merge runs in a scratch worktree (G3 gate); one coordinator day executes the
governance packet (§4), the G5 prose fixes, and the G9 evidence inventory;
manuscript skeleton assembled from the correspondence docs (G8). *Friday
gate:* each of G1/G2 has either a live candidate or a sized obstruction;
probes have answers; dry-run has a session count; G9 inventory is complete
with a landing plan.

**Week 2 — first closures land.**
S1 and B2DESC to acceptance/audit as they terminate; 648e512 real merge if the
dry-run gate passed, blind audit launched behind it; G6 harness scale-up
including the measured-overhead column (engineering lane, no proof risk); G9
audit reports and acceptance records land on `main`; U3's audit disposition
settled. *Friday gate:* at least one of G1/G2 closed or its obstruction
committed; audit in flight; `main` self-contained for all pre-existing claims.

**Week 3 — composition and the optional ascent.**
Compose landed closures into the claim surfaces (the four disclaimers shrink
or fall); B3 R4 launches iff both probes passed and G1 or G2 is closed;
novelty search executes (G7) and its log lands; manuscript to complete draft.
*Friday gate:* claim surfaces consistent with exactly what is proved; every
manuscript claim resolves to a named theorem; B3 either running with a scoped
contract or closed with banked assets.

**Week 4 — V1 freeze.**
Per the roadmap V1 rung: pinned-version Linux CI with stored logs, advisory
independent checker (`nanoda`), axiom/hygiene gates across all nine
axiom-check scripts, theorem-correspondence/claims/related-work/novelty-log
freeze, DOI-ready (Zenodo) and if needed anonymized artifact bundle, and the
fresh blind external audit of the exact release commit — scoped to cover U3's
outstanding audit if G9 routed it there. Nothing new lands in week 4 except
audit-fix loops and manuscript polish.

Throughput realities baked in: ~25 min per protected-main CI cycle; one heavy
Lean process at a time; few deep worker rounds beat many shallow ones; every
merge to main stages on a branch and fast-forwards after green.

## 4. Governance packet (one coordinator day, week 1)

One owner DD covering, in the procedure's own vocabulary:

1. supersession of `RMQ_UNIMPEACHABLE_COST_PLAN.md` by this plan, original
   archived verbatim at `2562684`;
2. supersession of the A4 selection-before-publication ordering; B2-full and
   B4 recorded `UNRESOLVED`-and-unpursued (deliberate, reversible); B2DESC
   explicitly carved out as live (it serves G2, not the selector);
3. disposition of DD-20260722-003 (adopt or reject — it has never been
   accepted) and of the handoff-vs-PRELOGIC selector contradiction, including
   whether the owner now records the general
   frozen-text-yields-to-accepted-input rule on this arguable fourth
   instance;
4. roadmap amendments: S1 status deferred→**active** (prerequisite M1 is
   closed); E1 rung wording updated to the post-fork reality; the stale
   207-era matrix header reconciled;
5. the ACCEPTED-authority question (who may record acceptance on this
   runtime) — resolved or explicitly deferred with its interim rule restated.

## 5. Non-goals for this runway

Full B2 current-route implementation (exceeds runway at its verified lower
bound); running A4; construction-cost theorems as V1 gates; external C/Rust
generation; any redesign chasing envelope tightness without the reachable
family the corrected record demands first; the **A1 refactor** (roadmap
rung, "partially begun" — cosmetic module surgery is the worst possible use
of a submission runway and risks destabilizing proven interfaces); editing
archived evidence documents in place.

## 6. Publication-readiness checklist

The plan is complete iff, at the release commit, a reviewer finds all of:

| # | Item | Gap | State today |
|---|---|---|---|
| 1 | A manuscript whose every claim resolves to a named Lean theorem | G8 | **absent — no paper source exists** |
| 2 | Space/query object identity, or a committed obstruction | G1 | disclaimed on four surfaces |
| 3 | Descriptor sufficiency certificate, or a committed obstruction | G2 | not attempted |
| 4 | Machine theorem published at its honest granularity | G3 | kernel-complete, unmerged, unaudited |
| 5 | Counted-image route, or banked assets + probe results | G4 | 3 rounds banked, probes unrun |
| 6 | Envelope/constants prose with no parity implication | G5 | wording live, crossover undisclosed |
| 7 | Measured overhead and cost at `n ≥ 2^15` in CI | G6 | harness exists at 64–128 |
| 8 | Novelty search log and real citations | G7 | **never performed** |
| 9 | Every acceptance chain reconstructible from `main` | G9 | A05/A06/A07 off-main; U3 audit owed |
| 10 | LICENSE, artifact guide, `CODE_MAP`, reproduction script | — | present ✓ |
| 11 | Pinned Linux CI, axiom/hygiene gates, `nanoda`, DOI bundle | V1 | CI ✓; DOI/checker pending |
| 12 | Fresh blind external audit of the exact release commit | V1 | pending |

Best case: rows 1–12 all green — the one-object story closed at cell-probe
granularity, the machine companion merged and audited, B3 landed or honestly
banked, measured scale evidence, precedent-anchored prose, a submitted paper.
Worst case this plan still permits: today's headline with corrected wording,
the machine companion, a complete manuscript, and **committed obstruction
records for G1/G2 stating exactly what failed** — because the one outcome
forbidden here is reaching the freeze to discover the gaps were never
seriously attempted, or that there was no paper.
