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

- Instruments: (i) prose discipline — never "classical parity"; state the
  envelope and its non-tightness; scope "exactly 2n"; disclose
  construction-cost as explicit non-scope in all four claim surfaces;
  (ii) the zero-range/piecewise theorem (public-input threshold `n < 2^96`)
  if U-lane capacity exists; (iii) *optional strengthener, only after G1/G2*:
  a construction read/write-count theorem — genuinely basic relative to
  classical implementations and currently absent, but new territory and
  therefore not runway-gating.
- Acceptance form for (i): claim-drift rules updated so the forbidden
  phrasings are policed, not just avoided.

### G6 — Executable evidence at scale (the original centerpiece, unfinished)

`rmq_succinct_classic_cost_harness` exists with theorem-equal Array-backed
prepared mirrors, but only at fixture sizes 64–128 against the plan's
`n ≥ 2^15` goal, and Linux CI timings/DOI wiring from the original Workstream
C4 are absent.

- Instrument: pure engineering on existing theorem-equal mirrors — extend
  fixtures/generators to `2^15` (target `10^5–10^6`), assert the fast-regime
  and all-size caps differentially, print model-cost vs wall-clock in
  separate columns, record CI timings.
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

## 3. Sequencing (4 weeks, Friday gates)

**Week 1 — every unknown gets touched.**
S1-lift scoping round (G1-i) and B2DESC R4 (G2-i) launch as the two primary
worker rounds; B3's two probes run as half-days (G4); the 648e512 dry-run
merge runs in a scratch worktree (G3 gate); one coordinator day executes the
governance packet (§4) and the G5 prose fixes. *Friday gate:* each of G1/G2
has either a live candidate or a sized obstruction; probes have answers;
dry-run has a session count.

**Week 2 — first closures land.**
S1 and B2DESC to acceptance/audit as they terminate; 648e512 real merge if the
dry-run gate passed, blind audit launched behind it; G6 harness scale-up in
parallel (engineering lane, no proof risk). *Friday gate:* at least one of
G1/G2 closed or its obstruction committed; audit in flight.

**Week 3 — composition and the optional ascent.**
Compose landed closures into the claim surfaces (the four disclaimers shrink
or fall); B3 R4 launches iff both probes passed and G1 or G2 is closed;
novelty search executes (G7). *Friday gate:* claim surfaces consistent with
exactly what is proved; B3 either running with a scoped contract or closed
with banked assets.

**Week 4 — V1 freeze.**
Per the roadmap V1 rung: pinned-version Linux CI with stored logs, advisory
independent checker, axiom/hygiene gates, theorem-correspondence/claims/
related-work/novelty-log freeze, DOI-ready artifact, and the fresh blind
external audit of the exact release commit. Nothing new lands in week 4
except audit-fix loops.

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
family the corrected record demands first; editing archived evidence
documents in place.

## 6. What V1 ships under this plan

Best case: the one-object story closed at cell-probe granularity (G1+G2
kernel theorems), the fully charged machine companion merged and blind-
audited (G3), B3 either landed on the counted image (G4) or honestly banked,
scale evidence in CI (G6), precedent-anchored prose with the novelty log
(G5+G7). Worst case that this plan still permits: today's headline with
corrected wording, the machine companion, **plus committed obstruction
records for G1/G2 that state exactly what failed** — because the one outcome
this plan forbids is discovering at the freeze that the gaps were never
seriously attempted.
