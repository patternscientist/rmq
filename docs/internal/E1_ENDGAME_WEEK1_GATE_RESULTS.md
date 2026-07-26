# Endgame week-1 gate results

Prepared: 2026-07-25 by C06. Source: a 10-agent campaign (5 investigators, 4
adversarial checkers on the two launch-gating verdicts, 1 synthesis) run
against the ratified plan `RMQ_ENDGAME_PLAN.md`. Corrections applied by the
checkers are incorporated; where a primary verdict was corrected, the
correction governs. Evidence tiers: (a) kernel-checked Lean at an exact
commit, (b) committed prose, (c) research narrative. **Nothing here is an
acceptance.**

## 0. The finding that changes the release picture

**The `210` headline cost literal has never been accepted by any fresh blind
audit.** The last fresh blind audit to ACCEPT the public RMQ theorem surface
is A04, 2026-07-14, at cost literal **328**. Every step of the migration
`328 → 76 → 207 → 210` carries a REJECT (A05 twice, A06, A07) or `blocked`
(A08) — and **A07's and A08's targets are both ancestors of `main`**, so the
rejected and blocked code shipped while only the accepting verdict stayed
behind at 328.

This reframes gap G9 from paperwork to substance. U3 was not "audit owed"; it
was independently rejected three times. Recommendation (owner decision A6
below): do **not** commission a dedicated U3 audit — it would audit the
retired 76 route and still leave 210 unaccepted. Amend the V1 release-commit
audit prompt to name the 210 public surface and the whole migration, so the
one audit that must happen anyway discharges the chain.

## 1. G1 (S1 space/query-object identity) — LAUNCH_SCOPED as an obstruction round

**The roadmap's stated blocker is wrong in both directions at once**, which is
precisely why the rung looked deferrable: nobody costed the real blocker
because the stated one was unreal.

- It asks for a chunking decoder that **already exists and is kernel-checked**:
  `chunkPayloadWords` (`RMQ/Core/SuccinctSpace/WordStore.lean:154`) with
  `flattenPayloadWords_chunkPayloadWords` (:199), plus the rank bridge
  `chunkPayloadWords_rankPrefix_exact` (`RMQ/Core/SuccinctRank.lean:531`).
- It asks for a uniform-width theorem that is **false, not merely absent**:
  `BoundedPayloadWordStore.ofChunksWithSentinel` (`WordStore.lean:576`)
  appends `List.replicate (payload.length + 1) []` — literally empty words —
  so the physical word list contains ≥ `2n+1` length-0 words. Only the `≤`
  form is provable and only it is proved
  (`...ReviewerPhysicalWord_length_le_wordBits`, `ReviewerPhysical.lean:2078`).

**Checker correction, load-bearing:** the roadmap's operative *conclusion*
nonetheless stands. No theorem of the form
`chunkPayloadWords w (buildPayload xs) = physicalWords` exists or can be true,
because the canonical word list is a 22-source concatenation of stores at
differing word sizes, not a fixed-width chunking. S1 remains new construction,
not composition — the roadmap's reason is wrong, its verdict is right.

**Route B (use B1's padded image) is dead on the crux**, not on cost: B1's
image is a sibling object, not provably the counted bits, and it is
Ω(n log n) against a `2n + o(n)` claim.

**The real blocker.** The canonical layout
(`FlatPayload.lean:1864`) is `bpCode ++ access ++ close ++ fringe ++
selectChunk` with no padding and no descriptor. Three aux components have
exact n-determined lengths and `bpCode.length = 2n`, but the 18-source live
access block has only a `≤` bound (`FlatPayload.lean:1908`) **and sits in the
middle** — so `...CloseBitOffset` (`FlatPayload.lean:1896`) is shape-dependent.
A bit-addressed query given only `buildPayload xs` and `n` cannot locate its
own components. Genuinely shape-dependent, not merely unproved: the
long-relative table's length is proportional to the number of *long*
superblocks, which depends on the bit pattern (`RelativeTables.lean:276`).

The lawful fix — pad each sub-source to an n-determined budget, exactly the
device the **legacy** layout already uses (`accessPadding`/`closePadding`,
`FlatPayload.lean:79-105`, which is why legacy has an exact length theorem and
canonical has only `≤`) — changes `buildPayload` itself: 4-8 sessions on the
highest-blast-radius object in the repo, plus re-audit of the space chain and
the 210 cost spine. **Not a week-1 or week-2 bet.**

Adversarial review found two gifts the primary verdict missed: a *generic*
family bridge (`EncodedPayloadLiveBPCloseRMQNavigationView.toBPCloseRMQNavigationDirectory`,
`BPCloseRMQNavigation.lean:684`) that already demands the equality the payload
lacks — making the obstruction kernel-visible rather than prose — and a much
cheaper padding granularity (one trailing pad, not eighteen).

**Scope:** sized-obstruction round. Deliver (1) the two cheap prefix-sum
lemmas (`reviewerWordBitOffset` + slice/bound pair — list-combinatorial, land
regardless of verdict); (2) the **two-shape `#eval` counterexample** (two
size-n Cartesian shapes, monotone vs bitonic, with different access-block
lengths) — every link is kernel-checked but this witness exists at no commit,
so the status today is honestly "obstruction highly likely, witness pending";
(3) the sized closure estimate. **Build note:** this worktree has no `.lake`,
and the only built checkout is dirty and not a main descendant — budget a
clean build at the target commit.

## 2. G2 (descriptor sufficiency) — LAUNCH_SCOPED, the strongest bet on the board

**G24 evaporates.** The obstruction that stopped B2 R1, shaped R2's entire
residual-equation amendment, and was still R3's named target discharges in two
lines under sufficiency framing: `canonicalLayout shape = layoutOfSize
shape.size` by `rfl`, then rewrite through the charged size cell. Three worker
rounds were spent on a wall that is not there once the constant-time ISA
framing is dropped.

The investigator kernel-checked representatives of **14 of the 25** frozen
geometry rows in one session (~45 min, <25 s elaboration), including G24. The
two rows that could genuinely have obstructed (G11/G13 exception counts) also
came back clean, because `FixedWidthNatTable` stores one word per entry rather
than bit-chunking, so the count divides out exactly. Both places sufficiency
could have failed were cleared **by probe, not by argument**.

**Non-negotiable prerequisite:** launch as a FRESH round under a new id
(`E1-ARCH2-B2SUFF-R1`), off `1e111e5`, **not** as "B2DESC R4". The frozen
B2DESC contract *is* the hard (ii) version; inheriting its obligation or its
sixteen execution fixtures re-imports the G24 wall for a fourth consecutive
round and turns 5 days into 20. Replace "permitted familiar atomic operations"
with "any total Lean function of loaded descriptor values", delete the
atomicity/no-wrap/divisor column and the R3 ISA rows, apply the four §5
corrections, and replace F01-F16 with ~6 geometry-evaluation fixtures.

Effort 4-6 focused engineer-days, of which 1-2 are replay/governance tax —
which *exceeds the proof work*, and is the main scope risk.

**Integration caveat:** the certificate is a statement about
`currentE1SharedRouteInput`, which lives only on the B1 lineage, and B1's
`1727de1` is not an ancestor of `main`. Closing G2 on a branch converts a
proof gap into an integration gap against the plan's own rule that branch-only
evidence does not exist. Decide the landing target before launch.

## 3. G4 (B3 counted-image route) — LAUNCH_SCOPED to path-independent assets only

**Probe (b): CLOSED-PASS, no size floor at any n.** `w(n) = log2(800000(n+1)+50)+1`
bottoms out at **w = 20** (`2^w = 1,048,576`) at n = 0, clearing image
addresses (694), ROM/branch targets (5,646/5,644), the register ceiling (151),
and the encoded-ROM cells simultaneously. The scheduled half-day is
**released**; `INV-ALL-SIZE` is not at risk. Caveat: the pass is purchased by a
loose capacity constant (400000·(n+1)), not by structure — at an honest ~4n+50
capacity the same probe would bind.

**Probe (a): provenance clean — the architecture-reopening fear is
discharged.** Every shape-varying interior geometry value reduces to already-
charged descriptor cells (checker correction: **three** cells — cell 1
`shape.size`, cell 0 physical count, cell 22 segment-20 offset — not one), via
the unconditional `bpCode_length : shape.bpCode.length = 2 * shape.size`
(`Shape.lean:51`). **B1 needs no new counted slots.**

**But probe (a) cleared onto a job ~10× its stated size**, and this is the
correction that matters: the geometry values are consumed as **instruction
immediates** (~69 `mulConst`/`divConst`/`const` sites), so closing it
constructively means re-lowering every one from an instruction operand to a
register operand and re-deriving the interior's position geometry. The
verdict cited the shape-independent `4204` constant as reassurance; that
constant exists *because* the literals are baked in, and the fix destroys it.

**Scope:** launch only path-independent assets needed under every resolution —
the log2/bit-length register block first (eight of fifteen derived values
depend on it, and a wrong `Nat.log2 0`/`Nat.log2 1` boundary invalidates all
of them), then pow2, the ceil-div consumer, and the missing store-size lemma —
with a **named stop condition**: if sizing the re-lowering exceeds one further
round, record unreachability and stop. Do not spend weeks two and three
discovering it. Full B3 R4 closure is not reachable by freeze.

## 4. G9 (evidence consolidation) — LAUNCH unscoped

Docs-only: policy JSON, two regression fixtures, one PowerShell regex, four
`git checkout <ref> -- <path>` adds, one new disposition file. Zero Lean, zero
proof risk, 1-2 sessions.

**Ordering is a hard constraint, not a preference.** A1 first: register one
exact `allowedPathLinePairs` entry for the A05 blind report's line 27 — which
quotes a retired public query alias that the `forbidden-retired-paper-query-alias`
rule bars outside frozen history or enforcement data — plus accept/reject
fixtures in both regression scripts. A directory allowance is **forbidden** —
that is exactly the blanket exemption U3-FH-01/FH-02 removed. Landing the A05
report verbatim fails main's own gates today on exactly one line, caught by
two independent strict enforcers: a thirty-minute fix that is invisible until
attempted, and the reason "just cherry-pick the four reports" is wrong.

**This document demonstrated the hazard on itself.** An earlier revision
spelled that retired alias out while *describing* the allowlist entry needed to
land it, and the strict scan rejected this file for exactly the rule the
sentence was about. Per `rmq-audit-prompt`'s standing guidance, the repair is
to paraphrase the forbidden spelling, never to widen an allowlist to
accommodate one's own prose. The G9 worker should expect the same trap when
writing its disposition file.

Accepted cost: the round puts four REJECT verdicts and one `blocked` onto the
release commit. That is the correct and honest outcome.

## 5. G3 (companion dry-run merge) — HOLD, estimate was wrong

Blocked on identifier collisions outside its ≤3-session estimate: `648e512`
collides with `main` on **seven live decision ids** (`DD-20260719-002`
through `-008`), each a *different* decision on each side, plus three-way
ARCH2 collisions on `DD-20260723-001`, `WDD-20260723-001`, `WDD-20260723-...`.
Re-estimate before committing the lane; the ≤3-session gate in the plan should
be read as covering the merge *after* an id-reconciliation pass, not including
it.

## 6. Owner decisions required

- **A6 — the 210 acceptance chain.** Recommended: amend the V1 release-commit
  audit prompt to name the 210 public surface and the `328 → 76 → 207 → 210`
  migration, rather than commissioning a dedicated U3 audit of a retired
  route. Record the decision or the gap returns at freeze.
- **G4 cost model.** The interior cost surface is stated as bare constants
  (`canonicalRelativeRmmInteriorQueryCost = 264`; principled charged trace
  cost `33`). An O(log n) geometry preamble costing up to `9w+3` per multiply
  and `14w+19` per divide cannot leave those constants unchanged. Decide
  whether the counted-image route may restate them before R4 sizing.
- **G4 dead cell.** B1's dead cell decodes to exactly `2^w`, violating
  `B3-HIST-04`'s strict width bound. Size-independent, not fixed by probe (b).
  Three escapes: prove the dead read unreachable for all shapes/queries (the
  pinned run shows address 693 unread, but that is one run, not
  `ParameterizedComplete`); restate the bound as `≤ 2^w`; or change the dead
  marker. Architecture-bearing; owner call.

## 7. What this cost, and what it bought

Ten agents, ~1.2M tokens. It converted four "launch or not" guesses into four
scoped decisions, released a scheduled half-day, discharged the plan's stated
fear of reopening architecture at owner level, found that the strongest lane's
blocking obstruction is not real, found that the highest-ranked lane's stated
blocker is not real *either* (in the opposite direction), and surfaced the
unaccepted 210 chain — which no amount of proof work would have revealed.
