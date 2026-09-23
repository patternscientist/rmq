# Coordinator disposition — RMQ program-plan audit

**Date:** 2026-08-13. **Audited artifact:** `RMQ_PROGRAM_PLAN_2026-08-13.md`.
**Auditor verdict:** `NOT_SOUND`. **Coordinator disposition: VERDICT UPHELD.**
**Author of the audited plan:** this coordinator. Every finding below was
independently reproduced against the tagged tree before disposition.

---

## 1. Summary

The auditor examined a program plan spanning four goals and returned
`NOT_SOUND` on a single P0: the plan's first new public claim could be formally
green and substantively empty. That finding is **correct, reproduced, and
decisive**, and it invalidates the acceptance criterion of an entire track.

Nothing in the report was found wrong. One finding is qualified on cost
(`P1-1`); one figure the auditor disputed was resolved **in the auditor's
favour against this project's own fact base**.

This is the third consecutive audit in this program to return a negative
verdict with a 100% valid-finding rate, and the first to audit a *plan* rather
than a candidate. The pattern is stable: the mathematics holds, the *claims
about* the mathematics and the *checks guarding* them do not.

---

## 2. Verification of the auditor's own accuracy

Before dispositioning findings, the auditor's arithmetic was independently
recomputed from the tagged tree.

| quantity | coordinator recomputation | auditor | match |
|---|---|---|---|
| Inclusive `RMQPaper` closure | 204 files / 202,096 lines | 204 / 202,096 | exact |
| Import-graph floor saving | 830 lines = 0.411% | 830 / 0.411% | exact |
| Packed-only reduction | 3.448% files, 1.585% lines | 3.448% / 1.585% | exact |
| Drop-packed reduction | 27.472% | 27.472% | exact |
| Historical citation defect | cited `:9349`, declaration at `:8261–8269` | "approximately reproduces" | confirmed |

**Disputed figure resolved against this project.** The plan's fact base recorded
**24** `ACCEPTED_BASE` ledger rows; the auditor reported **29**.
`grep -c 'Status: ACCEPTED_BASE'` on the tagged ledger returns **29**. The
auditor is right and the plan's own fact base was wrong.

The auditor also correctly identified that the plan's headline closure figure
(203 / 202,083) is the closure of `RMQ/Headlines/RMQ.lean`, *excluding* the
13-line `RMQPaper.lean` wrapper — a wrapper-exclusive count presented as the
paper root's closure.

---

## 3. Findings and dispositions

### `P0-1` — PRE-2 can certify an oracle result with decorative writes

**ACCEPTED. Reproduced. Decisive.**

All three underlying code facts verified at the tag:
- `Costed.pure` has `cost := 0` (`RMQ/Core/Cost.lean:41-44`) — a semantic
  oracle is free.
- `WordRAM.TraceEvent` has **no write constructor**: only `readWord`,
  `wordRank`, `wordSelect`, `syntheticCostOnlyPrimitive`
  (`RMQ/Core/WordRAM.lean:102-108`).
- `TraceResult.ofCosted` builds a trace from a cost *number* with no relation
  to any computation (`RMQ/Core/WordRAM.lean:668-671`).

The plan's two conjuncts — final-store equality, and charged writes = payload
length — are therefore **both satisfiable with zero charged construction**.

**Root cause, stated plainly.** The plan asserted that the `rfl` identity
`packedReviewerPayloadBits = buildPayload` closed the "two-payload trap". It
closes *which payload object is referred to*. It says nothing about *whether an
execution produced it*. Those are different properties, and the plan conflated
them — in the same document that names conflation of this kind as the house
defect.

**Disposition:** the preprocessing track's acceptance criterion is withdrawn.
No PRE implementation may begin until a frozen operational builder contract
exists. Contract design is in progress; its acceptance test is that the
auditor's fake, and stronger ones, are excluded by a *named* obligation.

### `P1-1` — V1 promotes a module-graph floor into a structural floor

**ACCEPTED, with one qualification on cost.**

The distinction is real and the plan blurred it: "no *re-rooting* materially
shrinks the closure" was measured; "no *claim-preserving change* materially
shrinks it" was asserted. The plan then made Core restructuring a **non-goal**,
foreclosing the only untested option, and scheduled a confirmation probe (`N4`,
minimum-imports over existing declarations) that **cannot test restructuring**.

**Qualification.** The auditor's proposed seam — `ReviewerCapstone` importing
the 14,048-line `ReviewerControllerStateProof` while textually using one
declaration from it — is not reachable by refactoring alone. While
`packedReviewerArchitectureCapstone_holds` is exported, its **proof-layer
dependencies can never leave the import closure**. Realising the seam requires
*re-deriving* the needed facts from lower-level modules — new proof work, not
re-plumbing, unless the direct versions already exist in
`ReviewerController`/`ReviewerControllerProof` as the auditor suggests.

**Disposition:** accepted. DD-A becomes conditional on a scratch feasibility
port with an exact-type check and a closure measurement; the non-goal on Core
restructuring is lifted for that probe only. The plan may not record
"minimization exhausted" as governance until the probe reports.

### `P1-2` — G2 starts from a false E1 acceptance state

**ACCEPTED. Reproduced.**

On branch tip `648e512`: `grep -c 'NOT SATISFIED'` = 1 and `grep -c 'SATISFIED'`
= 9 (inclusive of that one), giving **8 SATISFIED / 2 PARTIAL / 1 NOT
SATISFIED**, not the 9/2 the plan recorded. The unsatisfied row is
**`REQ-E1-09`** — the machine-level discharge of the documentary
uncharged-omissions list.

**Aggravating detail:** `REQ-E1-09` *was* present as a work item in the source
design this plan synthesized. **The synthesis dropped it while compressing.**
The defect was introduced by the plan's author, not inherited.

The consequence the auditor draws is the serious part: closing only the two
advertised PARTIAL rows would let a new E1 ledger row coexist with `L-OPEN-06`
and the manuscript non-claims, so the paper would simultaneously assert that an
instruction machine exists and that none does — with every declaration check
green.

**Disposition:** accepted in full. G2 gains an all-row adjudication phase
covering all 11 REQ rows, inherited INV rows, CHK rows, `REQ-E1-09`,
`L-OPEN-06`, the evidence matrix, and every current-fact surface, disposed
atomically.

### `P1-3` — "one logical protocol, two refinements" is not established

**ACCEPTED. The sharpest finding in the report.**

The plan's narrative verdict V-C claimed the packed machine and the E1 machine
are refinements of "the identical accepted 210-fuel logical route". This is in
direct tension with a property the project ships and enforces:
`scripts/independence_check.lean` proves the two `210`s are **independent** at
declaration and proof-term level. Shared low-level imports and a coinciding
numeral are not a refinement theorem.

This is the *same conflation* the `L-ARCH-01` amendment retired in the RC-2
correction round — reintroduced in a narrative intended for the manuscript.

**Disposition:** accepted. The phrase is retired. Replacement: *"two
independent operational refinements connected to the same public RMQ
semantics."* "One protocol" may be used only after an explicit checked join
theorem exists, and any such theorem must be reconciled with
`independence_check` before it is written.

### `P1-4` — post-V1 E1 paper integration is not covered by the planned audit

**ACCEPTED.**

G2's public landing edits the manuscript, the ledger, current-fact surfaces and
the base pin. That is a new release surface, and V1's own policy requires a
fresh audit of the exact release commit including manuscript/ledger and
artifact-root correspondence. The plan scheduled only an E1-rung audit.

**Disposition:** accepted. E1 either stays strictly supplementary and outside
the accepted manuscript/ledger, or its public landing is treated as a new
release candidate requiring the full release audit. The choice is an owner
decision and is added to the DD packet.

### `P1-5` — PRE-1's linear shape proof is impossible for the named implementation

**ACCEPTED. Reproduced from source.**

`insertRightStack tree value = insertRightStackLoop value tree []`
(`RMQ/Core/Shape.lean:675-677`) — an **empty frame list on every insertion**.
`insertRightStackLoop` walks the right spine from the root, pushing frames, and
`plugRight` rebuilds the ancestors it walked. `buildTreeAux` calls it per
element (`:897`). On strictly increasing input, insertion *k* traverses *k*
nodes: Θ(n²).

The plan scheduled "amortized with `Amortized.Bound` (potential = right-spine
length; push/pop once each)". That potential argument is valid for a monotone
stack **persisting across insertions**; this stack is local to one insertion and
discarded. The scheduled proof does not exist for this implementation.

**Disposition:** accepted. The shape lane is respecified: implement a
persistent monotone-stack scan or a direct shape emitter, and prove value
agreement with the canonical shape. Charging the existing builder is
prohibited — it would either be quadratic or hide traversal behind decree ticks.

### `P1-6` — "four S1 surfaces" is the requested house defect

**ACCEPTED, with attribution corrected.**

The count is not the plan's invention: `RMQ_FINAL_ROADMAP.md` states verbatim
that "Four reviewer-facing surfaces currently disclaim this capability". The
plan inherited it uncritically. The auditor's enumeration of at least nine
registered current-fact surfaces carrying the boundary means the **roadmap's own
number is stale**, and a sync check pinned to four would pass while five or more
surfaces went stale — the exact failure mode.

**Disposition:** accepted, and the finding is escalated to the roadmap itself.
The inventory is derived from `CLAIM_DRIFT_POLICY.json` at the pinned commit
with a per-path disposition; no fixed count is pinned anywhere.

### `P1-7` — naming an `Int`-honesty hypothesis permits a vacuous theorem

**ACCEPTED.**

A named hypothesis constrains nothing: instantiated `True` it grants no
representability; instantiated `False` it discharges every conditional theorem
by contradiction. The plan's "named hypothesis in the theorem and the ledger
row" was a labelling discipline masquerading as a semantic one.

**Disposition:** accepted. The predicate must require signed-word
representability of every input and every compared operand at the declared
width, with a comparison/order refinement theorem and an exhibited satisfiable
all-size input family. Absent that, the model is called a unit-cost comparison
oracle in public wording.

### `P1-8` — the proposed E1 root checks can pass while checking the wrong root

**ACCEPTED. Reproduced.**

`ledger_decl_check` imports broad `RMQ` plus multiple roots, so an E1
declaration resolves even if `RMQE1` exports nothing — a root-export check that
cannot fail on an empty root. Separately verified: the branch defines
`[[lean_exe]] name = "rmq_e1_machine_validate"` (root
`RMQ.Validation.E1MachineValidate`). The plan proposed adding
`lean_exe e1_validator`, **renaming a frozen public executable identity**.

**Disposition:** accepted. Any new root check must import *only* that root and
carry an exact declaration inventory, a count floor, a deletion mutation and an
anti-empty control. The frozen executable name is preserved; an alias may be
added, never a rename. Packet manifest and the operational-surface list are
enumerated explicitly rather than counted.

### `P2-1` — metrics repeatedly change measurement universe

**ACCEPTED. Partially self-identified before the audit.**

The coordinator had already reconciled the blank/non-blank and
wrapper-inclusive/exclusive discrepancies. The auditor adds two the coordinator
missed: "3%" is a **file** percentage quoted beside line percentages, and
"204 not 317" compares new imported dependencies against the current check's
inclusive closure.

**Disposition:** accepted. One committed script emits separately named fields —
root-inclusive files, imported dependencies, physical lines, non-blank lines —
with wrapper, off-by-one and blank-line mutation controls. No percentage is
quoted without its unit.

### `P2-2` — V4's conclusion is too broad

**ACCEPTED.**

The `rfl` identity is exact but covers the **payload list only**. Queries
consume a logical segmented store, a physical word/read store, and the packed
header-plus-padding-plus-chunk memory; existing M1 and packed lowering theorems
bridge these separately. "One costed builder serves the space theorem and the
packed capstone" overreached. The auditor further notes "charged writes =
payload bit length" is dimensionally wrong: word writes, duplicates,
overwrites and one-bit writes can all satisfy it.

**Disposition:** accepted. Wording becomes "one shared payload sub-builder".
Physical-store emission and packed memory construction are separately costed and
joined, with write units stated (bits counted in bits, or words counted in words
with an exact concatenated-bit-length and address/value replay).

### `P2-3` — workspace and close-lane forecasts precede their measures

**ACCEPTED.** Five wrappers vs eight encoded tables; a `RightSpineFrame`
carries a whole subtree plus an unbounded `Int`, so the forecast `≤ 2n` bits has
no basis before the representation and measure are fixed.

**Disposition:** accepted. Report five wrappers / eight encoded tables. The `2n`
forecast is removed until DD-E fixes the representation, encoding and
peak-live-state measure and an encoding bound is proved.

### `P2-4` — effort and calendar gates are unsupported and internally inconsistent

**ACCEPTED, and one internal contradiction is conceded outright:** G2 is
estimated at 9–13 worker sessions but gated on a six-session runway threshold.

The ITP finding is material. The auditor reports the official series page still
identifies **ITP 2026** as next, and found only a **call for bids** for 2027 —
no 2027 CFP. The February deadline and anonymised-supplement requirement in the
plan are therefore inherited from the **2026** call. This also puts this
project's own memory ("ITP 2026 has passed; target ITP 2027") in question.

**Disposition:** accepted. All session figures are relabelled planning
hypotheses. The E1 gate uses the upper estimate plus audit buffer. Calendar
gates update only from an official 2027 CFP; the venue question is escalated to
the owner. Building the anonymised bundle proceeds regardless — it is prudent
under either venue.

### `P3-1` — governance wording imprecise across conflicting surfaces

**ACCEPTED.** "Zero-paper-facing" becomes "no positive paper claim" (E1 is
already tracked as a public non-claim via `L-OPEN-06`). "Zero proof
obligations" between S1 and PRE becomes "neither discharges the other".
`M1 → S1` is retained explicitly as a deferred non-gating edge. Both roadmaps
and the packet manifest are synchronized — the packet currently ships the stale
DAG.

---

## 4. Finding the coordinator owes the auditor

The auditor disclosed that identity inspection exposed a prior-summary fragment
in the annotated tag. That is this coordinator's doing and it applies to the
**pending RC-3 candidate audit as well**: the `audit-v1-rc-3` tag message is a
detailed narrative of the RC-2 findings and their repairs, including the
sentence "This was our own incomplete fix". Any auditor running
`git show audit-v1-rc-3` receives coordinator framing before reading a line of
source.

This was built into the candidate deliberately as a provenance aid and its
contamination cost was never considered. It is a standing defect in the
tagging convention, not a one-off.

**Disposition:** recorded as an open item. Future annotated tags carry
identity and scope only; narrative moves to the coordinator record. The
existing tags are left unmodified — rewriting a tag under a pending audit would
be worse — and the leak is disclosed to the RC-3 auditor's disposition when it
returns.

---

## 5. What survived attack

Recorded because it is evidence, not decoration. The auditor's failed
refutations load-test the plan's two central pivots:

- **V1's redirection stands in its measured form.** Deleting redundant direct
  imports did not shrink the closure; exact declaration re-rooting saved 0.411%
  of lines; packed-only saved 1.585%. Only dropping the packed claim was large,
  and it is not claim-preserving. What fails is the *generalization* to all
  claim-preserving change, not the measurement.
- **V2's core stands.** Mainline really is 0/11; the ratified endgame roadmap
  really banks the historical machine post-V1; M1 does not depend on E1.
- **V3 stands.** S1 remains a serialized-payload querying problem, the
  `flattenPayloadWords` non-invertibility blocker survives, and S1 neither
  closes nor gates preprocessing.
- **V4's identity stands exactly** — it is definitional `rfl`.
- The 18 access-source count and the 47/6 ledger partition both survived.

---

## 6. Consequences

1. **Preprocessing:** acceptance criterion withdrawn; no implementation until a
   frozen operational builder contract exists that provably excludes the oracle
   family. Contract design underway; the contract's own acceptance test is
   adversarial (the fake must be killed by a *named* obligation).
2. **Paper root:** DD-A conditional on the feasibility probe; the Core-splitting
   non-goal lifted for that probe.
3. **E1:** scope corrected to all-row adjudication; the "one protocol" narrative
   retired; public landing treated as a release-audit question.
4. **Measurement:** one script, named units, mutation controls, before any
   number re-enters a governance record.
5. **Calendar:** relabelled hypotheses; venue escalated.

A revised plan follows this record.

## 7. Assessment of the audit

The strongest audit this program has received. It reproduced the project's own
numbers to three decimals, corrected a figure the project had wrong, found a P0
by constructing a concrete counterexample rather than reasoning about
categories, caught a defect the coordinator introduced while *compressing* a
source design, and caught a manuscript narrative that contradicted a property
the project actively enforces.

Its independence disclosure is exemplary: it names the leak channel, states
what it excluded, and declines to claim perfect blindness. The
`PA-09` house-defect inventory — 21 items — is the most useful artifact
produced in this program's planning to date.

Two audits of candidates and one of a plan have now returned negative verdicts
with no invalid findings between them. The correct inference is not that the
work is bad; it is that this project's self-assessment is systematically
optimistic in one specific direction — **claims and their guards, never the
mathematics** — and that external adversarial review is the only mechanism that
has reliably caught it.
