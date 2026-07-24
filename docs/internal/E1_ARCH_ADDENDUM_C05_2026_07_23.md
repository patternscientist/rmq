# Addendum to `E1_ARCHITECTURE_COORDINATOR_HANDOFF.md`

**Author:** C05 (Claude runtime, disclosed fallback — cannot record `ACCEPTED`).
**Date:** 2026-07-23. **Travels with:** the dossier of the same date.
**Status of everything below:** coordinator analysis and verification receipts.
**No acceptance, no verdict, no launch authority.** The architecture choice in
§3 is a *recommendation to the owner and successor coordinator*, not a decision.

Every git fact below was resolved directly against
`C:\Users\poin\.codex\worktrees\bb61\RMQ` and the accepted PREHIST blob. Claims
sourced from reading are marked; claims not verified are marked as such.

---

## 1. The dossier is accurate, with two defects to fix before reuse

**Defect 1 — a truncated hash.** The dossier gives the B3 freeze tree as
`903c00b4458751d6dc4ec3c7ca39ea6c962f6e1` (**39 hex characters**). The correct
value, resolved by `git rev-parse 0554c0f^{tree}`, is:

```
903c00b4458751d6dc4ec3c7ca39ea6c962f6e1e
```

The worker's own report has this right. Note the irony: the dossier's failure-mode
table contains a "joined `rev-list` hashes" row about exactly this class of
defect. **Correct it before the dossier is used as an identity source.**

**Defect 2 — temporally superseded on B3.** The dossier froze while the B3 task
was `active` with a dirty worktree, and instructs the successor not to steer or
duplicate it. **That task has since terminated.** Runbook step 3's "if active"
branch no longer applies; the successor proceeds directly to terminal audit.

Everything else I checked in the dossier held.

---

## 2. The B3 candidate: independently verified

Verified against the worktree, not the worker's prose.

| Claim | Result |
|---|---|
| Chain `c190616 → 0554c0f → bc71cad` | **Confirmed** (`git log`) |
| Exactly two commits after base | **Confirmed** |
| Worktree/index/untracked clean | **Confirmed** (`git status --porcelain` empty) |
| Exactly five authorized paths changed | **Confirmed** (`git diff --name-only`) |
| HEAD tree `0ed3235d926c190adacdc8babc28c7acfa06490f` | **Confirmed** |

**The obstruction is execution-derived, not hand-authored.** `firstSubUnderflow`
(`Obstruction.lean:44`) observes only fetched instructions and prestep registers;
its successor comes from `E1Machine.step`; it runs over the accepted global read
store and the accepted `initialState`. This is precisely the "decorative
trace/category fields" hazard in the dossier's failure-mode table, and the worker
avoided it.

**Evidence tiers are honestly separated**, which is the main reason to trust the
report:

- **Kernel-checked:** `denseSegB_underflow_slot_numeric` (the slot really is
  `.sub 19 22 23`), `denseSegB_underflow_pc` (`(9+55)+4+2+3 = 73`),
  `pinned_source_subtraction_is_truncated`, `pinned_source_subtraction_is_not_ordered`,
  `ordered_subtraction_impossible_at_observed_state`,
  `source_simulation_and_ordered_subtraction_incompatible`.
- **Executable-tier only:** that tick 71 is *reached*. `pinnedFirstSubUnderflow`
  is a fuel-13000 run; the kernel cannot reduce it (the `Nat.log2`
  well-founded-recursion boundary this project has hit repeatedly).

The worker claimed no more than this, explicitly declined `HistoricalFAIL`, and
disclosed that the replay's Lake subprocess was sandbox-blocked and the escalation
denied. **The mutation campaign is therefore unexecuted** — acceptable for a stop
condition, mandatory before any eventual route acceptance.

**Not verified by me:** the frozen-byte and 42-case registry identity checks, the
non-owned blob identities, and the claim that commit 1 is matrix-only. A successor
audit should confirm those.

---

## 3. The architecture question — and the finding that reframes it

### 3.1 PREHIST already authorized the answer. The frozen contract dropped it.

This is the most important thing in this addendum.

**Accepted PREHIST report** (blob `be80468e…`), §6 "Arithmetic", verbatim:

> "Bound both operands and the result of each `add`, truncated `sub`,
> `mulConst`, and `divConst`; establish every required subtraction ordering
> **or an explicit checked-underflow behavior**."

PREHIST states a **disjunction**. Its ISA table (line 110) also records `sub`
correctly and unambiguously:

> `| sub dst src1 src2 | both source registers | truncated Nat subtraction | ... |`

The frozen B3 matrix row `B3-HIST-04-DYNAMIC-WIDTH-CLOSURE` requires
"...raw decode, **ordered subtraction**, and dormant-field coverage" — i.e. it
**collapsed PREHIST's disjunction to its first disjunct**, silently dropping
"or an explicit checked-underflow behavior."

**This changes the governance weight of the decision entirely.** Option 1 is not
an amendment weakening a frozen requirement against its accepted input. It is
**restoring a branch the accepted input already authorized**, which the contract
lost in transcription. That is a contract-repair result of exactly the same kind
as B2 R3 — and it is the **second** instance in this campaign of a frozen clause
contradicting the accepted definitions it constrains.

**Honest complication, flagged rather than smoothed:** PREHIST is *internally*
inconsistent. Its mutation row, copied verbatim into the B3 matrix, reads:

> `| MUT-HIST-06G-SUBTRACTION-UNDERFLOW | At pinnedSubPhase, swap the proved ordered operands | REJECT; consumeDynamicWidth |`

That row presumes the ordered branch. Under Option 1 there are no "proved ordered
operands," so **this mutation row must itself be re-specified**, not merely
inherited. A successor that adopts Option 1 without fixing `MUT-HIST-06G` will
carry a meaningless mutation case into the new registry.

### 3.2 Recommendation: Option 1

**Adopt truncated (monus) subtraction in the bounded target. Restate the clause
as: every arithmetic result is `< 2^w`.**

Four reasons, in descending strength:

1. **PREHIST authorizes it** (§3.1). This is restoration, not amendment.
2. **The accepted source ISA defines `sub` as monus.** The historical
   `E1Machine` docstring reads *"truncated natural subtraction, matching the
   route's `Nat` arithmetic."* An ordered-subtraction clause contradicts the
   accepted source's own definition of the operation it constrains.
3. **Truncation is the pervasive idiom, not a stray case.** The accepted port's
   own docstrings describe *"the truncated-subtraction min chain"*
   (`E1DenseSelectBlock.lean:34`) and *"the same truncated-subtraction cap chain
   `rankAtInit` uses"* (`E1FringeArmBlock.lean:23`). The program uses monus
   deliberately, as a saturating min/cap operator.
4. **Monus serves the clause's actual purpose better than orderedness does.**
   The clause exists so no value escapes `2^w`. Monus is width-closed
   *definitionally* — its result never exceeds its left operand. An
   ordered-ness side condition is both stronger than needed and refuted by the
   real execution.

**A fifth reason, forward-looking:** DD-20260719-205 (verified present at
`DESIGN_DECISIONS.md:7554`) documents a `Nat` truncation in the **current** route
— `decodePacket = if v = 0 then none else some (v - 1)`. So an ordered-sub clause
would eventually collide with **B2 as well**. Fix this once, centrally, across all
route contracts, rather than three times.

### 3.3 On the alternatives

**Option 2 (explicit compare-and-branch) is Option 1 implemented expensively.**
`if right ≤ left then left − right else 0` **is** monus, spelled with a branch,
at the cost of reopening ROM layout, atomicity, and charge accounting. It is
worth keeping in reserve as a *presentational* refinement if a reviewer ever
demands hardware-conventional wrapping semantics — it refines monus, so **nothing
is lost by deferring it.**

**Option 3 (change the historical source) defeats the historical route's
purpose.** B3 exists to show the *old* program runs on the shared object. A B3
that alters the source semantics is no longer B3.

---

## 4. Amendment to the earlier two-layer plan

The converged two-layer architecture (Nat reference machine + bounded machine +
one refinement bridge) rested on: *"the canonical run never overflows, so wrapping
is observationally irrelevant."*

**That premise covered growth only** — `add` and `mulConst`. Tick 71 shows
**underflow-agreement is a separate obligation**, and the canonical run
demonstrably *relies* on truncation there rather than merely tolerating it.

Consequence for whoever writes the bounded machine: **`sub` must be monus**, or
every reachable subtraction owes an ordered-ness proof — which the B3 obstruction
now refutes for at least one reachable state. This is not optional and should be
fixed in the contract before implementation, not discovered during it.

---

## 5. Process fix for the feedback loop

**A frozen contract clause about operation semantics must cite the accepted
source definition it constrains — and must preserve the full form of any
disjunction it inherits.**

Both halves matter here. The sub clause would have died at freeze time against a
one-line docstring; and the disjunction it dropped was sitting in the accepted
input it was derived from. Candidate regression name:
`FROZEN-CLAUSE-CONTRADICTS-ACCEPTED-DEFINITION`, alongside the existing
`Frozen-contract drift` row.

Recommend also auditing whether **other** B3 matrix rows narrowed PREHIST
disjunctions. I checked the subtraction clause only; the same transcription error
could have occurred elsewhere, and it is cheap to check now versus expensive to
discover mid-implementation.

---

## 6. Session/coordinator recommendation

**Hand off to a fresh coordinator before further architecture work.** Reasons, in
order of weight:

1. **The frontier moved past what this session knows.** Governance `a154983`, B1,
   and the entire B2/B3 campaign postdate this session's context; its cached pins
   are stale. Fresh entry through the dossier's startup gate is cleaner than
   patching state.
2. **Length is a fact-error risk.** This session has been compacted and carries a
   documented series of ~43 of its own failed claims — the exact failure mode an
   architecture finalization cannot absorb.
3. **This runtime cannot close the loop.** It is a disclosed fallback barred from
   recording `ACCEPTED`. The B3 disposition, the B2 re-freeze, and A4 all require
   a coordinator who can.

The successor should read the dossier as primary, this addendum as supplementary,
and **reconstruct both from git before acting on either.**

---

## 7. What this addendum does not establish

- It does not audit B3 to acceptance. §2 verifies identity, cleanliness, path
  scope, and the obstruction's derivation — not the frozen-byte checks, the
  42-case registry, non-owned blob identity, or the mutation campaign (which was
  not executed).
- It does not settle whether tick 71 is the *first* reachable underflow. The
  search is fuel-bounded and executable-tier; the kernel-checked facts are the
  slot, the PC, and the incompatibility.
- It records no verdict on B2, B4, or A4, and confers no launch authority.
- §3.1's transcription finding is based on reading the accepted PREHIST blob and
  the frozen B3 matrix row. **A successor should re-derive it independently
  before amending any contract on its basis.**
