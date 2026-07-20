# C05 post-E1 plan — owner-directed 2026-07-19

Recorded so it survives context loss. **Nothing here starts until E1 has totally
landed** — meaning every loose thread from the eleven-row evidence audit is
closed and the matrix is adjudicated, not merely that construction is done.

Owner's sequence, in order.

---

## 0. Scout C/Rust generation — a DECISION memo, not an implementation

**The question, in the owner's terms:** is it worth it, given that the goal is
the strongest version of the RMQ spoke with "technically justifiable but
reviewers must audit the justification rather than pattern-match against
precedent" MINIMIZED?

Weigh two things explicitly:

1. **Effort from here versus precedent.** What would it actually take, and does
   the literature have a standard shape for it that a reviewer recognises?
2. **Reviewer confidence gained relative to what we now have.** We now have a
   fully charged small-step machine with positional receipt equality, an
   independent `List Int` reference implementation, twelve machine-level
   mutations each proved real and proved invisible to the discriminators that
   should miss it, and a kernel-checked all-size step literal.

**The project's own roadmap already carries a steer, and it should be quoted
rather than rediscovered:**

> "External C/Rust generation is optional. Add it only if it reduces reviewer
> friction after the reference-machine theorem exists; **a bespoke translation
> validator that is harder to audit than the Lean executable is not progress.**"

My prior — to be tested, not assumed — is that the marginal reviewer confidence
is small and the marginal audit surface is large, which is the wrong side of the
stated goal. **But that is a prior and the owner asked for a weighing, so do the
weighing.** The honest output may be "no", and a well-argued "no" is a real
deliverable here.

## 1. An external audit prompt for E1

Use the audit-prompt skill. **NOTE THE RENAME AND THE BROKEN WRAPPER:**

- The canonical skill on `main` is now `.agents/skills/rmq-audit-prompt/SKILL.md`
  (verified on `main` at `0b8490c`; there is also `agents/openai.yaml` beside
  it, and `.agents/skills/rmq-coordinator/`).
- **My Claude-runtime wrapper is `.claude/skills/rmq-audit/SKILL.md` and defers
  to the OLD `rmq-audit` path.** It must be repointed at `rmq-audit-prompt`.
- The coordinator worktree predates the rename and carries only
  `.agents/skills/rmq-proof-sprint/`, so read the canonical file from `main`.

Standing protocol constraints that still apply: a fresh blind auditor gets
**exact commits and an audit packet, never the worker verdict, the live worktree,
or the chat transcript**; prefer a different model family from the one that
authored the candidate; log the round to `AUDIT_AND_A_DESIGN.md` and, for
A-series audits, to `docs/internal/audit_reports/`.

**Material the audit prompt should point at**, all produced this campaign:
the eleven-row evidence table with each row's `Scope` and `Evidence needed`
quoted; the all-size literal `11886` and its derivation; the twelve machine
mutations; the three address coincidences found only by execution; and the
standing corrections — that matrix rows are NOT whole-query scoped, that `210`
bounds READS while `11886` bounds STEPS, and that there are two distinct `33`s.

## 2. Remaining roadmap items — A1 and M1

Read from `main`'s roadmap, not recalled.

### M1 — Make Machine Adequacy Reviewer-Native
Roadmap status still reads "partially present; strengthen after `U3`". Wants
exact **dynamic read set** agreement as the primary supplied-store theorem, safe
footprint demoted to a corollary, and the recurring address/operand/word-width/
store/trace invariants bundled into a named **machine-well-formedness
certificate** consumed by the headline, so the public statement reads as one
chain: list query = canonical costed query = supplied-store execution under exact
read agreement = first-order controller execution.

**E1 has probably discharged much of this already** — positional receipt
equality IS exact dynamic-read-set agreement, and `WholeQueryMachineAgrees` is
close to the certificate shape. **Establish the real residual by reading, not by
assuming, before scoping any work.** Also note `codex/m1-reviewer-native-machine-adequacy-r4`
is NOT in `main`.

**Highest priority of the two**, because it is closest to E1's output and most
likely to be nearly done.

### A1 — Refactor Around The Stable Argument
"Partially begun; perform after `U2` stabilizes interfaces." Split payload
layout / program-and-trace semantics / cost derivation / adequacy; thin
compatibility roots; quarantine history, obstruction and superseded route
modules; regenerate the import-closure report. Two hard constraints from the
roadmap itself: **remove dead aliases only after reverse-dependency proof**, and
**mechanical movement and semantic strengthening must be separate commits**.

**Largely mechanical — good Codex work.** But it contains public-surface
removal, which is on the escalate list, so the pruning decisions go to the owner.

### Delegation
The owner has authorised delegating to Codex. `CODEX_HANDOFF_FROM_C05_2026_07_19.md`
is the existing handoff pattern. A1 is the natural candidate; M1's residual
assessment should be done first and by whoever holds E1's context.

---

## Also outstanding, not in the owner's three

- **`ready-threshold measurements once construction is fast enough`** — named in
  E1's own roadmap section under the executable-evidence path, and the one item
  of that list I believe has never been done.
- **V1** (independent verification and submission freeze) remains the final
  milestone; a scout exists at `codex/v1-s01-independent-verification-scout`
  (`f218b98`). Its real gate is **one fresh blind external audit of the exact
  release commit**, with the same auditor only for its correction loop and a
  DIFFERENT fresh auditor for final acceptance if material changes land.
