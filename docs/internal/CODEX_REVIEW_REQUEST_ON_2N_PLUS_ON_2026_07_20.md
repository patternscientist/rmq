# Review request to a Codex coordinator — the `o(n)` overhead finding and C05's recommendation

**Engineered per `.agents/skills/rmq-audit-prompt/SKILL.md` (canonical, read from
`main`).** Mode is non-standard and is declared below rather than forced into one
of the four the skill lists.

Everything from `## PASTE BELOW` onward is the prompt. Text above it is
coordinator launch metadata and must NOT be pasted.

## Coordinator launch metadata (do not paste)

- **Mode: DECISION REVIEW, not artifact audit.** The skill's four modes
  (fresh-blind delta, continuation, longitudinal, whole-frontier) all presuppose
  a candidate to accept or reject. Here the subject is a *strategic
  recommendation* plus the evidence behind it. The skill's substantive demands
  still apply and are carried over: adversarial evidence, independent
  reconstruction, evidence tiers, and the tightness/attainment standard.
- **Independence is deliberately compromised in one direction and compensated
  for.** The skill says do not give an auditor prior verdicts. But the owner
  asked for review OF the recommendation, so the recommendation must appear. It
  is quarantined into PHASE 2, after the reviewer commits their own verdict in
  writing. This is imperfect — a reader can look ahead — so the prompt says so
  and asks the reviewer to self-report if they did.
- **Prefer a different model family from the one that produced the findings**
  (they were produced by Claude). Genuine independence matters more here than
  usual, because four of the load-bearing claims sit at the weakest evidence
  tiers.
- Durable report path: `docs/internal/audit_reports/`.

---

## PASTE BELOW

# Decision review: is the RMQ project's `2n + o(n)` space claim in the right shape, and is C05's recommendation the right call?

You are reviewing a strategic recommendation and the evidence behind it. You are
NOT auditing a code candidate. Nothing here is asking you to accept or reject a
commit.

The governing goal of this project, in the owner's words, is the strongest
version of the RMQ spoke with **"technically justifiable but reviewers have to
spend brainpower auditing the justification as opposed to pattern matching
against precedent" MINIMIZED.**

## Ground rules

- **Read PHASE 1 and write your answer to it BEFORE reading PHASE 2.** PHASE 2
  contains another coordinator's recommendation, and reading it first will anchor
  you. If you do read ahead, say so in your report — an honest note costs
  nothing and a contaminated verdict presented as independent costs a great deal.
- Anchor every claim you make as `path:LINE` or as a verbatim quotation with a
  page number. Do not rely on search-result snippets for any literature claim;
  they fabricate plausible quotations. Retrieve primary PDFs.
- Distinguish what you READ from what you INFER, explicitly, throughout.
- **"The recommendation is right" is a perfectly good outcome.** So is "the
  finding itself is wrong." Both are more useful than a hedge.

## Repository

Read-only. Worktree `C:\Users\poin\Documents\RMQ\.worktrees\b2-charged-fringe`,
branch `claude/b1-b2-charged-fringe-tables`, HEAD `847a08b`.

**Two traps that have already cost this campaign real time:**

1. **A namespace-shadowed twin.** `RMQ.GenericSelect.sparseExceptionRelativeTableOverhead`
   (`RMQ/Core/GenericSelect/RelativeTables.lean:1192`, body
   `idDivLogLogOverhead 512 n + 512`) is a DIFFERENT definition from
   `RMQ.SuccinctSelect.sparseExceptionRelativeTableOverhead`
   (`RMQ/Core/SuccinctSelect/CloseSelect/BuiltRouting/SpanBudgets.lean:540`, body
   `idDivLogLogOverhead 512 (2 * n) + 512`). Grepping by bare name finds both.
   27 occurrences across 3 files bind to the twin. Check the namespace.
2. **Anchors in this project drift.** Several coordinator-supplied line numbers
   have been wrong. Verify anchors rather than trusting them, including the ones
   in this prompt.

---

# THE SITUATION (evidence only — no verdict)

The project proves a succinct RMQ structure occupying `2n + f(n)` bits with
`f(n) = o(n)`, plus a constant query cost. A survey established the following.
**Each claim is tagged with the evidence tier it actually rests on.** The skill
governing this review ranks tiers: kernel theorem > model theorem > executable
validation > artifact evidence > process evidence.

| # | Claim | Evidence tier |
|---|---|---|
| C1 | Overhead is `Theta(n / log log n)`, entering via `idDivLogLogOverhead` at two call sites | READ from definitions |
| C2 | Classical is `O(n lg lg n / lg n)` — Fischer & Heun SIAM J. Comput. 40(2) Thm 5.8; Navarro-Sadakane `O(n/log^c n)` | VERBATIM, primary PDFs |
| C3 | Therefore ours is worse by `lg n / (lg lg n)^2` — about a full log factor | INFERENCE from C1,C2 |
| C4 | `LittleOLinear` (`RMQ/Core/SuccinctSpace/Asymptotics.lean:22`) is the standard `o(n)` predicate, rationalised over `Nat` | READ |
| C5 | The `2n` is exactly `2n` (`Shape.lean:51`), payload one flat `List Bool`, nothing outside the counted structure | READ, equality |
| C6 | **The dominant term is IDENTICALLY ZERO for all n < 2^97**, because `localStride = 1` there and no slot is ever exceptional | **TRANSCRIPTION — Python re-implementation, exhaustive over all 2^m strings m<=16 plus adversarial to m=65536. NOT machine-checked.** |
| C7 | **The term is order-tight asymptotically above 2^97**, so it cannot be re-proved away | **INFERRED. The scout stated it could NOT enumerate the worst-case achievability argument.** |
| C8 | Call site (A) is FORCED by a correctness precondition: the dense leaf reads at most two machine words, so reaches only `wordSize` past base (`RMQ/Core/GenericSelect/Primitives.lean:531`) | READ precondition + INFERENCE |
| C9 | Four-Russians machinery is not portable here; it was ALREADY applied to this exact query path (`bpChunkedSelectCosted`, `ChargedRankSelectLeaves.lean:462`), moving cost 13->35 and space not at all | READ |
| C10 | Classical resolves multi-word blocks by reading one word of a COMPRESSED SUMMARY (count index: `lg lg n`-bit cardinality fields over `lg n`-bit chunks) and tabulating on the summary | VERBATIM, Golynski TR CS-2006-03 p.4 |
| C11 | A table on `c` RAW bits has `2^c` rows, so sublinearity forces `c <= ~(1/2) lg n` — no raw-bit table can ever reach past one word and stay `o(n)` | INFERRED (counting argument) |
| C12 | The summary already exists here: `logLogSampledDirectoryOverhead` (`Asymptotics.lean:239`) is `n lg lg n/lg n`, already proven `LittleOLinear`, already the rank directory's budget | READ |
| C13 | Floor for this architecture is `Theta(n (lg lg n)^3 / lg n)`, because past that the pre-existing `logLogCubed` terms bind | INFERRED |
| C14 | Below that is barred for INDEXING structures — Golynski Thm 1 p.8, `r = Omega(n lg lg n/lg n)`; escaping needs an ENCODING structure | VERBATIM |
| C15 | **Fixing this would move the frozen query-cost constant `210` and the step literal `11886`** | **INFERRED by C05 from the C9 precedent** |
| C16 | Blast radius of a value change: 5 value-dependent consumers, ~200 transparent; the target lemma already exists and is already proven | READ |
| C17 | The proposed better envelope crosses BELOW the current one at about `n = 2^10^5`; existing payload accounting cannot reach it past that crossover, so the repaired statements may be FALSE in the tail | COMPUTED |
| C18 | ZERO gates would fire on a space-shape change. `claim_drift_scan.ps1:7` roots are `README.md, artifact, docs` — nothing under `RMQ/` is ever scanned; `design_decision_check.ps1` omits `RMQ/Core/GenericSelect` | READ |
| C19 | At n = 2^20 the bad term is UNDER 1% of total overhead; the ~6,800x ratio to `2n` comes from the `logLogCubed` family, whose shape is ALREADY the classical one | COMPUTED |

Supporting detail, if you want it, is in `docs/internal/AUDIT_AND_A_DESIGN.md`
rounds 92-95. **That file is very long — read only those rounds.**

## Context you need about the cost side

The project's query cost is a frozen literal **`210`** charged reads
(`SuccinctFinalRAM.lean:8820`), with an all-size step literal **`11886`**. An
entire word-RAM reference-machine campaign ("E1") has been built on top of these
and is close to complete. C05 treats reopening `210` as expensive. Whether it is
*necessary* is claim C15, and C15 is inferred, not proved.

---

# PHASE 1 — YOUR INDEPENDENT VERDICT. Write this before reading PHASE 2.

Answer these. Do not look ahead.

**Q1. Is the finding itself correct?** Is the overhead really `Theta(n/lg lg n)`,
and is that really a log factor worse than the classical result? Check C1 and C3
against the source. If the survey mis-read the definitional chain, everything
downstream collapses and that is the most valuable thing you could return.

**Q2. Attack the two weakest links specifically.**
- **C6** rests on a Python transcription, the weakest tier in the hierarchy. If
  it is wrong — if the sparse-exception table is NOT empty below `2^97` — then
  the claim "invisible at every realistic size" is false and the whole practical
  argument inverts. Can you confirm or refute it from the Lean source? Could it
  be stated and proved as a Lean theorem, and what would that take?
- **C7** claims order-tightness. **Per this project's own audit standard, a
  claimed tightness or impossibility requires an equality/lower-bound witness or
  a checked counterexample on the same reachable object — an upper-bound proof
  establishes only an upper bound.** No such witness exists. Is C7 actually
  supported, or is it an unproved assertion doing load-bearing work?

**Q3. Is C8 — "forced" — really forced?** It rests on a correctness precondition
about two-word reach. Is that a genuine constraint on the architecture, or an
artifact of the current leaf that a different leaf would dissolve? C11 argues the
constraint is information-theoretic. Is that argument sound?

**Q4. Is C15 true?** *This is the single most decision-relevant question in this
review.* Would fixing the space bound necessarily move `210`? C05 inferred it
from the C9 precedent (rebuilding these leaves moved cost 13->35). But is there a
route that improves the space bound WITHOUT changing the read count — for
instance by changing only what is STORED rather than how it is READ? If C15 is
false, C05's recommendation loses its main support.

**Q5. Given all of the above, what should the project do?** State your own
recommendation and your reasoning, in your own terms, before reading PHASE 2.

**Q6. What is the honest sentence?** If the claim is to be reframed rather than
fixed, write the sentence you would put in an abstract. Judge it against the
governing goal: does a reviewer pattern-match it, or audit it?

---

# PHASE 2 — C05's recommendation. Read only after writing PHASE 1.

C05's recommendation is:

1. **Do NOT chase the classical asymptotic.** It is forced (C8), the ceiling
   short of a new mechanism is `sqrt(log)`, it would be invisible at every real
   size (C6, C19), and closing it reopens `210` and `11886` (C15) exactly as the
   E1 campaign lands.
2. **DO tighten the constants and prove the practical-range theorem.** The
   `hcodec` bound charges `512` where about `3` is true (~170x slack), and the
   `logLogCubed` `slots` constants are what actually produce the ~6,800x ratio at
   realistic sizes. Neither touches `210`.
3. **DO write the gap up as diagnosed, scoped future work** — arguing that a
   passage naming the mechanism precisely (raw-bit tabulation caps reach at one
   word; routing through the existing count directory yields
   `n (lg lg n)^3/lg n`, within `(lg lg n)^2` of Golynski's proven optimum for
   indexing structures) demonstrates command of the design space and reads better
   than either silence or a rushed fix.

**Now attack it.**

**Q7.** Where does it differ from your PHASE 1 answer, and who is right?

**Q8. Is item 3 self-serving?** "Document the gap as future work" is what a team
says when it does not want to do the work. Is this a genuine strength, or a
rationalisation? Would a program-committee reviewer read it as mastery or as an
excuse? Answer as if you were that reviewer.

**Q9. Is the reframed claim publishable?** The result would be: first mechanised
end-to-end verified succinct RMQ; exact `2n`; standard `o(n)`; explicit constant
query cost; **but a lower-order term a log factor weaker than the classical
result, and no construction-time theorem at all** (classical claims `O(n)`). Is
that a contribution, and at what venue? Be specific and cite precedent for
comparable formalisation papers.

**Q10. What did C05 miss?** Name anything not considered — a cheaper fix, a
different framing, a risk not surfaced, a claim that should not be made at all.

---

# NON-GOALS AND REJECTION CONDITIONS

- **Do not write Lean.** This is a review.
- **Do not accept a claim because it is confidently stated.** Four of the
  nineteen claims sit at the weakest evidence tiers and are marked as such.
- **Do not treat process evidence as mathematical evidence.** A report saying
  something was checked is not the check.
- **Reject any answer of your own that rests on a search snippet.** Primary
  sources or nothing, for every literature claim.
- Treat hedging language in the source material — "remaining risk", "the
  reviewer should ask", "medium-high confidence" — as presumptive evidence of
  incomplete closure, and say so where you find it.

# REPORT

Findings first, P0 through P3, each with exact evidence. Then your PHASE 1
answers, then PHASE 2. Then a single bottom line: **fix, reframe, or something
C05 did not consider** — and the one piece of evidence that most drove you there.

State explicitly whether you read PHASE 2 before completing PHASE 1.
