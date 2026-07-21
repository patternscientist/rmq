# Fresh-blind external audit of E1, and the conditions for merging it

**Engineered per `.agents/skills/rmq-audit-prompt/SKILL.md` (canonical, read from
`main`), mode: FRESH BLIND DELTA.** Everything from `## PASTE BELOW` onward is
the prompt. Text above it is coordinator launch metadata and must NOT be pasted.

## Coordinator launch metadata (do not paste)

- **This is the rung's real gate.** Ten-plus internal lanes and a coordinator
  adjudication are not an external verdict, and must never be presented as one.
- **The coordinator's verdict, row statuses, evidence cells, and session
  narrative are deliberately WITHHELD.** Per the skill: do not give a fresh
  auditor prior verdicts or transcripts. The auditor reconstructs the
  requirement-to-evidence mapping independently from the frozen IDs. The
  `Evidence obtained` and `Status` cells in the matrix are **coordinator-written
  and are part of what is under audit** — the prompt says so.
- **Prefer a different model family from the one that authored the work**
  (Claude). Independence matters more than usual here: the coordinator has
  recorded ~43 of its own failed claims across this campaign, and an
  independent review two days ago refuted two of three justifications in an
  adjacent decision.
- **Sequencing matters and is in the prompt:** `main` must be merged into the
  campaign branch BEFORE the audit, or the audit is against a stale pre-audit
  B7. That merge is already item 1 of an existing Codex handoff.
- Durable report path: `docs/internal/audit_reports/`.
- Merge is explicitly NOT authorised by this prompt. It is gated on the owner
  accepting the audit's verdict.

---

## PASTE BELOW

# Fresh-blind audit: the E1 word-RAM reference machine

You are the independent external auditor for a milestone in a Lean 4
formalization of succinct RMQ (Range Minimum Query). Your report is the gate on
whether this milestone is accepted. **You are not being asked to confirm a
conclusion — no conclusion is being supplied to you.**

## What you are NOT given, and why

You are deliberately not given the implementing team's verdict, their per-row
status assessments, their session narrative, or their confidence. **The matrix's
`Evidence obtained` and `Status / residual gap` columns are written by the
coordinator who commissioned the work and are themselves part of what you are
auditing.** Do not treat them as evidence. Reconstruct the
requirement-to-evidence mapping yourself from the frozen requirement text.

## Commits and sequencing

- **Campaign branch:** `claude/b1-b2-charged-fringe-tables`, HEAD **`e9de160`**
- **`main`:** **`dcc660f`**
- **Divergence base:** **`d5a9355`** — 195 commits on the campaign side, 66 on
  `main` since.

**BEFORE AUDITING, MERGE `main` INTO THE CAMPAIGN BRANCH AND REBUILD.** The
campaign carries a pre-audit B7 from before the divergence. Auditing `e9de160`
as-is audits a stale base, and any finding about B7-era constants would be
against superseded code. If the merge is not clean or does not build, **that is
itself a P0 finding and you should stop and report it** rather than working
around it.

## The claim under audit

E1 is a **reference word-RAM machine** for the whole RMQ query. In outline: a
small-step instruction semantics; one charged step per executed instruction; the
entire query compiled to a program and actually executed; and the machine's
memory-read log related to the route's trace. Its purpose is to make the
project's cost claim mean something operational rather than definitional.

Two constants recur and are **NOT the same thing** — conflating them is a known
hazard:

- **`210`** bounds **charged READS** (`queryCost`, `SuccinctFinalRAM.lean:8820`),
  algebra `2*35 + (2*11 + 2*37 + 33) + 11 = 210`.
- **`11886`** bounds **machine STEPS**
  (`E1WholeQueryCostLiteral.lean`), derived separately.

## The frozen requirement IDs

Eleven, in `docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`:
`REQ-E1-01` through `REQ-E1-11`. **Enumerate them verbatim from the file** —
reject any ID not present there and do not invent IDs. The matrix also carries
`INV-` invariants and `CHK-` checks; include them.

Two amendments to frozen requirement text exist (`AMENDMENT A1`, `AMENDMENT A2`)
and are owner-approved. **Amendments are legitimate, but audit them**: an
amendment that quietly widens a requirement to fit what was built is a P0. Ask
specifically whether each amendment changed what must be proved, or only which
object it is proved about.

## What to attack — mapped to this milestone

Generic adversarial checks apply, but these are where this particular work is
most likely to be hollow:

**1. Trace provenance — occurrence, not membership.** The project claims
"positional receipt equality": the machine's read log equals the route's trace
element-by-element. **State whether the theorems retain only event-VALUE
membership, or genuinely occurrence POSITION, multiplicity, producing
instruction, and invocation parameters.** `List.Mem` alone is not
occurrence-level evidence, and a proof term's construction does not compensate
for information erased from the proposition. Check whether an equality is over
lists, multisets, or sets.

**2. Counterfactual mutation.** The project claims a family of machine mutants,
each rejected by a discriminator the others miss. For each mutant, **identify
which checked theorem or executed check rejects it**, and verify the rejection
is real rather than incidental. Then construct your own mutant the suite does
not anticipate. Specifically try: a program that pads its receipt with
DECORATIVE reads (correct answer, extra events), and one that reads nothing at
all. If a discriminator is claimed "value-only" or "receipt-only", test that
claim rather than accepting the label — at least one such label was recently
found to be wrong.

**3. Address capacity, including tiny and dead/sentinel cases.** Check the width
accounting at SMALL shapes (`n = 0, 1, 2, 4`) and at any dead or sentinel
address. This project has found **three separate address coincidences** that were
invisible until executed — two distinct program locations sharing an address
while every proof still passed. Look for a fourth.

**4. Claimed constants — upper bound is only an upper bound.** `210` and `11886`
are literals. **A proof of `cost <= K` does not establish that `K` is attained or
that `cost <= K - 1` is false.** If any document claims tightness, attainment, or
minimality for either, demand an equality or lower-bound witness on the same
reachable object, or report the claim as unsupported.

**5. Identity chain across combined claims.** The public story combines space,
execution, provenance, and machine facts. **Verify they concern the SAME
construction** — that the object the machine executes is the object the space
bound is about is the object the public `List Int` query answers with. A
technically correct wrapper over a different object is the failure mode.

**6. Uncounted storage and synthetic events.** Check that nothing operationally
required sits outside the counted payload, and that no trace event is
manufactured rather than emitted by an executed read.

**7. Executable evidence versus proof.** The project has both theorems and a
validator executable. **Do not accept a validator run as proof of a mathematical
claim, and do not accept a theorem as evidence that the executable does what it
says.** Report which tier each key claim actually rests on: kernel theorem, model
theorem, executable validation, artifact, or process.

## Hazards that will waste your time if you do not know them

These are factual, not verdicts. They exist because this campaign has already
lost time to each.

- **There are TWO distinct `33`s**: a fringe-window chunk-read cap living INSIDE
  `endpointFringe = 4 + 33 = 37` (`ChargedFringeChunks.lean:1647`), and a
  whole-interior-directory read cap (`InteriorDirectory.lean:1934`). One sits
  inside the other's sibling term in the same algebra. There are likewise **two
  distinct `8`s**.
- **Frozen HISTORICAL constants (`207`, `142`, `76`, `328`, `352`) are pinned to
  literals deliberately** so no later recharge can rewrite history. A row stated
  against a historical constant is not weakened by a live constant moving.
- **Namespace-shadowed twins exist.** At least one identifier
  (`sparseExceptionRelativeTableOverhead`) has two definitions with different
  bodies in different namespaces. Check namespaces before concluding.
- **Line numbers in this project's documents drift and several are known wrong.**
  Verify anchors; identifiers are stable, line numbers are not.
- **An empty or truncated Lean file compiles silently.** No output from a run is
  conclusive until the input's byte count is checked.
- **`Nat.log2` is well-founded recursion** — the compiler evaluates it, the
  kernel cannot. Proofs that ask the kernel to reduce it on large literals will
  hang.
- **Piping a PowerShell script through another command reports the PIPE's exit
  status, not the script's.** Use
  `powershell -Command "& { & '<script>' <args>; exit $LASTEXITCODE }"`.

## Commands

- `lake build RMQ` — the library.
- `lake build rmq_e1_machine_validate` then `lake exe rmq_e1_machine_validate` —
  the validator. Read its per-check lines, not only its final verdict; several
  lines are annotated with what they must equal and why.
- `#print axioms <decl>` — expect at most `[propext, Classical.choice,
  Quot.sound]`. **Any `sorryAx` or extra axiom is a P0.**
- Hygiene: no `sorry`, `admit`, `axiom`, `native_decide`, `partial`, `unsafe`,
  `implemented_by`, no Mathlib import, no raised `maxHeartbeats` on proofs about
  execution structure.

## Non-goals and rejection conditions

- **Do not fix anything.** Report-only. Proof and source files are read-only to
  you; you may write exactly your report file under
  `docs/internal/audit_reports/`.
- **Do not accept a claim because it is confidently stated**, in a docstring, a
  design-decision entry, or a matrix cell.
- **Do not inherit any statement that a residual theorem is "strictly stronger"
  or optional.** Map it to the frozen requirements yourself.
- **Treat hedging language as presumptive evidence of incomplete closure** —
  "remaining risk", "the reviewer should ask", "a future consumer must prove",
  "medium confidence". Where you find it, say so.
- **A blank cell or a coordinator-owned `Open` status is not by itself a failed
  row** when the schema reserves acceptance to the coordinator. Conversely,
  appended prose does NOT close a row unless its exact proposition, consumer,
  object identity, and anti-vacuity obligation do.
- Reject invented IDs, count-only summaries ("14 rows checked, all fine" is a
  claim, not an audit), and findings that infer missing evidence solely from
  where it is physically placed.

## Report

Findings first, **P0 through P3**, each with exact source, theorem, and command
evidence. Then:

1. **Your independent requirement-to-evidence reconstruction** — every frozen ID
   mapped to the evidence you found, with your own verdict per row, reached
   without reference to the coordinator's cells.
2. Verification outcomes: build, validator, axioms.
3. **Stale objections** — things you initially suspected and then cleared. These
   are useful; record them.
4. Roadmap alignment: does this milestone advance the stated target, or is it
   valuable work advancing a different goal?
5. The best next target.

## On merging

**This prompt does not authorise a merge.** If your verdict supports it, state
explicitly what would have to be true for the campaign branch to merge to
`main` — which findings are blocking, which are advisory, and what should be
re-verified after the merge. The owner decides; a merge before their acceptance
would bypass the gate this audit exists to be.
