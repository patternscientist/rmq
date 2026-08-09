# RC-1 correction round — working state and what remains

**Branch:** `codex/rc1-corrections`, on top of `main` = `f958f54`
(tag `audit-v1-rc-1`, the audited candidate).
**Commits so far:** `a484bbc` .. `29b1e85` (13 commits). Pushed, not merged.

Written so this round can be resumed cold. Read §4 first if you are picking up.

## 1. Why this round exists

The 2026-08-09 fresh-blind audit of `audit-v1-rc-1` returned **NOT_ACCEPTABLE**
(`docs/internal/audit_reports/2026-08-09_V1_RC_fresh_blind.md`). Every blocking
finding was independently reproduced before being fixed — none were taken on the
auditor's word, and none were wrong.

No mathematics failed. `RC-01`, `RC-03`–`RC-08` reconstruct; builds and axiom
inventories pass with standard axioms only. The failures are **claim wording,
gate coverage, and packaging**.

A second, non-blind strategic review (GPT 5.6) ran in parallel. It agreed on
substance and added one finding the audit did not have (see §4.1). One of its
claims is **wrong** and should not be acted on: it reports no `#print axioms`
for the packed capstone; there is one, at `scripts/axiom_check.lean:1232`.

## 2. Done, with verification

| auditor item | commit | verified by |
| --- | --- | --- |
| 1 — exact-cost wording → "at most `210`" | `a484bbc` | the theorem is `..._cost_le_...`; a guarded invalid query is `Costed.pure none` with cost `0` |
| 2 — manuscript/ledger/matrix reconciliation | `4980596` | `check_paper -SelfTest` PASS; `latexmk` exit 0, 0 undefined refs |
| 3 — hub lint whitespace | `a484bbc` | auditor's indented-import injection now exits 1 |
| 4 — constants at anchors, not file-wide | `a484bbc` | auditor's 1-of-5 mutation exits 1; a non-anchored one also exits 1 |
| 5 — strict claim-drift fails on missing roots | `a484bbc` | missing root exits 1; normal run unchanged at 0 |
| 6 — paper phrases + aggregate wiring | `a484bbc` | unattributed claim → 2 failures; attributed to a real bib key → excused |

Two of the four broken gates were **written by this project and claimed to be
injection-verified**. Both failed the same way: the injection tested the failure
shape the author imagined, not the space of failures.

The exact-cost defect **originated in the commissioning prompt's §2**, which
told the auditor the route "has a uniform charged-trace cost of `210`". It is
corrected and now names the `_cost_le_` theorem and the zero-cost invalid query.

## 3. Governance consequence, live

`RC-02` is not discharged in its commissioned literal form, so by its own terms
**`WDD-20260807-014` (the U3 subsumption) is void.** It is restored by the
corrected wording, not by any Lean change — the audit confirms the row
discharges as "at most `210`". Re-record this when the next audit returns.

## 4. What remains

### 4.1 Promote the packed result into `RMQPaper` — **DONE** (`7655ee8`, `1ff8cd2`)

Was: `RMQPaper`'s closure was 153 files with **zero** `PackedCellProbe` modules,
so the paper root exported the old `210` story while
`docs/PAPER_CLAIM_CORRESPONDENCE.md` named the packed theorem as the accepted
claim. A reviewer asking "what single import gives me the paper's theorem?" got
two different answers.

Now: `RMQ/Headlines/RMQ.lean` imports the capstone module and exports
`SuccinctRMQPackedCellProbeArchitecture` (the 39-field certificate) and
`succinctRMQPackedCellProbeArchitecture` (its producer), with a docstring
carrying the three reading rules this result is repeatedly over-read without.
The claim map cites the **public alias**, so the documented identity and the
importable identity are now the same string.
`scripts/headline_axiom_check.lean` audits it: `[propext, Classical.choice,
Quot.sound]`, nothing else. See DD-20260809-097 / WDD-20260809-016.

**The tension is now measured, and it is an owner decision.** The closure grew
`153 → 204` files and `139,054 → 190,529` lines — **+51 files, +51,475 lines,
+37%** in exactly the reviewer surface the owner wants reduced drastically.
Correctness was taken first: a paper root advertising the wrong theorem is a
defect, a large closure is a cost. The likely resolution is a **separate minimal
paper root** carrying the packed capstone and its genuine dependency spine,
leaving `RMQPaper` as the broad compatibility root. But which theorem the paper
is *about* determines what that root contains, so it was **not** settled here.

### 4.2 Independence regression (auditor item 7) — **DONE** (`3652d4b`, `c140d68`)

`scripts/independence_check.lean`, gate step 3b. Walks the transitive constant
closure of `packedReviewerControllerMeasure_valid_eq_427`'s type and value and
fails if `SuccinctClassic.queryCost` or `nonSyntheticWeight` appears. Observed:
1855 constants, neither present. Scope is the narrow property the ledger
actually claims — proof-term level, not module closure, since the packed
module's compilation closure *does* reach the charged declaration.

Three vacuity guards; two were added **because injection broke the first
version**: skipping proof terms left the type-reachable control green while the
target closure collapsed `1855 → 16` and still passed, and a non-transitive walk
left *both* controls green because both are shallow — only the closure floor
caught it (`74 < 500`). See WDD-20260809-017 / DD-20260809-098.

### 4.3 Base repin -- **DO THIS LAST**, and it is not a string swap

`paper/*` still pins base `e3362d4`. Before doing it mechanically, note the pin
appears in **two different roles** and they must not be treated alike:

1. **Substrate pin** -- `paper/README.md`, `paper/rmq.tex` (4 places),
   `NOVELTY_LOG.md`, `RELATED_WORK_LEDGER.md`: "this manuscript is pinned to
   repository base commit X". This is a statement about which tree the
   manuscript describes. It **must** move to the landing commit.
2. **Per-row acceptance records** -- 31 `Commit:` fields in
   `THEOREM_LEDGER.md`, each paired with `Status: ACCEPTED_BASE`. These assert
   *the row was verified against that tree*. Blanket-restamping them to a new
   commit asserts a re-verification that did not happen -- the project's own
   recurring defect class. Only restamp rows whose evidence was actually
   re-established, and say in the commit what re-established it.

Nothing enforces the pin: `paper/check_paper.ps1` never reads it.

**Citations audited 2026-08-09** (see `paper/EVIDENCE_MATRIX.md`): 9 `:NNN`
citations, 7 correct, 2 fixed. One had drifted from this round's own edits; the
other, `L-UB-06`'s `:9349`, **was already wrong at the pinned base commit** by
~1,090 lines and the fresh-blind audit did not catch it.

Follow-up, deliberately deferred to keep this round converging: a checker over
`file:line -> expected declaration` pairs, in the manner of the constant-sync and
independence checks. Better still, cite declaration names and keep line numbers
only where a checker verifies them.

Superseded original note:

`paper/*` still pins base `e3362d4`. It must be repinned to whatever commit the
round lands as. **Do this last**, after the tree stops moving.

### 4.4 P3-1 polish (non-blocking) -- **DONE** (`8e913b9`, `3265987`, `29b1e85`)

All four items closed. DD-20260809-099 (decorative premise, "tight" caps) and
DD-20260809-100 (fixture probe count, field 32); WDD-20260809-018.

- The decorative premise was a **chain of three**: removing the leaf's exposed
  that the same premise on `canonicalLcaCloseCostedWithRankSeed_cost_le` and
  `..._cost_le_principled` existed only to feed it. All three now stated without
  it -- a strengthening, disclosed per the B6 REQ-B6-09 precedent. Checked that
  the frozen matrix and `PAPER_MODEL_ADEQUACY.md` cite the conclusion, not the
  hypothesis list.
- "Tight operation-wise caps" -> upper bounds, with a note not to reintroduce
  "tight" without an attainment theorem.
- `egcpFixtureTraceLength` exported and added to `axiom_check`; the old local
  `have` routes through it.
- Field 32's docstring now states what it does **not** establish and points at
  fields 33/34.

Superseded original list:

- `_hleftCloseBound` accepted but unused in
  `ChargedFringeSubstitution.lean:359-365` — decorative premise.
- "Tight operation-wise caps" comment at `SuccinctFinalRAM.lean:8107-8109`
  overstates: the interior `33` has an attainment witness, the whole `210` does
  not.
- Stage-A field 32 is an eta/`rfl` arity pin, not the semantic no-hidden-input
  theorem it reads as.
- No exported `trace.length = 68` theorem for the fixture.

### 4.5 Then

New exact tag (`audit-v1-rc-2`, **not** `v*` — a `v*` tag fires
`release-artifact.yml` and publishes a GitHub Release) and a fresh blind audit.

## 5. Method note that cost this session five corruptions

**Do not edit this repository's CRLF files with Python `str.replace`.** Writing
`"\ref"` in a Python replacement string emits a carriage return and silently
corrupts LaTeX cross-references; a byte-level repair then mangled the whole
file's line endings. The §2 manuscript work above was redone through
**exact-string replacement** and was clean on the first pass.

Corollary that caught every one of these: **verify the effect — counts, greps,
file sizes, `git diff --check` — never the exit status.** `$?` after a pipeline
reports the last command, not the script.
