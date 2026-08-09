# RC-1 correction round — working state and what remains

**Branch:** `codex/rc1-corrections`, on top of `main` = `f958f54`
(tag `audit-v1-rc-1`, the audited candidate).
**Commits so far:** `a484bbc`, `4980596`, `1c0c8bb`, `7655ee8`, `1ff8cd2`. Pushed, not merged.

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

### 4.2 Independence regression (auditor item 7)

Add a check that the packed structural countdown does not acquire a dependency
on charged-cost declarations. Current status is recorded honestly in
`paper/THEOREM_LEDGER.md`: independence holds at **declaration and proof-term**
level; the module closure does transitively reach the charged declaration
(`ReviewerController.lean` → `ReviewerSparsePrelude` → `ReadProgram` →
`SuccinctFinalStoreParam` → `SuccinctFinalRAM`). Guard the narrow property, not
the false one.

### 4.3 Base repin

`paper/*` still pins base `e3362d4`. It must be repinned to whatever commit the
round lands as. **Do this last**, after the tree stops moving.

### 4.4 P3-1 polish (non-blocking)

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
