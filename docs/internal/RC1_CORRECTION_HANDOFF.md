# RC-1 correction round — working state and what remains

**Branch:** `codex/rc1-corrections`, on top of `main` = `f958f54`
(tag `audit-v1-rc-1`, the audited candidate).
**Commits so far:** `a484bbc`, `4980596`. Pushed, not merged.

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

### 4.1 Promote the packed result into `RMQPaper` — the biggest item

**Measured:** `RMQPaper`'s import closure is 153 files and contains **zero**
`PackedCellProbe` modules. So the paper artifact root exports the old `210`
story while `docs/PAPER_CLAIM_CORRESPONDENCE.md` says the accepted claim is the
packed theorem. A reviewer asking "what single import gives me the paper's
theorem?" gets two different answers.

Shape of the work:
- `RMQPaper.lean` imports only `RMQ.Headlines.RMQ`.
- `RMQ/Headlines/RMQ.lean` imports `EncodingLowerBound`,
  `SuccinctFinalModelAdequacy`, `SuccinctRMQClassicProvenance` — and references
  the packed capstone **nowhere**.
- The capstone is `RMQ.SuccinctFinal.PackedCellProbe.PackedReviewerArchitectureCapstone`
  (`ReviewerArchitectureCapstone.lean:300`), discharged by
  `packedReviewerArchitectureCapstone_holds` (`:702`).
- So: add the import plus a headline alias in `RMQ/Headlines/RMQ.lean`, following
  the naming convention of the existing aliases there.

**Needs a full `lake build`** (~13 min) — it changes the import graph. Do it
fresh, not at the end of a long session.

**Known tension, unresolved and deliberately so:** the owner also wants the
reviewer surface (~139k LOC in the `RMQPaper` closure) drastically reduced.
Promoting the packed result *grows* that closure. Both are right; the resolution
is probably a separate minimal paper root rather than widening the existing one.
Flagged for a design decision, not to be settled silently.

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
