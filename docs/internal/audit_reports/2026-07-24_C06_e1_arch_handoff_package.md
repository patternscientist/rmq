# C06 audit: E1 architecture handoff package (`E1_ARCH_HANDOFF_C06.zip`)

Auditor: C06 (Claude runtime, disclosed fallback — cannot record `ACCEPTED`).
Date: 2026-07-24.
Mode: coordinator handoff-package audit — package fidelity plus independent
re-derivation of the package's load-bearing claims. Not a route audit; no B2,
B3, B4, or A4 verdict is recorded here.

Subject: `C:\Users\poin\Downloads\E1_ARCH_HANDOFF_C06.zip` (41,690 bytes),
containing the C05 index, dossier, addendum, archived B3 worker terminal
report, and the two frozen prompt contracts.

Audit branch: `claude/rmq-formalization-audit-6d835f` at governance
`a154983ae465b25ae6d8118b56abfa95ddf5b409` (confirmed equal to `refs/heads/main`,
tree `9232abdcacbda528a6294370476907237f4e98bb`).

## Verdict

The package is **faithful and usable as the C06 entry point**. All six files
are byte-identical to the in-tree package on `claude/e1-arch-handoff-durable`;
both frozen prompt hashes and sizes reproduce exactly; every structural git
identity I checked resolves as recorded; and the addendum's central
transcription finding (PREHIST disjunction dropped by the frozen B3 matrix)
**re-derives independently from the accepted blobs**, as §9 of the addendum
requested. Two factual defects in the package's own prose were found (P2-1,
P2-2 below); neither changes any recommendation's substance, but both should
be corrected before the affected sentences are reused as identity sources.

No acceptance is recorded. The B3 candidate remains `OBSTRUCTED /
architecture-choice-required`, unaudited to acceptance, with its mutation
campaign unexecuted.

## Findings

- **P0:** none.
- **P1:** none.
- **P2-1 — the "adjudication file location" claim is false as written.**
  Index defect bullet 3 and addendum §1 defect 3 state that
  `docs/internal/E1_FINAL_ARCHITECTURE_ADJUDICATION.md` "exists only on the
  three rejected B2 branches, via commit `19b6d64`." Independently checked:
  the file is **also present at the accepted B3 source-port commit
  `c19061629ce8cf1e78992a99346170edd84b4971` itself** (both
  `docs/internal/E1_FINAL_ARCHITECTURE_ADJUDICATION.md` and
  `RMQ/Validation/E1FinalArchitectureAdjudication.lean`), because `19b6d64` is
  an ancestor of `c190616`. It is therefore at the tips of every descendant,
  including the B3 candidate branch `codex/e1-arch2-b3-historical-route-r1`
  and `codex/e1-arch2-final-adjudication`. The substantive point — the file is
  **not** at governance `a154983`/`main` — is confirmed correct. Consequence:
  dossier deferred item 8 is *more* satisfiable than the addendum suggests
  (any B3-derived checkout carries the file), but the "only three rejected
  branches" sentence must not be reused for retargeting decisions.
- **P2-2 — DD-20260719-205 citation contradicts the addendum's declared
  verification base.** Addendum §3.2 says the DD was "verified present at
  `DESIGN_DECISIONS.md:7554`," while the addendum declares all git facts were
  resolved against the bb61 worktree (HEAD `bc71cad`). At `bc71cad`,
  `docs/internal/DESIGN_DECISIONS.md` has 5,138 lines and does **not** contain
  `DD-20260719-205`. The DD exists at line 7554 on
  `claude/b1-b2-charged-fringe-tables` (and is referenced from
  `RMQ/Core/WordRAM/E1WholeQueryAgreement.lean` on several E1 branches). The
  **substance is confirmed**: the DD documents
  `decodePacket = if v = 0 then none else some (v - 1)` — a current-route
  `Nat` truncation — so the addendum's fifth reason stands; only the
  provenance sentence is wrong.
- **P3-1 — no committed artifact pins the seven-field observation.** The
  committed `Obstruction.lean` at `bc71cad` defines `pinnedFirstSubUnderflow`
  (fuel 13000) but contains **no theorem or committed `#eval` output stating**
  `pinnedFirstSubUnderflow = some { tick := 71, pc := 73, … }`. The exact
  observation exists only in matrix prose and via the replay's generated
  probe, and the replay never ran green (Lake subprocess sandbox-blocked;
  escalation denied). The kernel-checked theorems are honest but arithmetic
  in character; the anti-vacuity core — that PC 73 with registers 5/19 is
  actually reached — is currently backed by no reproduced artifact. Both the
  worker report and addendum §9 disclose this tiering, so it is a
  successor-obligation note, not a misrepresentation: **the obstruction
  replay (at minimum the probe) must run green before any B3 disposition
  treats tick-71 reachability as established.**
- **P3-2 — in-tree package is on an unmerged branch.** The index says the
  documents "are now in-tree." True on `claude/e1-arch-handoff-durable`
  (three commits atop governance: `e01c58a`, `82afc6c`, `67c6799`), which is
  **not merged to `main`**. A successor cloning `main` alone still will not
  see the package. Consistent with the no-integration-without-authority rule;
  noted so the branch is not mistaken for mainline durability.

## Package fidelity (all confirmed)

| File | Bytes | SHA-256 (computed) | Matches record | Byte-identical in-tree |
|---|---:|---|---|---|
| `prompts/E1_ARCH2_B3ROUTE_R1_PROMPT.md` | 22,058 | `EF0112…D320` | yes (dossier + index) | yes |
| `prompts/E1_ARCH2_B2DESC_R4_PROMPT.md` | 18,623 | `A3EC3C…47CF` | yes (dossier + index) | yes |
| `00_READ_FIRST_INDEX.md` | 4,342 | `D1DE6F…D612` | n/a | yes (`E1_ARCH_HANDOFF_INDEX.md`) |
| `01_DOSSIER…HANDOFF.md` | 28,486 | `B7F35B…CA63` | n/a | yes |
| `02_ADDENDUM_C05_2026_07_23.md` | 15,917 | `83F603…0767` | n/a | yes |
| `03_WORKER_TERMINAL_REPORT_B3ROUTE_R1.md` | 5,641 | `9129A4…9267` | n/a | yes |

The `.gitattributes` on the handoff branch carries
`docs/internal/e1_arch_prompts/** -text` plus the dossier, as the index claims.

## Independent re-derivations (the checks the addendum asked of a successor)

1. **Transcription finding (addendum §3.1) — CONFIRMED.** Accepted PREHIST
   blob `be80468e…`, lines 543–545, verbatim: "establish every required
   subtraction ordering **or an explicit checked-underflow behavior**"; ISA
   row at line 110 defines `sub` as "truncated `Nat` subtraction". Frozen B3
   matrix blob `f292cd75…`, line 201 (`B3-HIST-04-DYNAMIC-WIDTH-CLOSURE`)
   requires "raw decode, **ordered subtraction**, and dormant-field coverage"
   — the disjunction's second branch is absent. Line 415 (`MUT-HIST-06G`)
   presumes "the proved ordered operands" and must be re-specified under any
   monus adoption, as the addendum flags.
2. **Dossier defect 1 (truncated hash) — CONFIRMED.** Dossier records the B3
   freeze tree as 39 hex chars; `git rev-parse 0554c0f^{tree}` =
   `903c00b4458751d6dc4ec3c7ca39ea6c962f6e1e`.
3. **Dossier defect 2 (B3 terminal) — CONFIRMED.** Chain
   `c190616 → 0554c0f → bc71cad` exact; bb61 worktree clean at `bc71cad`
   (empty `git status --porcelain`); HEAD tree `0ed3235d…490f`.
4. **Candidate scope — CONFIRMED (closes an addendum §9 gap).** Commit 1
   adds only `docs/internal/E1_ARCH2_B3_HISTORICAL_ROUTE_MATRIX.md`
   (matrix-only). Commit 2 changes exactly the five paths of the frozen
   prompt's write scope (prompt line 27): the obstruction module, the matrix,
   the replay script, and both decision logs. No non-owned path changed, so
   all non-owned blobs are base-identical by construction.
5. **Frozen-byte property — CONFIRMED (closes an addendum §9 gap).** Diff of
   freeze matrix blob vs `bc71cad` matrix touches only the terminal
   evidence/status section (line 513 onward); all frozen rows byte-identical.
6. **42-case registry — CONFIRMED structurally.** Final matrix carries
   exactly 42 `MUT-HIST-*` rows; the committed replay enforces 42 unique IDs
   with an exact 41 `REJECT` / 1 `ACCEPT` split and a frozen-byte guard.
   **Not run**: the replay itself (Lake build requires network/toolchain);
   the mutation campaign remains unexecuted, matching the worker's
   disclosure.
7. **Obstruction module content — CONFIRMED.** No `sorry`/`admit`;
   `firstSubUnderflow` observes only fetched instructions and prestep
   registers with successors from `E1Machine.step` over the accepted global
   read store and `initialState`; the six named theorems are present with
   the reported statements. See P3-1 for the tiering caveat.
8. **Truncation idiom citations — CONFIRMED at `c190616`.**
   `B3SourcePort/E1Machine.lean:94` ("truncated natural subtraction,
   matching…"), `B3SourcePort/E1DenseSelectBlock.lean:34`
   ("truncated-subtraction min chain"), `B3SourcePort/E1FringeArmBlock.lean:23`
   ("the same truncated-subtraction cap chain"), plus the `Nat.min` theorem at
   `E1FringeArmBlock.lean:247`.
9. **Startup-gate claims (addendum §7) — CONFIRMED.** At governance,
   `scripts/project_skill_preflight.ps1` computes `missingRequiredRuntime`
   against `-RequiredSkills` only (line 108), fails on an empty runtime
   catalog (line 167), and iterates checkout/working checks over all expected
   skills (lines 106–107). `.claude/skills/` is absent on `main` and present
   only on `claude/rmq-formalization-coordinator-bd7045` with wrappers
   `rmq-audit`, `rmq-coordinator`, `rmq-proof-sprint`.

## Verification commands (summary)

`sha256sum`/`wc -c` over all zip members; `git cat-file blob | cmp` against
`claude/e1-arch-handoff-durable` paths; `git rev-parse` /
`git log --format='%H %T'` over the B3 chain; `git diff --name-status` for
both candidate commits; `git cat-file blob` + line-addressed `sed`/`grep`
over blobs `be80468e…`, `f292cd75…`, and the `bc71cad` matrix/replay/module;
full freeze-vs-final matrix diff; `git branch --all --contains 19b6d64`;
`git merge-base --is-ancestor`; `git status --porcelain` in the bb61
worktree. Skipped: `lake build` / replay execution (toolchain/network), and
`project_skill_preflight.ps1` (Claude runtime structural limitation —
disclosed fallback; no role skill was substituted).

## Disposition and next actions for the owner / successor

1. The package may be used as the C06 entry point as-is; correct P2-1 and
   P2-2 in a superseding note (per convention, do not edit the archived
   files in place).
2. The architecture recommendation (adopt monus; contract repair, not
   amendment) now has its evidentiary basis independently re-derived by a
   second coordinator. **The decision remains with the owner.** If adopted:
   restate the width clause as "every arithmetic result is `< 2^w`",
   re-specify `MUT-HIST-06G`, and audit the other B3 matrix rows for further
   narrowed PREHIST disjunctions before any re-freeze.
3. Before any B3 disposition, run the committed obstruction replay green
   (closing P3-1) and execute the mutation campaign.
4. Decide whether to merge `claude/e1-arch-handoff-durable` into `main`
   (owner authority required) so the in-tree package claim holds on the
   mainline.
