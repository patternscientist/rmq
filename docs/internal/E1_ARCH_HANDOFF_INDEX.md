# E1 architecture handoff — index

**Start here.** This is the durable entry point for a coordinator picking up the
E1 architecture campaign. It exists because the handoff dossier instructs its
successor to *"reconstruct the frontier from Git rather than from this prose"* —
while the dossier itself and the frozen prompt contracts previously lived only
outside the repository, in a Downloads folder and a per-session visualization
directory. They are now in-tree, so that instruction is satisfiable.

Committed 2026-07-23 by C05 (Claude runtime, disclosed fallback — cannot record
`ACCEPTED`). **Nothing here is an acceptance, a verdict, or launch authority.**

## Read in this order

| # | Document | What it is | Trust |
|---|---|---|---|
| 1 | `E1_ARCHITECTURE_COORDINATOR_HANDOFF.md` | The frontier map: accepted inputs, B2/B3 chronology, remaining work, runbook, failure modes | Editable handoff, **not proof evidence**. Three known defects — see below. |
| 2 | `E1_ARCH_ADDENDUM_C05_2026_07_23.md` | Verification receipts against the dossier and the B3 candidate; the architecture recommendation and its evidence; startup-gate and packaging findings | Coordinator analysis. §9 states its own limits. |
| 3 | `E1_ARCH2_B3ROUTE_R1_WORKER_TERMINAL_REPORT.md` | The terminal `OBSTRUCTED` report from the B3 route worker | **Untrusted worker prose.** The subject of an audit, not evidence for one. |

Then reconstruct everything else from git. The dossier names exact commits for
B1, PRELOGIC, PRECUR, PREHIST, and the B3 source port; `AUDIT_PROTOCOL.md` and
the `rmq-coordinator` skill are already in-tree and need no separate handover.

## Archived prompt contracts

`e1_arch_prompts/` holds the frozen contracts, committed **byte-identical** so
the SHA-256 identities recorded in the dossier reproduce. A `.gitattributes`
rule marks them `-text`; without it, `core.autocrlf` would normalize their CRLF
content and the hashes would not reproduce off-Windows.

| File | Bytes | SHA-256 | Classification |
|---|---:|---|---|
| `E1_ARCH2_B3ROUTE_R1_PROMPT.md` | 22,058 | `EF0112772907E0005BF5B6A978EF7903957CFA0DEF948CF1FABB3F064165D320` | Frozen contract for the terminated B3 task. **The document the B3 candidate must be audited against.** |
| `E1_ARCH2_B2DESC_R4_PROMPT.md` | 18,623 | `A3EC3C3077FEE9A34D34FBD745D393ED2DF9BAB92DA081CFDB79F5F6091A47CF` | **DRAFT / NOT LAUNCHED.** Not launch authority. Re-read against then-current governance, correct its contract, and run `worker_prompt_preflight.ps1` first. |

Both verified against the dossier's recorded size and hash before commit.

## Known defects in document 1, corrected in document 2

Read the dossier **with these three corrections in hand.** It is archived
verbatim rather than edited, per this project's standing convention of
superseding in place rather than overwriting — and because its own provenance
statement ("every named commit and blob was resolved with Git while preparing
this dossier") would become false about an edited copy.

1. **Truncated hash.** The B3 freeze tree is given as
   `903c00b4458751d6dc4ec3c7ca39ea6c962f6e1` — 39 hex characters. The correct
   value is `903c00b4458751d6dc4ec3c7ca39ea6c962f6e1e`.
2. **Superseded on B3.** The dossier froze while the B3 task was active and
   dirty, and says not to steer or duplicate it. That task has since terminated
   with a clean two-commit candidate. Runbook step 3's "if active" branch no
   longer applies.
3. **Deferred item 8 targets a file that is not on the mainline.**
   `E1_FINAL_ARCHITECTURE_ADJUDICATION.md` is not at governance `a154983` or on
   `main`; it exists only on the three *rejected* B2 branches, via commit
   `19b6d64`.

## The open architecture question

The B3 worker stopped on a genuine architecture choice: the accepted historical
program uses `Nat` subtraction as a **saturating min-chain operator**, and the
frozen B3 contract simultaneously demands ordered/no-wrap subtraction. Addendum
§3 recommends adopting truncated (monus) subtraction, and records the finding
that makes this a *contract repair* rather than a requirement amendment — the
accepted PREHIST report authorized this branch explicitly, and the frozen matrix
row dropped it.

**That recommendation is for the owner and the successor coordinator to accept or
reject. It is not a decision.**
