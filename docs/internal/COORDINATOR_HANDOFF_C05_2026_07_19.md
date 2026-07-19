# RMQ Coordinator Handoff — C05, 2026-07-19

Written mid-campaign with three workers in flight, ahead of a merge wave.
Supersedes nothing; the durable audit record is the round log in
`AUDIT_AND_A_DESIGN.md` (C05 rounds 1-15).

## Repo

- Path: `C:\Users\poin\Documents\RMQ`
- Coordinator branch: `claude/rmq-formalization-coordinator-bd7045` (round log
  only; no Lean)
- Campaign branch: `claude/b1-b2-charged-fringe-tables`
- `main`: `4a60853` — the B campaign is NOT merged to main
- Workflow-governance ref: `5f59455e62fc26e881fbd722834c33b615d2c914`
  (12 commits ahead of main on `codex/rmq-prompt-readiness-hardening`, still
  unmerged; content-safe but `2c30a3a` touches `gate.ps1` and WDD-003/006 are
  automation-authority grants that want an explicit user nod)
- Runtime: Claude. `.claude/skills/rmq-{coordinator,proof-sprint,audit}` are
  thin wrappers deferring to the canonical `.agents/skills` packages
  (WDD-20260717-C05-001). `scripts/project_skill_preflight.ps1` fails
  structurally on this runtime; operating as the user-authorized disclosed
  fallback, which cannot record ACCEPTED or roadmap closure.

## What this campaign changed

The accepted RMQ query route was rebuilt so that every charged trace event is a
memory read and no uncharged computation's cost grows with input size. Rungs:
B2 (charged fringe via o(n) four-Russians chunk tables), B3 (in-word
rank/select recharged; **readWord-only vocabulary theorem**), B4 (provenance
hardening), B6 (same-block leg — the last silent scan found at the time), and
B7 (in flight, the sparse level). The literal moved 76 -> 142 -> 207, each
predecessor frozen as a named historical constant; B7 will move it to 210.

## Unmerged branches (merge wave pending)

| Branch | Commit | Status |
|---|---|---|
| `claude/b1-b2-charged-fringe-tables` | `c52e91b`+ | B0-B6 candidate-complete and coordinator-reconstructed; E1 machine rung in flight |
| `claude/b7-charged-sparse-level` | `0993c02`+ | B7 in flight; mechanism + cost settled, implementation underway |
| `claude/a07-blocker-repairs` | (Codex R1) | A07 blockers + validator fixture; in flight |
| `codex/a07-option-b-charged-route-audit` | `bb76860` | A07 blind audit report, REJECT, findings all accepted |
| `codex/v1-s01-independent-verification-scout` | `f218b98` | V1 scout report, accepted |
| `codex/m1-reviewer-native-machine-adequacy-r4` | `947bde5` | M1 candidate; gate passed; NOT accepted; registry needs refresh after the campaign |
| `codex/e1-fully-charged-small-step-machine-r3` | `7fe5b8b` | Kernel-verified obstruction to the SUPERSEDED E1 target; preserve as evidence, do not merge as closure |

**Merge order when the three active branches land:** B7 first (it changes the
route literal and the interior leg), then a07-repairs (scripts/docs/witnesses),
then the campaign branch (E1 machine modules are additive but simulate the
route B7 changes). Expect the E1 interior-leg work to be re-derived against
B7's amended trace — that is planned, not rework.

## Theorem frontier

Closed and reconstructed: charged fringe/rank/select/same-block legs; the
readWord-only vocabulary theorem; derived literal 207 from a named component
algebra; payload erasure and `<= 2n + o(n)` shape preserved; W19 provenance
extended to the new table sources; corruption witnesses at component level.

Open: the sparse level (B7); the E1 whole-query glue, derived step literal,
amended-target Prop, and matrix closure (all downstream of B7); the
answer-level value-dependency theorem (A07 P1-2, assigned to R1); the
top-level same-block occurrence witness (A07 P1-3, R1); `instrPos` disequality
(A07 P2-1, R1); the allocated-cell space theorem (queued as a strengthening,
not a blocker).

## Verification standards — learned the hard way, do not relax

1. `lake build <root>` is BINDING. Per-file `lake env lean` is an iterate aid
   only: it reports clean on code accidentally commented out, and writes no
   olean (so `#print axioms` says `unknown constant` for fresh names).
2. Confirm each claimed theorem with `#print axioms` after a root build.
3. The coordinator runs full `gate.ps1` at every RUNG boundary. Deferring it to
   "integration" let a stale identifier survive four rungs.
4. Any rung renaming/retiring an identifier MUST run both axiom inventories.
5. Any rung changing the accepted TRACE must re-run every executable fixture
   that indexes trace positions (this is how the validator regression happened).
6. Worker-reported check results are ATTESTATION. A session logged
   `wordram_axiom_check` as exit 0 when it deterministically exits 1;
   coordinator re-ran it and observed exit 1. Paste decisive output lines.
7. Anti-vacuity bar for machine work: do not merely HOST a block — execute
   both branches onto distinguishable halts. A theorem about a branch target
   past the end of a program is true and worthless.

## Principles established (paper-facing)

- **Representation artifact vs algorithmic work.** A Lean-level traversal is an
  artifact when its value is checked-equal to an input parameter or a charged
  read (`occurrenceCount shape.bpCode false = shape.size`; `localBPWindowBits`
  -> four charged reads; `queryOccurrence`, `queryPos`, `machineWordBits`). It
  is algorithmic work needing a charge when it computes the ANSWER or an
  ADDRESS from runtime data (B2 fringe scan, B6 same-block scan, B7 sparse
  level). State it with named bridge lemmas, never as an absolute.
- **The distinction is the operand, not the operation.** `blockSize =
  2*(log2 shape.size + 1)` is shape-determined and an encodable immediate; the
  interior `Nat.log2` applies to a runtime count feeding a read address.
- **A green check is evidence only of what it examined.** Prefer the check that
  fails loudly over the one convenient to run.
- **Diff receipts, not verdicts.** A back-edge mutation preserved program
  length and reached the correct exit pc; only event-by-event receipt diffing
  caught it.

## Outstanding user decisions

1. Governance-branch merge to main (`2c30a3a` gate edit; WDD-003/006 authority).
2. **B5b**: alias consolidation (~50 public aliases -> ~6) and pruning the
   compatibility surface from the shipped artifact. Public-surface removal;
   needs explicit sign-off.
3. When to record formal ACCEPTED for M1-01R4 and the B rungs (blocked on the
   disclosed-fallback constraint above).

## Highest-value remaining work, ranked

1. Finish B7, then E1's interior leg, glue, and closure ladder.
2. Land R1's four A07 blockers and the validator fixture.
3. **The complete uncharged-computation inventory** (set as B7's stretch goal):
   enumerate every uncharged computation reachable from the accepted route,
   each classified artifact-or-charged with its bridge lemma. Three instances
   of the defect class were each found by a different accident; an enumeration
   converts luck into coverage and is the single best artifact for reviewer
   confidence.
4. Re-run A07 (or a fresh blind auditor, cross-family) at the post-merge commit.
5. V1: Linux CI portability (`project_skill_preflight_regression.ps1:38` invokes
   `powershell`, absent on Ubuntu; `Join-Path`; drop `GIT_CONFIG_GLOBAL=NUL`),
   and pin the exporter + working Nanoda commit — Nanoda already checked all
   6,643 declarations of the canonical headline closure with no errors.

## Do not work on next

- Merging any branch before B7 lands (the literal is mid-migration).
- E1's whole-query glue or derived literal before B7 (they consume the trace
  B7 is changing).
- Alias consolidation or compatibility pruning without user sign-off.
- Re-auditing the campaign's mathematics; it survived a cross-family blind
  audit and an independent kernel check. Audit the CLAIM-TO-EVIDENCE gaps.

## Warning signs for the next coordinator

- Line numbers drift constantly. Verify REACHABILITY of a cited site, not just
  its existence — C05 propagated four wrong site citations from a worker report
  and a scout caught it.
- Two near-homonyms differ by one suffix 60 lines apart:
  `concreteBPNativeLCACloseGlobalWordTraceResult` (legacy) vs
  `...AllSizeStructural` (accepted, used by the route). A `Legacy` rename is
  queued and is the highest-value naming repair.
- Matrix rows marked Closed on process attestation are a recurring finding;
  keep them visually distinct from kernel-checked rows.
