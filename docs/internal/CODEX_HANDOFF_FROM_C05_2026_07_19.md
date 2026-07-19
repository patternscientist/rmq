# Handoff to Codex from coordinator C05 — 2026-07-19

Everything in this document is **outside the substance of E1**. C05 is staying on
E1's remaining proof work; these are integration, documentation and tooling items
that are ready to act on. Each is self-contained — you should not need the C05
session transcript.

**Standing constraints that still apply:** no weakened acceptance rows; no
renamed or deleted frozen public identities; no asserted constants; frozen
requirement text is never edited (append a NOTE) except by owner-approved
amendment; builds green at every commit.

---

## 1. Merge `main` into the E1 campaign branch — HIGHEST VALUE, DO FIRST

`main` is `0b8490c` (B7-R4 repairs, R1-R4 lineage, A08 audit integrated). The E1
campaign branch `claude/b1-b2-charged-fringe-tables` diverged at `d5a9355`, a B7
session-10 commit, so it carries an **earlier, pre-audit B7**. The divergence
should be closed so E1's eventual acceptance is against current `main`.

**C05 already verified the merge is safe. Do not redo this; verify it if you
want, but the findings are:**

- `queryCost_eq : queryCost = 210` is **identical** on both branches.
- `InteriorDirectory.lean` is **+715 insertions, ZERO deletions** since the
  merge-base — purely additive — and the nine route computations the whole E1
  interior leg targets are at **identical line numbers** on `main`: `2300`,
  `2311`, `2329`, `2351`, `2376`, `2400`, `2413`, `2426`, `2444`.
- `concreteBPNativeLCACloseGlobalWordTraceResultAllSizeStructuralWithStore_globalReadStore`
  is still at `SuccinctFinalStoreParam.lean:1633`.
- Present on `main`: `queryTraceResult_valid`, `queryCosted_invalid`,
  `cartesianShape`, `prepareInput_shape_eq_cartesianShape`,
  `bpChunkedRankTraceResultWithStore_store_parametric`,
  `concreteBPNativeRankCloseWordTraceResultAtSegment_canonical_eq`, and
  `listInt_flatPayloadStore_noSynthetic_two_n_plus_o_execution_story`.
- The only deletions in `SuccinctRMQClassic.lean` touch
  `canonicalTransitionalQueryCost = 352`, a frozen HISTORICAL constant E1 does
  not use.

**Coordination requirement:** the campaign worktree
(`.worktrees/b2-charged-fringe`) has live C05 lanes in it intermittently. **Ask
C05 for a quiet window before merging**, or work in a fresh worktree off the
campaign head and hand back a merge commit. A worktree is a single-writer
resource and merging under a live lane has already cost this campaign one
verification run.

There is also an unmerged C05 branch `claude/e1-cost-algebra` (cost-algebra
lane). Do **not** merge that one — C05 owns its lifecycle.

**After merging, run the full battery** and note that
`design_decision_check.ps1` **examines nothing and exits 0 without `-Base`** —
always pass `-Strict -Base <merge-base>`. Also: piping a PowerShell script
through `tail` reports TAIL's exit status, not the script's; use
`powershell -Command "& { & '<script>' <args>; exit $LASTEXITCODE }"`.

---

## 2. Paper-facing numeral migration `207` -> `210` — the public surface is
## currently self-contradictory and no gate catches it

`207` at HEAD names a **retired route**
(`concreteBPNativeSuccinctRMQSilentSparseLevelChargedTraceCost`). The live bound
is `210`, migrated by commit `f6000c3`. The algebra is
`2*select35 + (2*rank11 + 2*endpointFringe37 + interior33) + rank11 = 210`, with
`closeLCA = 129`.

**`README.md` is internally inconsistent at HEAD**: `:76` calls a paper-facing
theorem "charged-trace cost at most `207`" while `:80` cites the
`...SumLe210` identifier. Also stale at `:70`, `:140` ("current charged-trace
cap"), `:334`.

**`docs/FAMILY_SUMMARY.md` still carries the PRE-B7 algebra** — `:9` reads
`2 * select35 + (2 * rank11 + 2 * endpointFringe37 + interior30) + rank11 = 207`
— plus `:43`, `:48`, `:133`, `:446`, `:1041`.

Already migrated and needing no work: `docs/WHAT_IS_PROVED.md`,
`artifact/CLAIMS.md` (its `:31` even carries the correct decomposition), and
`docs/PAPER_MODEL_ADEQUACY.md`.

**Neither gate catches this.** `docs/internal/CLAIM_DRIFT_POLICY.json` has **no
term for `207` or `210`** (verified by grep), and `scripts/paper_topology_lint.ps1`
anchors on IDENTIFIERS, not prose numerals — so both exit 0 while the README
asserts a superseded cap. **Add a `207`/`210` term to the drift policy** so a
recurrence is caught, and note that the policy's existing
`principled-charged-trace-76` term's `status` string still describes `76` as
"current", which is itself stale.

Do **not** touch the frozen historical constants themselves (`207`, `142`, `76`,
`328`, `352`) — they are pinned to literals in `SuccinctFinalRAM.lean` precisely
so no later recharge can rewrite history.

---

## 3. REQ-E1-09's stated checks are aimed at yesterday's defects — append a NOTE

The row instructs fixing four "fresh segment 21" public surfaces
(`README.md:94`, `docs/WHAT_IS_PROVED.md:14` and `:95`, `artifact/CLAIMS.md:68`,
`docs/PAPER_MAIN_THEOREM.md:60`) — **all of these already read `23` at HEAD**,
matching `concreteBPNativeSuccinctRMQFreshUnusedCanonicalSource`. It also
instructs fixing a 33-cap file attribution in `PAPER_MODEL_ADEQUACY.md:152-155`
— **already correct**.

Meanwhile the genuinely stale numerals in item 2 above are named by no row and
caught by no gate.

Frozen requirement text is not edited: **append a NOTE** recording that those
two instructions were satisfied before the rung began, and that the live
documentary defect is the `207` migration instead.

---

## 4. The two distinct `33`s have never been flagged — append a NOTE

The campaign shorthand "the caps 33/8/8" conflates **three** different values:

| Value | Object | Anchor |
|---|---|---|
| 33 | fringe-window chunk-read cap — lives INSIDE `endpointFringe = 4 + 33 = 37` | `ChargedFringeChunks.lean:1624-1687` |
| 33 | whole-interior-directory read cap, `canonicalRelativeRmmPrincipledInteriorChargedTraceCost` | `InteriorDirectory.lean:1934` |
| 33 | coincidence: `3 * rankClose` | — |
| 8 | per-machine-word fringe chunk cap | `ChargedWordChunks.lean:39` |
| 8 | interior table adapter per-read chunk cap | `InteriorDirectory.lean:4511` |

The two `8`s were flagged as distinct in an existing M3d-11 note. **The two 33s
never were**, and they are the more dangerous pair because one sits INSIDE the
other's sibling term in the same algebra. Any text written to REQ-E1-07's literal
"33/8" wording will conflate them.

---

## 5. Deferred tooling items, lowest priority

- **`design_decision_check.ps1` matches by ENUMERATION**, so its coverage is
  exactly the list someone remembered to write. C05 already added
  `^RMQ/Validation` (WDD-20260719-002) after it exited 0 over a candidate
  carrying five design decisions. The better long-run shape is a denylist so
  coverage is opt-out; recorded as a candidate cleanup, deliberately not done in
  a repair commit.
- The `Legacy` naming repair and the M1-registry refresh, both previously
  deferred to a merge window.

---

## What C05 is keeping

E1's remaining proof substance only: the whole-query layout repair and its
executed confirmation, the interior trace ladder, result agreement, positional
receipt equality, category accounting across all four branches, discharging
`WholeQueryMachineAgrees`, the `none`-branch discriminator, the composite
category-log bounds, the fringe fold's unexecuted preservation clause, and the
acceptance-matrix adjudication.

**One item may need the project owner rather than either of us:** `ProgramFits`
at a log-based width is **false at small shapes** (register file reaches `152`;
at `n = 4` the bound is `2^3 = 8`), which may make REQ-E1-02 unsatisfiable as
literally worded. C05 has a lane evaluating it to produce numbers before anyone
decides. Do not act on this one.
