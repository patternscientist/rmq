# Coordinator record: Stage-A closure through the V1 release candidate

**Range:** `a0402e1` (Stage-A integration) .. the commit tagged **`audit-v1-rc-1`**,
the release candidate. 29 commits; the measured delta at `bdb79bf` (25 commits
in) was 83 files, +20,830 / −14,182.

## 0. What this document is for, and when to read it

This is a **coordinator reconstruction packet**, to be read *after* the
fresh-blind release-candidate audit returns, not before. Its purpose is to let
the coordinator answer one question: *does the audit's verdict actually cover
what changed, and is anything the audit did not look at still load-bearing?*

It is deliberately **not** given to the auditor. The auditor gets
`V1_RELEASE_CANDIDATE_AUDIT_PROMPT.md`, the exact commit, and the packet.
Handing them this document would convert an independent audit into a review of
the worker's own account of events.

Read §7 first when the audit lands. Everything above it is context for §7.

---

## 1. The starting point: what Stage A established

Stage A was recorded `ACCEPTED` on 2026-08-07 after a fresh-blind exact-commit
audit (report `60827a1`, merge-ready with follow-up, no `P0`/`P1`) and a
coordinator reconstruction in which every finding was independently reproduced
before disposition. The `P3-3` gap was repaired by amendment `CA-20260807-001`,
adding field 39, and re-certified.

The accepted claim, unchanged since and repeated verbatim here because
everything in §7 is judged against it:

> For every input list, one allocated `header ++ buildPayload ++ padding` packed
> memory of complete capacity `2n + o(n)` answers every valid half-open query
> with the leftmost minimum's index, in at most `427` attempted aligned
> `w(n)`-bit cell probes into that same memory, under a closed controller whose
> dynamic inputs are exactly `n`, the endpoints, and prior probe replies. `427`
> is an upper bound derived from the run's own measure, not an attainment claim;
> `210` is logical fuel; this is a cell-probe result and not word-RAM
> instruction time, preprocessing time, or a measured-runtime claim.

**No commit in this range strengthens, weakens, or restates that claim.** Every
proof-surface change preserved public statements byte-identically; the claim
changes only in where and how honestly it is *described*.

---

## 2. What changed, by intent

### 2a. Proof-surface reduction (`def5cb3`, `24bc22d`, `eadbb61`, `ffe7d9f`, `4f329f4`, `745a3c5`)

Nine unreachable modules deleted; 2,276 lines of dead declarations removed;
~900 lines of duplicated proof collapsed into delegations;
`InteriorDirectory.lean` split 7,419 lines into three modules behind a 13-line
hub. `PayloadMacro.lean` 3,346 → 2,441; `RelativeMerge.lean` 1,291 → 87.

Decisions: `DD-081`, `-082`, `-083`, `-084`, `-086`, `-089`.

The de-duplication was justified *before* editing, not by trial: each shared
lemma's conclusion was diffed against the hypothesis slot it would fill —
39 lines against 39, zero token differences, the sole difference a trailing
delimiter. The split was justified by showing **zero of 25 private declarations
cross a seam**, so no promotion was forced, and by the structural argument that
Lean requires definitions to precede uses, making the import chain sound by
construction.

### 2b. Claim honesty (`638d3da`, `b71db99`, `e3362d4`)

Five public over-claims corrected; the single offending Lean docstring fixed;
`PAPER_THEOREM_MAP.md` and `PAPER_CLAIM_CORRESPONDENCE.md` synchronized to the
accepted theorem, having previously described a July theorem in August.

Decisions: `DD-087`, `-088`, `-090`.

### 2c. Manuscript substrate (`bb15006`..`a54088b`)

`paper/` merged: manuscript, theorem ledger, related-work ledger, evidence
matrix, **novelty log**, hardened checker. Two statements in `rmq.tex` were
**false**, not stale, and were retracted. The novelty search retired twelve
candidate claims with primary-source receipts.

Decisions: `DD-091`, `WDD-016`.

### 2d. Governance and gates (`7763348`, `b65ef88`, `52e6b0f`, `a3ba169`, `c14d7a5`, `8a37b5a`)

U3 disposed by subsumption after its pin was found broken; hub import-closure
lint added; constant-sync check added; union-find cordoned; independent-check
procedure documented.

Decisions: `DD-085`, `-092`, `-093`; `WDD-014`, `-015`, `-017`, `-019`, `-020`,
`-021`.

---

## 3. Findings that changed a conclusion

These are the substantive results of the period. Each overturned something the
project previously believed.

| Finding | Prior belief | Established by |
| --- | --- | --- |
| **U3's pin named an off-main commit proving a *retired* numeral.** `880dfdf` is not an ancestor of `main` and proves `= 76`; `main` proves `= 210`. Path 1 (audit that commit) was therefore not executable. | U3 awaited a fresh-blind audit of a named candidate | `git merge-base`, `git show` on each commit in the lineage; every numeral read from its own commit (`76 → 142 → 207 → 210`) |
| **Two numerically identical `210`s** sit on the release path — the charged-trace cost and the packed controller's structural fuel inside `427 = 1 + 2*3 + 2*210` — and are provably independent. | implicitly one quantity | grep of `PackedCellProbe/`: zero references to `queryCost` or `nonSyntheticWeight` |
| **A linear preprocessing bound exists** for the dense-LCA spoke (`denseLCA_linearBuild_constantQuery_profile`), though not for the succinct payload. | preprocessing wholly unproved | `docs/ROADMAP.md:311-331` |
| **"Our novelty is the machine-checked asymptotic `o(n)`" is dead**, and so is any "first machine-checked query-cost bound": JIP 2018 §6.5.2 already machine-checks succinct query cost in Coq. | the repository's stated novelty framing | primary source; the JIP PDF was fetched and read, lemmas `RankInitNumBitsExamined` / `RankLookupNumBitsExamined` confirmed on page 67 |
| **The blanket deferral of all nine file splits was wrong for one file.** | module-scoped `private` forces promotions in every case | per-file measurement: 0 of 25 privates cross a seam in `InteriorDirectory` |
| **ITP 2026 has already run** (26-29 July 2026, LIPIcs vol. 382), so the target is ITP 2027 and the runway is longer than the roadmap assumed. | an imminent deadline | the ITP 2026 site |
| **An anonymised artifact is REQUIRED, not optional**: the call requires "anonymised supplementary material containing verifiable evidence of a suitable implementation". The DOI must therefore not be cited in the submission. | anonymity treated as an open nicety | the ITP 2026 call for papers |

---

## 4. Gate claims that were false, and are now checked

Twice in this period a gate was found to be weaker than it advertised. Both are
recorded because the pattern matters more than the instances: **a green gate was
cited as evidence for a property the gate did not establish.**

- **`paper/check_paper.ps1`** printed "all refs resolve" *unconditionally*,
  immediately after reporting an unresolved ref. Its multi-word patterns were
  matched only against raw text while `rmq.tex` is hard-wrapped, so a banned
  phrase split across a newline evaded it — demonstrated by injection. Its
  ledger-status guard compared totals and could not see a row losing its status.
  All fixed; `-SelfTest` now runs 16 detector cases. **Decisive check:** on
  identical input, the pre-hardening checker exits 0 where the current one
  exits 1.
- **`claim_drift_scan.ps1`** guarded every *retired* constant and neither
  *current* one. Closed by `scripts/constant_sync_check.ps1` (gate step 7b).
  **Decisive check:** with the Lean bound moved `210 → 214`, the new script
  exits 1 naming both values while `claim_drift_scan -Strict` reports
  `0 strict failures` and exits 0.
- **`RMQHub.lean`'s docstring claim** ("imports only modules that do not depend
  on RMQ ranges, Cartesian shapes, Euler tours, or any RMQ backend") was true
  but enforced by nothing. Closed by `scripts/hub_closure_lint.ps1` (step 5b),
  verified by injecting `import RMQ.Core.Spec` into the real `ModelHub.lean`.

---

## 5. Defects in this work, self-reported

Recorded so the coordinator can weigh the account, not to be exhaustive about
process.

1. **The refactor wave invalidated the Stage-A audit.** Ten commits landed on
   the tree that audit certified, five restructuring proof surface. The
   mathematics is unaffected — statements byte-identical, all gates green — but
   the freeze requires an audit *of the exact candidate*, so a new one is
   needed. This should have been flagged when the refactor began.
2. **The same refactor left eight dead paths in `CODE_MAP.md`**, found later
   rather than at the time.
3. **A drafted claim repair was itself false.** "Preprocessing cost is not
   bounded by this development" was written, then caught: the dense-LCA spoke
   has a proved linear build budget. Erring toward modesty is still erring.
4. **The union-find cordon was attempted, corrupted, and reverted** to a
   byte-identical tree after three sequential CRLF errors; a fourth occurred
   later on a docs edit. Nothing was committed in a broken state. The rule is in
   `DD-20260808-092`: never regex-anchor on this repository's files; verify the
   *effect*, not the exit status.
5. **The first version of a checker rule was vacuous.** The record-surface
   allowance included a quote character, which ordinary prose always supplies,
   so a bare priority claim in the novelty log passed. Found by injection, not
   by reading; three self-tests now hold that line.

---

## 6. Verification standard applied throughout

- Every commit: full local gate (~82 min) **and** both CI workflows green.
- Every rebase re-ran CI: a changed SHA no longer certifies what lands.
- Every landing was a verified fast-forward.
- New gates were verified by **injection against the real tree**, then restored
  byte-identical — not by unit test alone.
- Two full `lake build` runs backed the de-duplication (767 s, 770 s); the
  cordon build was 675 s with `union_find_axiom_check` clean on all 174 pinned
  declarations and the full axiom check clean in 212 s.

---

## 7. What the coordinator must check when the audit returns

This is the operative section.

1. **Does the audit's scope match this range?** The auditor is asked to
   discharge `RC-01`..`RC-10`. Confirm that `RC-02` was actually discharged: the
   U3 disposition (`WDD-20260807-014`) is **void without it**, because
   subsumption was chosen precisely on the grounds that the release audit would
   carry those propositions.
2. **Did the auditor test the new gates rather than trust them?** §4 of the
   prompt asks them to try to defeat `constant_sync_check`, `hub_closure_lint`
   and `check_paper`. A verdict that cites these as green without probing them
   has not covered the most recently added surface.
3. **Did the auditor confirm the two `210`s are independent**, or assume it?
   `RC-05` is adversarial by design. An unexamined "yes" here is weaker than a
   stated inability to check.
4. **Does the report state its limits?** Required by §5.4. An audit with no
   stated limits should be treated as incomplete regardless of verdict.
5. **Cross-check the findings against §5 of this document.** If the auditor
   independently found one of the five self-reported defects, that is
   corroboration. If they found something in §3 that this record calls settled,
   that is the important case and this record is what is wrong.
6. **Confirm nothing landed after the audited SHA.** If anything did, the audit
   no longer certifies the candidate and the freeze order has been broken again.

---

## 8. Open at `bdb79bf`

- **DOI and anonymity — resolved 2026-08-08** (`DD-20260808-094`) by reading
  the venue's own call. An anonymised artifact is **required**; ITP 2026 has
  already run so the target is ITP 2027; and the DOI must not be cited in an
  anonymous submission, so it belongs to the public release and camera-ready.
  Minting it remains an action on the owner's identity and is left to them.
  Anonymisation tooling is deliberately **not** built yet: on an ITP 2027
  timescale there is no reason to freeze that choice now.
- **Venue fit is coupled to E1.** An external expert independently recommended
  ITP as best fit with CPP as a secondary, matching this project's own analysis.
  But their premise included "a compiled small ISA machine to make the cost
  claim operational" -- that is E1, which is **not done**; controller dispatch,
  decoding, arithmetic and branching remain uncharged. Both of the secondary
  suggestions (CPP, and PL venues "if framed correctly") lean on exactly that
  operational angle, which is the same condition `PUBLICATION_STRATEGY.md`
  already attaches to CPP. ITP is the recommendation that holds for the artifact
  as it stands.
- The remaining `V1_RELEASE_CANDIDATE_AUDIT_PROMPT.md` §0 boxes are launch
  mechanics: choose `audit-v1-rc-1`, confirm green, build the packet.
- Deferred with reasons recorded: the `RankSelect` and `BPNavigation` cordons
  (§7 of the prompt; `BPNavigation` has 195 frozen Stage-F fixtures pinning its
  import path), the remaining eight file splits, and an executed
  independent-kernel re-check.
