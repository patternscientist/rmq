# V1 Release-Candidate Fresh-Blind Audit — commissioning prompt

**Status: READY TO LAUNCH.**

## THE COMMIT UNDER AUDIT

> **Tag: `audit-v1-rc-4`** — in `github.com/patternscientist/rmq`.
> Audit this commit and no other. Every `audit-v1-rc-4` below means this commit.

Obtain and verify it:

```bash
git fetch origin --tags
git checkout audit-v1-rc-4          # detached HEAD is expected and correct
git rev-list -n1 audit-v1-rc-4      # the SHA under audit; record it in your report
git status --porcelain              # MUST be empty: a dirty tree is not the candidate
```

Confirm you have the right tree before starting. All four must hold:

| check | expected |
| --- | --- |
| `git rev-parse HEAD` equals `git rev-list -n1 audit-v1-rc-4` | yes |
| `git status --porcelain` | empty |
| `git tag --points-at HEAD` | includes `audit-v1-rc-4` |
| `paper/` exists at the root | yes — it is in scope (`RC-10`) |

If any fails, stop and report it rather than auditing a tree you cannot
identify. The accompanying audit packet was built from this commit; its
`git-log.txt` records the same SHA, so the two can be cross-checked against each
other.

Launching against a moving tree is the specific failure this document exists to
prevent, so **nothing may land between commissioning and the verdict**.

---

## 1. Identity and independence

You are a **fresh-blind exact-commit auditor**. You have not seen this
repository's chat history, worker verdicts, or working trees, and you must not
seek them. You were given exactly two things -- this prompt and the audit packet
-- and the prompt names the commit to fetch. Those, plus the tree at
`audit-v1-rc-4`, are your only inputs.

Follow `docs/internal/AUDIT_PROTOCOL.md`. Report findings at `P0`/`P1`/`P2`/`P3`.

Prefer a different model family from the one that authored the candidate.

**Do not** read `docs/internal/` worker reports, worklogs, or audit reports for
the surfaces you are auditing before forming your own conclusion. They are
process evidence, not proof, and reading them first converts an independent
audit into a review of someone else's reasoning. Read them afterwards only to
check whether a finding is already known.

---

## 2. What is claimed, exactly

Audit these and nothing broader. Each is stated in the form the repository
intends to publish; your task includes deciding whether that form is honest.

**Space and answers.** For every `xs : List Int`, a payload of at most
`2n + o(n)` bits answers every valid half-open query with the leftmost minimum's
index, and rejects invalid, reversed, empty and out-of-range queries.

**Charged-trace cost (U3 lineage).** The canonical reviewer route has a uniform
charged-trace cost of **at most** `210` -- the theorem is
`..._cost_le_principledAllSizeChargedTrace`, an upper budget, and a guarded
invalid query costs zero, so no exact-cost reading is available. Decomposed
`2*35 + (2*11 + 2*37 + 33) + 11 = 210`, with the emitted trace containing only
`readWord` events and non-synthetic certificate weights summing to both trace
length and the `Costed` cost of the same execution.

**Packed cell-probe architecture (Stage A).** One allocated
`header ++ buildPayload ++ padding` packed memory of complete allocated capacity
at most `2n + rho(n)` for checked little-`o`-linear `rho`, answering every valid
half-open query with the leftmost minimum's index in at most `427` attempted
aligned `w(n)`-bit cell probes into that same memory, under a controller whose
dynamic inputs are exactly `n`, the endpoints, and prior probe replies.

**Lower bound.** Any fixed-length payload-only exact RMQ encoding needs
`2n - 1.5 log n - O(1)` bits, in doubled-Catalan-slack integer form.

### Scope the audit must hold the project to

- `427` is an **upper bound derived from the run's own measure**, not an
  attainment claim. The pinned fixture issues 68 probes.
- This is a **cell-probe** result. Computation between probes is free;
  controller dispatch, decoding, arithmetic, comparisons and branching are
  uncharged. It is not word-RAM instruction time, not preprocessing time, not
  measured runtime.
- Preprocessing complexity for the succinct construction is **unproved and
  unclaimed**. (A separate dense-LCA/Fischer–Heun spoke *does* have a proved
  linear build budget — do not report the absence of one as a defect, and do not
  let the repository claim the LCA bound covers the succinct payload.)
- **There are two numerically identical `210`s.** The charged-trace `210` above,
  and the packed controller's structural fuel inside `427 = 1 + 2*3 + 2*210`.
  They are claimed to be provably independent. **Verify that claim rather than
  assuming it**, and check that every surface stating both distinguishes them.

---

## 3. Rows to discharge

For each, reconstruct independently from source at `audit-v1-rc-4`. Do not accept a
docstring, a report, or a ledger row as evidence for the proposition it
describes.

| ID | Requirement |
| --- | --- |
| `RC-01` | The `2n + o(n)` payload bound and exact-answer contract hold as stated, over ordinary `List Int`, with invalid-range behaviour explicit and not weakening the valid case. |
| `RC-02` | The charged-trace `210` chain: the decomposition, the actual-event bridge (weight sum = trace length = `Costed` cost), and the `readWord`-only vocabulary theorem. **U3 is subsumed into this row** by coordinator disposition `WDD-20260807-014`; if you cannot discharge it, say so explicitly, because that disposition is void without it. |
| `RC-03` | The Stage-A capstone: that `packedReviewerArchitectureCapstone_holds` is inhabited for every input and endpoint pair, that its 39 fields say what §2 claims, and specifically that fields 8/9 bound complete allocated capacity and field 39 gives the index. |
| `RC-04` | The `427` cap is genuinely derived and genuinely an upper bound; that attempted (not merely successful) probes are counted; and that probes are aligned fixed-width reads of the *same* memory the space bound measures. |
| `RC-05` | The two `210`s are independent. Adversarial form: try to find any dependency of the packed cap on the charged-trace cost. |
| `RC-06` | The lower bound is coefficient-correct and is not silently compared against the upper bound as if they were the same model. |
| `RC-07` | Trust base: `sorry`-free, standard axioms only, pinned toolchain; the axiom-check scripts genuinely cover the cited declarations rather than a subset. |
| `RC-08` | **Anti-vacuity.** For each headline, check that hypotheses are satisfiable and the statement is not trivially true. Dropping a load-bearing hypothesis should break the proof; if it does not, the hypothesis was decorative. |
| `RC-09` | **Claim honesty across public surfaces.** Every surface in `currentFactSurfacePathRegex` states only what §2 licenses. Report any word-RAM, preprocessing, runtime, or attainment implicature. |
| `RC-10` | The manuscript in `paper/` and its ledgers describe the theorems that exist at `audit-v1-rc-4`, with no claim stronger than its cited declaration. |
| `RC-11` | **Artifact-root correspondence.** Take the theorem `docs/PAPER_CLAIM_CORRESPONDENCE.md` names as the accepted claim and check that importing the paper artifact root actually gives you it. A reviewer asking "which single import yields the paper's theorem?" must get one answer, and the documented identity and the importable identity must be the same string. |

---

## 4. Gates are claims, not evidence

This repository runs several self-checks. **A green gate is not evidence that
the property it advertises holds.** Test each as a claim you are trying to
falsify, and report what you find whether or not it agrees with the gate.

Deliberately, this prompt does not tell you what previous reviews concluded
about these scripts. Supplying those answers would narrow your search to
confirming them.

Gates present at this commit, and what each asserts:

| script | asserts |
| --- | --- |
| `scripts/claim_drift_scan.ps1 -Strict` | no forbidden claim language on the governed surfaces |
| `scripts/constant_sync_check.ps1` | the constants stated in the docs equal the ones Lean proves |
| `scripts/hub_closure_lint.ps1` | the hub layer's import closure reaches nothing RMQ-specific |
| `paper/check_paper.ps1` | the manuscript's citations, labels, ledger coverage and claim language |
| `scripts/gate.ps1` | the aggregate: builds, axiom checks, mutation regressions, the above |
| `scripts/owned_process_tree.ps1 -SelfTest` | the gate's process-ownership layer: that a bounded run's whole tree, descendants included, is dead when the runner says so |

Useful questions for each: what exactly does it match, and what would slip past?
Does it fail when it should — construct an input that ought to trip it? Can it
pass while reporting nothing, or report success after a failure? Does it examine
the files it claims to? Several ship a `-SelfTest`; run it, then try to defeat
the script anyway.

Two notes specific to `scripts/gate.ps1`. It is the required aggregate and takes
well over an hour on some platforms; run it to completion rather than reporting
a partial result, and say which platform you ran it on. Its process-ownership
layer has two implementations -- a POSIX `setsid` process group and a Windows
kill-on-close job object -- and only one of them executes on any given host, so
a green run says nothing about the other. A self-test that cannot create the
condition it checks is required to report itself inconclusive rather than pass;
if you see such a report, treat it as uncovered, not as evidence.

## 5. Deliverable

A report at `docs/internal/audit_reports/<date>_V1_RC_fresh_blind.md`:

1. The exact commit audited and how the packet was obtained.
2. Per-row verdict for `RC-01`..`RC-11`, each with the reconstruction you
   performed — file and line, not a summary of someone else's claim.
3. Findings at `P0`/`P1`/`P2`/`P3`, each with a concrete failure scenario.
4. An explicit statement of what you could **not** verify and why. This is
   required, not optional; an audit with no stated limits is not credible.
5. A verdict: `RELEASE_CANDIDATE_ACCEPTABLE`, `ACCEPTABLE_WITH_FOLLOW_UP`, or
   `NOT_ACCEPTABLE`, with the reasoning.

Do **not** state a verdict you cannot support from source you read yourself.

---

## Declared open at this tag — do not report these unless the RECORD of them is wrong

Every item below is known, measured, and recorded in the design logs. Report one
only if what the repository *says* about it is inaccurate. Anything not on this
list is fair game.

**Never executed.** RC-3 `P2-5` asked for a POSIX `setsid` containment probe and
a decision about descendant tracking. `Invoke-RMQOwnedProcessEscapeProbe` exists
in `scripts/owned_process_tree.ps1`, is reachable only through an explicit
`-EscapeProbe` argument, is deliberately **not** wired into the gate, and **has
never been run**. Its expected Linux outcome is ESCAPED. `WDD-20260816-039`.

**Shape-limited by construction.** `scripts/constant_sync_check.ps1`'s
conflicting-numeral scan can only see conflicts matching a declared claim shape.
`WDD-20260816-042` states that no shape-based detector closes the class.

**The gate roster covers `.ps1` stages only.** `GATE COVERAGE: n of 17` excludes
the eight `RunAxiomCheck` inventories, `independence_check.lean`,
`ledger_decl_check.lean`, the twelve `lake build` targets and steps 2/9 —
under half the gate's stages. `WDD-20260816-059`.

**The axiom directive floor is derived from the source it checks.** Deleting two
of three `#print axioms` directives moves both sides equally and passes; only
total deletion is caught. And its block-comment strip does not nest, so a nested
`/- ... -/` would false-fail (fails closed; no such block exists today).
`WDD-20260816-064`.

**Roster identity uses leaf filenames**, so two same-named scripts in different
directories are indistinguishable. All 25 tracked `.ps1` basenames are unique
today. `WDD-20260816-064`.

**Both claim-drift terms retain pre-v24 repo-wide `allowedLineRegex` tokens.**
Measured at policy v25, these one-word injections into a governed current-fact
surface still pass the strict scan: `novelty`, `policy`, `search` on the novelty
term; `previously`, `historical` on the cap term. `WDD-20260816-058`.

**On a branch-creation push** `github.event.before` is all zeros and the
certification range falls back to `HEAD~1..HEAD` — a one-commit window over an
N-commit push. `DD-20260816-122`. This is not abstract: see the entry below,
which measures what that window is currently concealing.

**Thirteen commits in this candidate's branch history fail the per-commit
certification the candidate ships.** They are `bb15006` `ebdaf22` `29c688b`
`4c56e7e` `aa3d585` `7655ee8` `c9cb19f` `3652d4b` `5c09c5a` `3265987`
`2bd03d8` `9389655` `f8de800` — a fixed set; the branch total was 103 non-merge
commits when last swept and rises with every commit, so the ratio is not the
claim. Measured by sweeping
`design_decision_check.ps1 -Strict` over every non-merge commit in
`$(git merge-base main HEAD)..HEAD`. All 13 are ancestors of this tag. Three
causes, of which the largest is the checker's own: `paper/` matches no
workflow root and the classifier reads `needsCode = -not needsWorkflow`, so a
whole directory of prose defaulted into proof/code architecture (7 commits);
`RC1_CORRECTION_HANDOFF.md` is absent from the neutral-evidence list, so ticking
a checkbox demands a design decision (3); and `.lean` under `scripts/` requires
both ledgers, one of which was written (3). Measured in a scratch worktree:
correcting the classifier certifies **5** of the 13, not more — the remaining 8
fail on `paper/rmq.tex`, `paper/references.bib`, `paper/check_paper.ps1` and
`scripts/*.lean`, where the check is arguably right. `WDD-20260817-077`.

This does **not** block integration, and the earlier draft of this entry was
wrong to imply it did. This repository integrates by squash-merge — main's last
200 commits hold 3 merges (all 2026-07-24) against 197 non-merges, and both
recent integrations, `a0402e1` (Stage A) and `0f38672` (ALLSIZE-R1), are
single-parent. Measured: squashing this branch onto `main` applies conflict-free
and certifies — 92 files (55 code, 40 workflow, 2 neutral), strict exit 0. On
that path the 13 never reach main.

They surface on one path only: `ci.yml` also triggers on `pull_request`, whose
range is `origin/main..HEAD`, so a PR from this branch enumerates all 101 and
goes red. Repair means rewriting history, which would discard this tag and its
GATE PASS, so it is recorded rather than performed. `WDD-20260817-075` carries
the full table and `WDD-20260817-076` the integration measurement. **Reporting
this is not a finding — reporting that the numbers or the causes are wrong is.**

**Content introduced by a merge alone** — a conflict resolution present in
neither parent — is certified by nothing, now that the enumeration excludes
merges. The alternative was judging a merge by the union of its parents, which is
the aggregate question the per-commit check exists to replace.
`DD-20260816-125`.

**Dynamic invocation is pinned, not resolved.** `& $variable` cannot be decided
statically. The raw-call walk records such targets and allows exactly one
(`$Path`, `Invoke-Checker`'s own dispatch); a new one is reported for review
rather than resolved. `WDD-20260816-069`.

**`scripts/paper_root_measure.ps1` does not exist.** The program plan schedules it
and says so.

**The program plan's own audit is separate.** `docs/internal/RMQ_PROGRAM_PLAN.md`
and `PLAN_LINEAGE.md` are tagged and commissioned independently as
`audit-plan-v14`; they are not in scope here.

### What twelve internal rounds did and did not establish

Twelve fresh-blind agent audits preceded this tag. No round found a defect in a
kernel-checked theorem. Rounds 7–9 found defects in the release-facing checkers;
rounds 10–12 found them almost entirely in the fixes made during the loop, and
the last six rounds returned **zero P1**. The loop was stopped when its subject
had migrated from the artifact to the apparatus checking it — not because the
apparatus is complete, which is why the list above exists.

Three findings from those rounds were themselves wrong and were rejected on
measurement rather than adopted. If you believe something here is wrong, measure
it; a report that reproduces is worth more than one that is merely plausible.
