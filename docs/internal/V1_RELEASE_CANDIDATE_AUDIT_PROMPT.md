# V1 Release-Candidate Fresh-Blind Audit — commissioning prompt

**Status: READY TO LAUNCH.**

## THE COMMIT UNDER AUDIT

> **Tag: `audit-v1-rc-3`** — in `github.com/patternscientist/rmq`.
> Audit this commit and no other. Every `audit-v1-rc-3` below means this commit.

Obtain and verify it:

```bash
git fetch origin --tags
git checkout audit-v1-rc-3          # detached HEAD is expected and correct
git rev-list -n1 audit-v1-rc-3      # the SHA under audit; record it in your report
git status --porcelain              # MUST be empty: a dirty tree is not the candidate
```

Confirm you have the right tree before starting. All four must hold:

| check | expected |
| --- | --- |
| `git rev-parse HEAD` equals `git rev-list -n1 audit-v1-rc-3` | yes |
| `git status --porcelain` | empty |
| `git tag --points-at HEAD` | includes `audit-v1-rc-3` |
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
`audit-v1-rc-3`, are your only inputs.

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

For each, reconstruct independently from source at `audit-v1-rc-3`. Do not accept a
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
| `RC-10` | The manuscript in `paper/` and its ledgers describe the theorems that exist at `audit-v1-rc-3`, with no claim stronger than its cited declaration. |
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
