# V1 Release-Candidate Fresh-Blind Audit — commissioning prompt

**Status: READY TO LAUNCH.** Every precondition in §0 is discharged.

## THE COMMIT UNDER AUDIT

> **Tag: `audit-v1-rc-1`** — in `github.com/patternscientist/rmq`.
> Audit this commit and no other. Every `audit-v1-rc-1` below means this commit.

Obtain and verify it:

```bash
git fetch origin --tags
git checkout audit-v1-rc-1          # detached HEAD is expected and correct
git rev-list -n1 audit-v1-rc-1      # the SHA under audit; record it in your report
git status --porcelain              # MUST be empty: a dirty tree is not the candidate
```

Confirm you have the right tree before starting. All four must hold:

| check | expected |
| --- | --- |
| `git rev-parse HEAD` equals `git rev-list -n1 audit-v1-rc-1` | yes |
| `git status --porcelain` | empty |
| `git tag --points-at HEAD` | includes `audit-v1-rc-1` |
| `paper/` exists at the root | yes — it is in scope (`RC-10`) |

If any fails, stop and report it rather than auditing a tree you cannot
identify. The accompanying audit packet was built from this commit; its
`git-log.txt` records the same SHA, so the two can be cross-checked against each
other.

### Why a tag and not a SHA in this file

A SHA cannot name the commit that contains it — writing one in moves the tip and
leaves the document pointing at its own parent. A tag is applied after the
commit exists, so it names the candidate exactly, and the tag can be moved
without this file going stale.

The tag deliberately does **not** begin with `v`.
`.github/workflows/release-artifact.yml` triggers on `push: tags: v*` and calls
`gh release create`, so a `v`-prefixed tag would publish a public GitHub
Release. An audit checkpoint is not a release, and publishing one here would
also pre-empt the still-open DOI decision, since a GitHub Release is what a DOI
would be minted from.

Launching against a moving tree is the specific failure this document exists to
prevent, so **nothing may land between commissioning and the verdict**.

---

## 0. Preconditions the coordinator must satisfy before launching

The freeze's terminal requirement is a fresh-blind audit **of the exact release
candidate**. The previous Stage-A audit no longer certifies anything shippable:
it targeted `ec35b5d9`, re-certified at `a8d2a5c`, and **ten commits** have
landed since, five of which move, delete, or restructure proof surface —
deleting nine modules, removing 2,276 lines, relocating theorems, replacing
proof bodies, and splitting a module. Every one of those preserved public
statements byte-identically and passed the gate and CI, so the mathematics is
unaffected; the *process* requirement is not.

The consequence sets the launch order: **any tree-touching change after the
audit invalidates it again.** All of the following were satisfied before
`audit-v1-rc-1` was tagged:

- [x] `codex/eg-cp-paper-evidence-r1` merged at `a54088b` on 2026-08-07: the
      manuscript substrate, its hardened checker, and the novelty log. `paper/`
      is now part of the release candidate, so the auditor must treat it as an
      in-scope claim surface (`RC-10`) rather than as an external draft.
- [x] Union-find cordon **landed** at `8a37b5a` (2026-08-08). The spoke is now
      `VerifiedDS.UnionFind` and `RMQ/Core/UnionFind/` no longer exists. Expect
      the neutral name; `RMQUnionFind.lean` is a compatibility shim.
- [x] Every V1 gap intended for this cycle is closed or explicitly
      dispositioned; §6 records each with its commit.
- [x] `audit-v1-rc-1` is on `main`, both CI workflows are green on it, and
      `scripts/gate.ps1` exits 0 on it (zero issues).
- [x] The audit packet is built from `audit-v1-rc-1` with
      `scripts/make_audit_packet.ps1`, reporting `AUDIT-PACKET: RESULT: PASS`.

### What to hand the auditor

**Exactly two things: this prompt and the audit packet.**

The commit is not a third item. It is named in this document -- tag
`audit-v1-rc-1` -- with the commands to fetch and verify it, so an auditor
holding the prompt can obtain the candidate themselves. Keeping the commit
inside the prompt rather than alongside it removes the failure where a SHA is
communicated separately, out of band, and drifts from the document that
describes what to do with it.

**Nothing else.** In particular *not*
`docs/internal/COORDINATOR_RECORD_STAGEA_TO_V1RC.md`, which is the coordinator's
own account of this period; giving it to a fresh-blind auditor would convert an
independent audit into a review of that account.

---

## 1. Identity and independence

You are a **fresh-blind exact-commit auditor**. You have not seen this
repository's chat history, worker verdicts, or working trees, and you must not
seek them. You were given exactly two things -- this prompt and the audit packet
-- and the prompt names the commit to fetch. Those, plus the tree at
`audit-v1-rc-1`, are your only inputs.

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
charged-trace cost of `210`, decomposed
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

For each, reconstruct independently from source at `audit-v1-rc-1`. Do not accept a
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
| `RC-10` | The manuscript in `paper/` and its ledgers describe the theorems that exist at `audit-v1-rc-1`, with no claim stronger than its cited declaration. |

---

## 4. Gate claims to test rather than trust

The project's own gates have twice been found weaker than advertised. Treat
every gate as a claim to be falsified, not as evidence.

- `scripts/claim_drift_scan.ps1` reports `0 strict failures`. **This is not
  evidence the claims are accurate.** Verify for yourself: which terms does the
  policy actually enforce, and are the *current* constants `210` and `427` among
  them? A known-open gap (`DD-20260807-087`) says they are not — `427` appears
  nowhere in the policy and `210` only inside an exception clause — so a bound
  change would leave public lines asserting a stale numeral with green CI.
  Confirm or refute, and judge whether the deferral is acceptable for V1.
- `paper/check_paper.ps1` was hardened after an audit found a wrapped phrase
  could evade it and a success line printed unconditionally after a failure. Run
  `-SelfTest`, then try to defeat it yourself.
- `scripts/hub_closure_lint.ps1` is new. Try to make the hub reach an
  RMQ-specific module without the lint firing.
- The claim-drift scan **cannot fail without `-Strict`**; check every invocation
  site passes it.

---

## 5. Deliverable

A report at `docs/internal/audit_reports/<date>_V1_RC_fresh_blind.md`:

1. The exact commit audited and how the packet was obtained.
2. Per-row verdict for `RC-01`..`RC-10`, each with the reconstruction you
   performed — file and line, not a summary of someone else's claim.
3. Findings at `P0`/`P1`/`P2`/`P3`, each with a concrete failure scenario.
4. An explicit statement of what you could **not** verify and why. This is
   required, not optional; an audit with no stated limits is not credible.
5. A verdict: `RELEASE_CANDIDATE_ACCEPTABLE`, `ACCEPTABLE_WITH_FOLLOW_UP`, or
   `NOT_ACCEPTABLE`, with the reasoning.

Do **not** state a verdict you cannot support from source you read yourself.

---

## 6. Known-open items at `5fe284f` (for the coordinator, not the auditor)

Close or explicitly defer each before choosing `audit-v1-rc-1`:

- ~~`paper/` not on `main`~~ — closed at `a54088b`, 2026-08-07.
- ~~Union-find cordon~~ — landed at `8a37b5a`, 2026-08-08. §7 is kept as the
  record of how it was done and what broke the first attempt.
- ~~`210`/`427` claim enforcement gap~~ — closed at `c14d7a5` by
  `scripts/constant_sync_check.ps1` (`WDD-20260808-021`), gate step 7b.
  **Still test it** (§4): check the pin mechanism, and that moving a Lean
  constant fails it.
- ~~Advisory independent checker~~ — dispositioned at `a3ba169`.
  `docs/INDEPENDENT_CHECK.md` documents the procedure and states that it has
  **not** been executed; Lean 4.22.0 ships no exporter. Check that the document
  does not read as a result.
- DOI and anonymous bundle — **resolved 2026-08-08 by reading the ITP 2026
  call**; see `docs/PUBLICATION_STRATEGY.md` §5. An anonymised artifact is
  **required**: "All submissions are expected to be accompanied by anonymised
  supplementary material containing verifiable evidence of a suitable
  implementation". ITP 2026 has already run (26–29 July 2026, LIPIcs vol. 382),
  so the target is **ITP 2027**. The DOI is still unminted and remains an owner
  action; note it must not be cited in an anonymous submission.

## 7. Union-find cordon — state and plan

Attempted at `5fe284f` and **reverted** to a byte-identical tree after repeated
line-ending errors during the mechanical pass; nothing was committed. The
analysis stands and should be reused:

- 11 files move (`RMQ/Core/UnionFind{,/**}.lean` -> `VerifiedDS/UnionFind{,/**}`).
- Zero private declarations, so no promotion risk.
- Only two external importers; `RMQ.lean` does not import the spoke at all.
- 212 `#print axioms` lines across `scripts/axiom_check.lean` and
  `scripts/union_find_axiom_check.lean` need the renamed identifiers.
- `RMQUnionFind.lean` must be **preserved**, not overwritten: it is one import
  plus a 179-line docstring naming the public profile theorems.
- Dated digests under `docs/digests/` and `docs/DIGESTION_LOG.md` must **not**
  be rewritten; they record what was true at a past commit.
- **The trap that broke the first attempt:** the spoke references hub names such
  as `Amortized.CostedBound` unqualified, which resolved only because it sat
  inside `namespace RMQ`. After the rename each moved file needs `open RMQ`.
  Insert it line-based, not by regex on CRLF files.
