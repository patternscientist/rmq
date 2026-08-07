# V1 Release-Candidate Fresh-Blind Audit — commissioning prompt

**Status: DRAFT. Do not launch until the release candidate is frozen.** The
exact commit is deliberately left as `<RC-SHA>` below; see §0 for the conditions
that must hold before it is filled in. Launching this prompt against a moving
tree is the specific failure this document exists to prevent.

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
audit invalidates it again.** Therefore, before `<RC-SHA>` is chosen:

- [x] `codex/eg-cp-paper-evidence-r1` merged at `a54088b` on 2026-08-07: the
      manuscript substrate, its hardened checker, and the novelty log. `paper/`
      is now part of the release candidate, so the auditor must treat it as an
      in-scope claim surface (`RC-10`) rather than as an external draft.
- [ ] The union-find cordon is either landed or explicitly deferred with a
      recorded reason. It is a tree-touching rename and must not follow the
      audit. **Not started as of `5fe284f`**; see §7.
- [ ] Any remaining V1 gap the coordinator intends to close in this cycle has
      landed (see §6 for the known-open list).
- [ ] `<RC-SHA>` is on `main`, both CI workflows are green on it, and
      `scripts/gate.ps1` exits 0 on it.
- [ ] The audit packet is built from `<RC-SHA>` with
      `scripts/make_audit_packet.ps1`.

---

## 1. Identity and independence

You are a **fresh-blind exact-commit auditor**. You have not seen this
repository's chat history, worker verdicts, or working trees, and you must not
seek them. Your inputs are exactly: the commit `<RC-SHA>`, the audit packet, and
this prompt.

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

For each, reconstruct independently from source at `<RC-SHA>`. Do not accept a
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
| `RC-10` | The manuscript in `paper/` and its ledgers describe the theorems that exist at `<RC-SHA>`, with no claim stronger than its cited declaration. |

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

Close or explicitly defer each before choosing `<RC-SHA>`:

- ~~`paper/` not on `main`~~ — closed at `a54088b`, 2026-08-07.
- Union-find cordon not started (§7).
- `210`/`427` claim enforcement gap (`DD-20260807-087`).
- Advisory independent checker (nanoda) not started.
- DOI and anonymous-bundle decision not made; `CITATION.cff` version is
  `provisional` with no `doi:`.

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
