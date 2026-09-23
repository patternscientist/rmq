# Coordinator disposition — RC-3 fresh-blind audit

**Candidate:** `audit-v1-rc-3` = `85f3eb971637ec797dea905094e83f5669c9f0f6`.
**Auditor verdict:** `NOT_ACCEPTABLE`. **Disposition: VERDICT UPHELD.**
**Report:** `docs/internal/audit_reports/2026-08-15_V1_RC_fresh_blind.md`.
Every finding was independently reproduced before disposition.

---

## 1. Summary

Eleven findings: three `P1`, six `P2`, one `P3`, no `P0`. **All reproduce.
None were wrong.**

**No mathematics failed, for the third consecutive audit.** `RC-01` through
`RC-09` and `RC-11` all pass, on independent source reconstruction plus
falsification. `RC-02` discharges U3 for the second consecutive round. The
kernel theorem chains for payload space, answers, charged-trace cost, the
packed cell-probe architecture and the doubled-Catalan lower bound all survived.

What failed is the release *artifact* and the required *gate* — the same
register as RC-1 and RC-2. The auditor's own summary is exact: *the Lean
artifact has the release theorem, but the paper does not yet say it has it, and
the aggregate gate does not rerun the packed architecture's adversarial suite.*

---

## 2. Auditor accuracy

| claim | coordinator verification |
|---|---|
| Manuscript pinned to `688c54a` | confirmed — 3 occurrences (`:3`, `:42`, `:108`) |
| `ARCHITECTURE_RESULT_PENDING` still present | confirmed — 1 occurrence |
| `gate.ps1` invokes neither EG-CP replay | confirmed — 0 hits; M1 runner 2 hits |
| `derived_cap_le_427` fed from `certificate.trace_cap` | confirmed at `:498-501`, `:802` |
| `independence_check` targets the structural equality | confirmed at `:60-64` |
| `RunAxiomCheck` greps only `sorryAx\|ofReduceBool` | confirmed — no standard-axiom whitelist |
| `EVIDENCE_MATRIX` says 27 accepted | confirmed stale — actual is 29 |
| claim-drift misses "210 word-RAM instructions" | **confirmed by design** — the exact probe sentence fires zero policy terms |
| `constant_sync` misses a contradictory `211` | confirmed by design — `211` is not a tracked value; `210` counts and anchors are unchanged by an insertion |

Nine for nine. The report's line citations resolved on every check.

---

## 3. Findings and dispositions

### `P1-1` — the manuscript is not the release-candidate manuscript (`RC-10` FAIL)

**ACCEPTED. And I under-rated this item myself.**

My own coordinator record listed the pending marker as known-open item #4 and
characterised it as *"an editorial gap the ledger itself discloses."* That
framing was wrong for a **release candidate**. At the release tag a reviewer
gets a kernel-exported 427-probe theorem from `import RMQPaper` and a manuscript
that pins to a four-day-older commit and calls that same result a future
editorial insertion. The paper and the artifact do not identify the same claim.
That is release-blocking, and `RC-10` is the row that exists to catch it.

The auditor also caught the checker reinforcing the defect: `check_paper.ps1`
*requires exactly one pending marker* and reports success while it remains — a
gate that enforces the presence of the problem.

**Disposition:** accepted at P1. Repin the paper substrate to the release
commit, absorb the 427 theorem into a theorem environment, remove the pending
marker, and synchronize ledger and evidence matrix — in one change, with the
citation checker run at the new pin.

### `P1-2` — the required aggregate omits both architecture replays

**ACCEPTED. New — missed by this coordinator and by two prior audits.**

`gate.ps1` runs the 41-case M1 registry and never invokes
`eg_cp_stagea_replay.ps1` (21 cases: 2 accept / 19 reject) or
`eg_cp_final_falsification_replay.ps1` (16 cases: 2 accept / 14 reject). Both
suites exist, are committed, and **passed when the auditor ran them by hand**.
The defect is that the *required* gate does not enforce them, so a coordinated
implementation/proof edit could keep ordinary elaboration green while making a
sibling store, hidden oracle, fabricated cap or weakened consumer acceptable,
with nothing in the aggregate noticing.

The release headline is the packed architecture. Its adversarial suite is not
in the release gate.

**Disposition:** accepted. Both replays are invoked from the aggregate with
propagated exit codes and retained clean-tree/hash-restoration checks.

### `P1-3` — the required full aggregate exceeded its own topology deadlines

**ACCEPTED.**

Six fixtures timed out at the 300-second per-case bound; neighbours passed at
297.425 s and 299.888 s; a focused warm-cache rerun of one produced the intended
reject in 298.145 s — **1.855 s of margin**. The auditor correctly declines to
let the focused rerun rescue the failed full run, and correctly diagnoses an
undersized deadline rather than a wrong semantic verdict.

**This is the M1 story repeating and it is my miss.** In the RC-2 round I found
the topology harness bounded its sleeper at 5 s where the M1 twin used 20 s,
raised it, and wrote a rule about divergent twins — and never asked whether the
*per-case* 300 s bound had margin on hardware slower than mine. On my run those
cases took 120–180 s. A deadline sized to one machine is exactly the defect I
had just fixed one level down.

**Disposition:** accepted. The deadline is re-derived from a measured slow path
on the supported Windows runner with explicit margin, or the topology replay's
repeated rebuild cost is reduced; then the entire aggregate is rerun from a
clean exact checkout. Deadlines get a stated derivation, not a chosen number.

### `P2-1` — the independence checker watches the wrong terminal theorem

**ACCEPTED. Third iteration of the same defect in the same checker.**

The capstone's public `derived_cap_le_427` field is populated from
`certificate.trace_cap`, supplied by
`packedReviewerRunAgainstMemory_trace_length_le_427`, which flows through
`packedReviewerControllerMeasure_start_le_427`. My checker targets
`packedReviewerControllerMeasure_valid_eq_427` — the structural equality, a
*different theorem*. The published cap's actual supplier is unwatched.

History of this one checker:
1. built to make a prose claim checkable;
2. RC-2 found the **forbidden set** guarded the sentence's two names — fixed;
3. RC-3 finds the **target** is not the theorem that supplies the published cap.

I corrected the set and never asked what the check was pointed at. The auditor
notes the gap is prospective — both the committed checker (1,855 constants) and
their own closure check of the real supplier (2,074 constants) are clean today.

**Disposition:** accepted. The checker covers all three: the structural
equality, the start-measure bound, and the run-cap supplier. A rule follows: a
dependency check must name the theorem that *supplies the published field*, and
that correspondence is itself asserted where the field is populated.

### `P2-2` — three advertised checkers have direct false-success inputs

**ACCEPTED. Verified by design, not merely by reported exit code.**

- `check_paper.ps1` passes a rmq.tex sentence asserting a fixed number of
  word-RAM steps.
- `claim_drift_scan.ps1 -Strict` passes "the canonical query executes in 210
  word-RAM instructions" in `README.md`. I ran the auditor's exact probe against
  every policy term: **zero fire.**
- `constant_sync_check.ps1` passes a contradictory current cap of `211`,
  because it enforces pinned anchors and counts of `210` and known retired
  numerals — an inserted `211` changes neither.

All three are checkers I wrote or hardened. Each was injection-verified against
the failure I imagined; none against a *contradictory current claim*.

**Disposition:** accepted. These exact mutation classes become persistent
self-tests, and `constant_sync_check` gains rejection of conflicting current
numerals rather than only known retired ones.

### `P2-3` — trust and headline gates check a curated subset

**ACCEPTED.** `RunAxiomCheck` rejects printed `sorryAx`/`ofReduceBool` and does
not whitelist `Classical.choice`, `propext`, `Quot.sound`. A declaration
depending on a differently-named project axiom prints and still receives
`AXIOM CHECK PASS`. The tree is clean today (1,163 + 337 dependency sets, only
the three standard names) — but the gate does not enforce that.

Also accepted: only the composite paper theorem has a substantial expected-type
pin; standalone aliases can be retargeted to weaker propositions while name,
existence and axiom inventory survive.

**Disposition:** accepted. Whitelist the three standard axioms; add independent
expected-type consumers for the standalone lower-bound, List-Int, readWord and
packed aliases.

### `P2-4` — the strict claim scan breaks the fresh-blind boundary

**ACCEPTED, and this one I owed them.**

The scanner defaults to all of `docs`, marks out-of-scope matches allowed, and
still emits every hit — 1,579 lines on this candidate, including prior audit
reports and worklogs, printed to a commissioned blind auditor *before* they
froze conclusions.

I identified this defect in the RC-2 round, scheduled it as a program item, and
did not fix it. It then contaminated the next audit. A known leak left open for
one round is a leak you chose.

**Disposition:** accepted. Production output restricted to failures and review
hits; process records excluded from default roots.

### `P2-5` — only the Windows ownership implementation was exercised

**ACCEPTED IN SUBSTANCE, ONE PART QUALIFIED.**

*Qualified:* the POSIX branch **is** exercised by CI — the `owned-process-posix`
job on `ubuntu-24.04` reports a conclusive barrier pass
(`grandchild=2367 absent`). The auditor's statement is true of their run, not of
the project's evidence, because they audited on Windows only.

*Accepted, and new:* their substantive point stands and is a genuine gap in my
own work. A descendant that calls `setsid` creates a new process group and
**escapes a negative-PGID kill**. My POSIX barrier self-test spawns an ordinary
grandchild, so the green CI run does *not* establish the whole-descendant-tree
property it advertises. I built that self-test in the RC-2 round to close
exactly this class of hole and left the escape case untested.

**Disposition:** accepted. Add a Linux self-test whose descendant calls
`setsid`, and either adopt a containment mechanism that survives the escape or
track descendants recursively.

### `P2-6` — the lower-bound load-bearing counterfactual is not persistent

**ACCEPTED.** An audit-time mutation deleting only `query_exact` admitted a
zero-bit encoding, demonstrating that exact query behaviour is load-bearing —
with no committed regression preserving that check.

**Disposition:** accepted. Add a small checked zero/one-bit counterfactual
around the injectivity adapter.

### `P3-1` — stale paper evidence metadata

**ACCEPTED.** `PAPER_CLAIM_CORRESPONDENCE.md:115` points at source line 490;
the field is at 498. `EVIDENCE_MATRIX.md:42-47` states 34 rows as
27 accepted / 1 provisional / 6 open; the table is 29 / 0 / 5.

Citation rot again — the third distinct instance across three rounds, after
`L-UB-06`'s 1,090-line error and the `:702 → :723` drift. The `file:line`
citation checker has been scheduled since the RC-2 round and remains unbuilt.

**Disposition:** accepted, and the citation checker moves from "scheduled" to
"lands in this round".

---

## 4. Contamination: what I owed and did not fix

The auditor disclosed three exposures. **Two are defects I had already
identified and left open:**

1. The strict scanner printing prior audit reports (`P2-4`) — identified in the
   RC-2 round, scheduled, unfixed.
2. The annotated tag object carrying a prior verdict and finding summary — I
   identified this in the program-plan disposition, predicted it would hit this
   audit, and deliberately did not rewrite the tag under a pending audit. That
   was the right call for the tag; the wrong call was creating the convention.

Their mitigation was substantive and worth recording: the space/architecture,
cost/lower-bound and anti-vacuity source auditors had not seen the leaked
material, and the paper auditor froze its conclusion before the scanner ran.

**Disposition:** both fixed in the correction round. Future annotated tags carry
identity and scope only.

---

## 5. Consequences — the RC-4 correction round

The auditor's own next-target list is adopted, extended with the findings above:

1. Repin and absorb the 427 theorem in `paper/`; remove the pending marker;
   fix the checker that requires it.
2. Ledger and evidence-matrix counts and line pointers; build the `file:line`
   citation checker and run it at the new pin.
3. Invoke both EG-CP replays from the aggregate with propagated exit codes.
4. Retarget the independence checker at all three cap-supplying theorems.
5. Persistent tests for the `P2-2` false-success inputs; `constant_sync`
   rejects conflicting current numerals.
6. Whitelist standard axioms; expected-type pins for standalone aliases.
7. Re-derive the topology deadline from a measured slow path with margin.
8. Scanner output restricted; process records out of default roots.
9. `setsid`-escaping descendant self-test on Linux.
10. Persistent lower-bound `query_exact` counterfactual.
11. Tag-annotation convention: identity and scope only.

Then rerun the entire aggregate from a clean exact checkout, on the tree that
gets tagged, and cut `audit-v1-rc-4`.

---

## 6. Assessment

The strongest candidate audit of the three, and the first to find a defect in
the *gate's coverage* rather than in its checks. `P1-2` had survived two prior
fresh-blind audits and this coordinator's own review.

The pattern across three rounds is now unambiguous and worth stating plainly:
**the mathematics has never failed, and the claims-and-guards layer has failed
every time.** Nine of eleven findings this round concern what a check *would
accept later* rather than what is wrong today — which is the correct thing for
an auditor to be finding, and the thing this project's self-review consistently
does not.

Two findings this round are second or third iterations of defects I had already
been told about and repaired one level too shallowly: the independence checker's
target after its forbidden set, and a per-case deadline after the per-sleeper
deadline. The lesson is not "check harder" but **when a defect is found in a
check, ask what else in that check is chosen rather than derived** — the target,
the budget, the threshold, the scope.
