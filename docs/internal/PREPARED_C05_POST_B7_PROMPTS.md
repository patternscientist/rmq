# Prepared C05 prompts — fire the moment B7 lands

Two prompts, written ahead of time so no session is spent drafting at the
handoff. Each needs exactly one substitution: `<B7_SHA>`, the B7 candidate
commit. Check the substitutions listed under each before firing.

Order matters. Fire **Prompt 1** (audit, read-only) and **Prompt 2** (E1
unblock, write) **in parallel** — they touch disjoint worktrees and the audit
does not gate E1's start, only E1's eventual acceptance. If the audit returns
blocking findings, message the E1 worker rather than restarting it.

---

## Prompt 1 — B7 reconstruction audit (read-only)

Launch metadata (do not paste): fresh general-purpose agent, read-only, its own
detached checkout of `<B7_SHA>`. Substitute `<B7_SHA>` and, in item 4, the
literal the worker actually derived (expected `210`; if it differs, the audit
must treat the divergence as its first finding).

```text
You are a fresh read-only reconstruction auditor for the RMQ Lean 4 project.
Audit exact commit <B7_SHA> on branch claude/b7-charged-sparse-level, worktree
C:\Users\poin\Documents\RMQ\.worktrees\b7-charged-level. Range f6564ec..<B7_SHA>.
READ-ONLY: no edits, no commits. Treat "it compiles and the reported battery
passed" as given; reconstruct every other claim from source. Do not read the
worker's completion report as authority — matrices and worklogs in the delta are
worker-authored process evidence, and every status column is a claim to verify.

CONTEXT. This rung charges the last known uncharged size-dependent computation
on the accepted RMQ query route: the sparse-table level. Previously
`bpSparseLogSpan blockCount = 2 ^ Nat.log2 blockCount` was evaluated on a
runtime-derived count whose result feeds a read address, emitting no trace
events. The rung replaces it with a count-indexed charged table whose cell packs
BOTH the level and the span, read once per two-span call. It landed in two
commits: A widened the interior cap 30 -> 33 and migrated the literal 207 -> 210
against the UNCHANGED route (deliberately loose, with a self-announcing slack
theorem); B is the atomic swap that makes the bound tight again.

Verdict each item CONFIRMED / REFUTED / UNCLEAR, with quoted Lean and file:line.

1. FREEZE INTEGRITY. B7 matrix rows were frozen before implementation. Extract
   the requirement columns at the freeze commit and at HEAD and diff them. No
   row weakened, none added post-freeze without its own pre-implementation
   freeze. Report any row whose evidence cell does not establish its
   requirement.

2. THE SILENT COMPUTATION IS ACTUALLY GONE. Walk the caller chain from
   `concreteBPNativeSuccinctRMQWholeQueryGlobalWordTraceResult` and confirm no
   reachable path still evaluates `Nat.log2` or `bpSparseLogSpan` on a
   runtime-derived value. Four executed sites were identified (two `Computation`,
   two `Costed` twins equated through `_refines`); the `WordReads.lean` pair was
   proved UNREACHABLE — re-verify that independently rather than inheriting it,
   since it is the difference between closing the rung and leaving a
   Theta(log n) hole. Classify every surviving occurrence as reachable or
   legacy/compat.

3. THE SLACK ARTIFACT IS DELETED, NOT WEAKENED. Commit A carried
   `canonicalRelativeRmmPrincipledInteriorChargedTraceCost_announced_slack_...`
   asserting `cost <= 30 /\ 30 < cap /\ cap = 33`. Confirm it is absent at HEAD.
   Then confirm it COULD NOT have survived: its middle conjunct must be
   unprovable once the swap consumes the headroom. A weakened or renamed
   survivor is a finding.

4. THE LITERAL IS JUSTIFIED BY READS, NOT BY SLACK. This is REQ-B7-05's whole
   point and the reason two rows were held open through commit A. Confirm the
   route literal derives from the named component algebra with the interior
   field at its tight post-swap value, and that the derivation is `rfl` from
   named components rather than an asserted numeral. Confirm 207 remains frozen
   and that every frozen historical algebra now uses ALL-LITERAL fields — a
   defect repaired mid-rung was that frozen algebras referenced the LIVE
   interior cap, so moving it silently rewrote history. Check the definitions,
   not just the identities: an identity that holds today is not evidence that a
   constant is pinned.

5. CHK-04 — THE SWAP IS LIVE, NOT DECORATIVE. The pre-swap harness baseline is
   76/72/54, 116/126/62, 92/96/57, 93/95/57. Confirm interior windows actually
   MOVED, and that the movement is consistent with the number of charged reads
   added on each branch. Windows identical to baseline would mean the store grew
   and nothing reads it.

6. WIDTH FIT. `bpSparseLevelLocalWidth_le_machine_of_macro_crossing` and its
   global twin claim a one-machine-word fit for ALL shapes under the route's own
   macro-crossing hypothesis. Verify: (a) the hypothesis is genuinely the one the
   interior dispatcher establishes before a cross-macro two-span call is
   reachable, NOT a size threshold introduced for convenience — a threshold in
   the public route is forbidden; (b) the small-size case is handled by
   reachability rather than by exclusion (the fit is expected to FAIL at size 4,
   saved only because macro crossing there requires `9 < 1`); (c) `10 <= base`
   is derived, not assumed; (d) branches without the hypothesis are covered.

7. SPACE. The new tables must be counted and o(n). Verify the four
   space-accounting links, that the tightened width did not invalidate them
   (a bridge lemma was used rather than reproving — check the bridge), the
   derived linear capacity constant, and that `buildPayload.length <= 2*n +
   overhead n` with `overhead = o(n)` retains its exact public statement shape.
   Confirm the local and global tables use DIFFERENT envelopes and that both
   are genuinely dominated.

8. VOCABULARY AND PROVENANCE. `..._readWord_only` must be re-proved over the
   AMENDED object, not inherited. Confirm its subject is the object the headline
   chain consumes. Confirm W19 provenance covers the new reads to the standard
   used for existing sources, and confirm no new segment was introduced
   (`canonical_segments_complete` should still bound at `< 23`).

9. NO DEAD SOURCES, EVER. The rung's central constraint is that a counted region
   nothing reads must not exist at ANY commit. Walk the commit sequence and
   confirm no intermediate state has counted storage without a reader. This is
   the constraint that forced the atomic commit; verify it was actually honoured
   rather than asserted.

10. NO WEAKENING ELSEWHERE. Confirm no closed B2/B3/B4/B6 row's supporting
    theorem changed statement; no frozen public identity renamed or deleted;
    hygiene clean over the delta (`sorry|admit|axiom|native_decide|partial|
    unsafe|implemented_by|noncomputable|Mathlib|ofReduceBool`); `git diff --check`
    clean apart from any committed `.patch` artifact, whose blank context lines
    are single spaces by construction and are not a defect.

TRAP TO AVOID, discovered the hard way on this rung: `import RMQ` does NOT reach
`InteriorDirectory`, so `#print axioms` there reports `unknown constant` even
after a green root build — indistinguishable from "never built". Import modules
DIRECTLY when confirming axioms, and never read `unknown constant` from an
indirect import as evidence of absence.

Also note: `scripts/wordram_axiom_check.lean`, `scripts/axiom_check.lean`, and
`lake exe rmq_succinct_classic_validate` are known-red for reasons owned by a
different branch (a stale retired constant, and a COMPILE-time failure that
prevents the executable from running at all). Record them; do not attribute them
to this rung.

END WITH: overall recommendation (accept and proceed to E1 / repair first,
naming repairs), an explicit answer on whether the accepted route now has ANY
remaining uncharged computation whose cost grows with input size, and updated
residual questions for the eventual external blind auditor.
```

---

## Prompt 2 — E1 unblock: discharge `hInterior`

Launch metadata (do not paste): fresh Claude worker, worktree
`C:\Users\poin\Documents\RMQ\.worktrees\b2-charged-fringe`, branch
`claude/b1-b2-charged-fringe-tables`. Substitute `<B7_SHA>` and confirm the E1
branch HEAD before firing. **Before launching, decide the merge question in the
note at the end.**

```text
You are worker E1-R4t on the RMQ Lean 4 formalization project (Mathlib-free,
Lean/Std + omega). Workspace: git worktree
C:\Users\poin\Documents\RMQ\.worktrees\b2-charged-fringe, branch
claude/b1-b2-charged-fringe-tables. Work ONLY there; no push, no merge.

YOU ARE UNBLOCKED. The interior leg's sparse level is now charged: worker B7
landed commit <B7_SHA> on claude/b7-charged-sparse-level, replacing the runtime
`Nat.log2`/`bpSparseLogSpan` computation with a count-indexed charged table whose
cell packs both level and span, read once per two-span call. Every E1 row has
been Open pending exactly this.

FIRST read `docs/internal/E1_WORKLOG.md` (the M3d-10 resume inventory and all
accumulated gotchas) and `docs/internal/E1_AMENDED_MACHINE_ACCEPTANCE_MATRIX.md`
(11 rows, all Open, all whole-query scoped).

WHAT IS ALREADY BUILT AND GREEN — do not rebuild any of it: the 12-instruction
ISA and `RunsTo` calculus; the invalid-guard slice with public parity; the route
decomposition; rank-close and select-close legs at canonical-store form; the
fringe fold block and its four-way merge; the fringe arms with register
preservation; the same-block arm and full leg; the branch dispatch composed with
the leg; the three-way candidate merge; whole-program width certificates; the
base-parametric fringe arm program; and `crossBlockArmProgramAt_runsTo` — 370
instructions, receipts positionally equal to `crossBlockArmSpec`'s trace, with
the interior supplied as the hypothesis `hInterior` and its trace, categories and
value all parameters. The validator executes the machine across five phases with
three complementary discriminators (receipt, value, preservation), each with a
witnessed mutation the others cannot catch.

MISSION, in dependency order:

1. DISCHARGE `hInterior`. Build the machine simulation of the AMENDED interior
   — note it now performs MORE reads than when the cross-block arm was written,
   because the level and span arrive from charged table reads instead of a silent
   recursion. Positional receipt equality against the amended interior trace,
   derived category counts, width certificate, and a hosting witness that
   EXECUTES rather than merely hosts.
2. COMPOSE THE FULL LCA LEG: branch dispatch, same-block leg, cross-block arm
   with `hInterior` now discharged, at canonical-store form.
3. WHOLE-QUERY GLUE via `E1RouteDecomposition`: `e1ValidPath` composition
   (select; select; option tests on packets; lca; rank; packet write; halt) with
   `RunsTo.trans`/`HostedAt`. Result agreement with `(...).value`, POSITIONAL
   receipt equality with `(...).trace`, and category accounting across ALL
   branches including selects-none and lca-none. Then the public `List Int`
   corollary via `SuccinctClassic.queryTraceResult` and `Cartesian.shape_size`.
   Land the ONE consolidated program-layout DD here.
4. M4 — the DERIVED all-size literal step total. Derive from the category
   algebra and the loop caps; never assert. Expect it in the low thousands;
   whatever derives, derives.
5. M5 — the amended-target Prop, proved by your construction, plus the
   obstruction-supersession note. Relate it precisely to the refuted
   `E1R3FamiliarMachineTarget` (commit 7fe5b8b on the old E1 branch): its
   per-position clause is void because no branch of the accepted route performs
   a per-position scan. IMPORTANT: the sentence "every loop is a chunk fold under
   a literal cap" was FALSE while the interior recursion existed and must not be
   shipped from an older draft unamended — after B7 it becomes true, so state it
   only with the B7 dependency made explicit.
6. M6 — extend the validator's whole-query phase. Its attachment point currently
   reports `wholeQueryComparison=OPEN (interior leg blocked; NOT a pass)`. Close
   it honestly: independent-reference expectations computed BEFORE any machine
   run, machine `readLog` diffed event-by-event against the route's independently
   computed `.trace`, modeled steps separated from wall-clock, and a deliberate
   mutation rejected. Choose the discriminator with actual power for the whole-
   query phase and say which and why.
7. M7 — extend `docs/PAPER_MODEL_ADEQUACY.md` with what the MACHINE now charges
   (B7 already repaired the route-level charge policy), close all 11 matrix rows
   with exact quoted propositions and P/Q pairs, and run the final battery.

VERIFICATION STANDARDS, all learned from real failures on this campaign:
- `lake build RMQ` is binding ONLY for the library — it reports success while
  `lean_exe` modules fail to compile. Your battery MUST include
  `lake build rmq_e1_machine_validate` and `lake exe rmq_e1_machine_validate`.
- Per-file `lake env lean` is an iterate aid only: it reports clean on
  accidentally commented-out code and writes no olean.
- Confirm claimed theorems with `#print axioms` after a root build, importing
  the module DIRECTLY — `import RMQ` does not reach every module, and an
  indirect import reports `unknown constant` for a theorem that exists.
- Report results EXACTLY as observed with the decisive line pasted. Never carry
  a predecessor's or the coordinator's claim forward as your own; this campaign
  has corrected both repeatedly.
- Anti-vacuity bar for machine work: do not merely HOST a block — execute its
  paths onto distinguishable halts. A theorem about a branch target past the end
  of a program is true and worthless.

FINAL BATTERY: `lake build RMQ RMQPaper RMQExamples`;
`lake build rmq_e1_machine_validate`; `lake exe rmq_e1_machine_validate`;
`lake env lean scripts/headline_axiom_check.lean`; hygiene `rg` +
native_decide scan; `git diff --check` and the committed-range form;
`design_decision_check.ps1 -Strict`; `claim_drift_scan.ps1`;
`paper_topology_lint.ps1`. Do NOT run `gate.ps1` — the coordinator runs it at
the rung boundary.

WATCHDOG: a cold rebuild runs 400-700s silent and the agent watchdog kills at
600s of no output. Keep output flowing, tee to a polled file, or keep builds
incremental. If you need a silent cold rebuild, stop, commit, and say so — the
coordinator runs it in a background shell and hands back the result.

RULES: no sorry/admit/axiom/native_decide/partial/unsafe/implemented_by/Mathlib;
builds green at every commit; no weakened rows; no renamed/deleted frozen public
identities; no asserted constants; kernel-safety pattern (no concrete-record
defeq at large shapes); mutex `Global\RMQHeavyVerification` for anything over
five minutes; commit early and often. If budget runs low, land the current
milestone green, commit, and write a verified file:line-exact resume inventory
rather than starting what you cannot finish — five predecessors made exactly
this call and it was right every time.

REPORT: first line exactly `Status: CANDIDATE_COMPLETE` / `Status: INCOMPLETE` /
`Status: OBSTRUCTED` / `Status: BLOCKED`; if complete, second line exactly
`I found no assigned or inherited acceptance criterion unmet; coordinator
acceptance is still required.` Then branch/base/HEAD, changed files, exact key
theorems (quoted Lean) — the amended-target Prop, the whole-query simulation,
positional receipt equality, and the derived step literal above all — matrix
summary, validator counts with modeled steps and wall-clock separated plus
mutation evidence, verification ledger with pasted decisive lines, proof
digestion, resume point if incomplete. Never claim acceptance, integration, or
merge-readiness.
```

---

## Decision required before firing Prompt 2

E1 lives on `claude/b1-b2-charged-fringe-tables`; B7's swap lives on
`claude/b7-charged-sparse-level`. E1 cannot discharge `hInterior` against an
interior that is not in its tree. Choose one:

- **(a) Merge B7 into the E1 branch first.** Simplest for the worker, and the
  branches are disjoint in files apart from the interior. Costs one merge before
  the audit completes, so a blocking audit finding would land on a branch that
  already consumed it.
- **(b) Have E1 work on a fresh branch off the B7 candidate.** Keeps B7's audit
  independent, but E1's committed history then has to be replayed or merged
  forward.

Recommendation: **(a)**, with the audit running in parallel. The audit is
read-only against the B7 commit itself, so a finding there is repaired on the
B7 branch and re-merged; E1's work is additive machine modules that do not
modify the interior, so a repair does not invalidate it. Record the choice in
the round log when firing.
