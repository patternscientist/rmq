Make the title of this chat exactly: (A09-ENDGAME-AUD1) Fresh blind audit of the RMQ endgame plan and its governance delta

Auditor:
- Handle: A09-ENDGAME-AUD1
- Requested title: `(A09-ENDGAME-AUD1) Fresh blind audit of the RMQ endgame plan and its governance delta`
- Mode: FRESH BLIND DELTA

Audit target:
- Base commit: bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4
- Target commit: 0e71b828ae975ba42881edf4c023813e80f070a0
- Branch: `claude/e1-strategy-memo`
- Active roadmap node and intent: the project has roughly four weeks to the `V1` submission freeze. The delta ratifies a successor plan for that runway, supersedes a governance procedure, amends two roadmap rungs, changes two public claim surfaces, and records a research disposition scoping four work lanes.
- Permission: **REPORT-ONLY.** You may create and write exactly one file, the durable report below. Every other tracked file — proof, source, script, document — is read-only. Do not commit anything else, do not merge, do not push, do not create branches or worktrees beyond your own audit checkout.
- Durable report: `docs/internal/audit_reports/2026-07-25_A09_endgame_plan_audit.md`

Independence:
- This delta was authored end-to-end by a Claude-runtime coordinator. You are a different model family; that is the point. Audit it adversarially.
- Do not seek out or read chat transcripts, worker narratives, or prior verdicts about this delta.
- **A necessary departure from ordinary fresh-blind practice:** the target documents *are* the audit subject, so you must read them. Read them as **claims to verify, not as findings to inherit.** Every factual assertion in them — commit identities, theorem names, line citations, counts, effort figures, "verified" labels — is unverified until you check it against the repository yourself. Several were produced by multi-agent research and are explicitly marked as narrative tier; treat that marking as a warning, not a waiver.
- Prior audit reports already on `main` are process evidence, not commands.

Project-skill preflight:
- Governance ref: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5`. This is the latest commit changing enforced workflow policy (skills, preflight scripts, gate, templates, repository attributes); later mainline commits add only prose and decision entries and do not advance it. Confirm it is in your checkout's ancestry.
- Runtime RMQ catalog: report the RMQ skill names your session actually exposes, and pass exactly those.
- Applicable audit-worker role skills: **NONE.** Omit `-RequiredSkills` and pass `-AllowNoRequiredSkills`. Do not name `rmq-audit-prompt`, `rmq-coordinator`, or `rmq-proof-sprint` to satisfy the gate — those are different roles. The catalog must still be supplied and non-empty.

```
powershell -ExecutionPolicy Bypass -File scripts/project_skill_preflight.ps1 `
  -GovernanceRef f0c7232a8a52b8d61ead5e96d72a8a849bc094b5 `
  -AllowNoRequiredSkills `
  -RuntimeProjectSkills "<your actual RMQ catalog>"
```

Scope:
- Delta: 6 commits, 8 changed paths.
  - `README.md`, `artifact/CLAIMS.md` — **public claim surfaces; the only substantive claim change in the delta.**
  - `docs/internal/RMQ_ENDGAME_PLAN.md` (new), `docs/internal/E1_ARCH_STRATEGY_MEMO_2026-07-25.md` (new), `docs/internal/E1_ENDGAME_WEEK1_GATE_RESULTS.md` (new)
  - `docs/internal/DESIGN_DECISIONS.md`, `docs/internal/WORKFLOW_DESIGN_DECISIONS.md` — new entries DD-20260725-004/-005/-006, WDD-20260725-008/-009
  - `docs/internal/RMQ_FINAL_ROADMAP.md` — S1 and E1 rung amendments
- Load-bearing surfaces:
  - The theorem `RMQ.Headlines.succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` (`RMQ/Headlines/RMQ.lean:595`), newly cited by both changed public surfaces.
  - `WordRAM.TraceEvent` (`RMQ/Core/WordRAM.lean:103`) and the canonical route's emitted-event vocabulary.
  - The claim-drift policy pair and its `currentFactSurfacePathRegex` 18-path inventory.
  - The roadmap rungs S1 and E1, and the acceptance status of U3 and the `210` cost literal.
- Acceptance criteria — the delta is sound iff all hold:
  1. Every public sentence changed in `README.md` and `artifact/CLAIMS.md` is true of the repository at the target commit, is supported by the theorem it names, and does not overclaim relative to that theorem's actual statement, quantifiers, and validity domain.
  2. The two changed surfaces are mutually consistent, and consistent with the other 16 current-fact surfaces.
  3. Each governance supersession (the 2026-07-07 plan; the A4 selection ordering) is lawful under the project's own recorded procedure, and its stated justification is factually correct.
  4. The roadmap amendments state the truth about S1's and E1's actual status.
  5. Factual claims in the three new documents that a reader would rely on are correct, or are correctly marked as unverified.
- Rejection conditions: any false public sentence; any claim-surface statement stronger than its cited theorem; a supersession whose stated factual basis is wrong; a roadmap status that misdescribes the repository; a "verified" label on something not verified.
- Non-goals: do not evaluate whether the plan's *strategy* is wise — that is the owner's judgment, already exercised. Do not audit the unmerged `648e512` lane, the B3 candidates, or the B2 candidates themselves; they are referenced, not changed. Do not propose new work lanes.

Adversarial requirements:

**A. The public claim change is the highest-risk item. Audit it hardest.**
- `succinctRMQWholeQueryGlobalWordTraceResultReadWordOnly` is an `abbrev`. Expand it fully to the underlying theorem. State its exact proposition, every quantifier, every hypothesis, and its validity domain. Then decide whether the two new public sentences are supported by *that*, or by something weaker.
- Specifically test: does it hold for **all sizes and all queries**, or only for valid/guarded queries, or only at a pinned instance? Both surfaces now assert "every event the canonical route emits is a payload-word read" without an explicit guard. If the theorem is guarded and the prose is not, that is a P0/P1 finding.
- Both surfaces call `wordRank`/`wordSelect` "compatibility cases that the canonical route does not emit." Verify that. Search for any route, alias, or legacy path reachable from the public surface that still emits them. If any does, the sentence is false as written.
- Both surfaces enumerate the uncharged controller work identically. Verify each listed item really is uncharged, and that nothing charged was moved into the uncharged list.
- Verify the prior wording was actually wrong. The delta claims `README.md` said the substrate has unit-cost "branches, comparisons" while `artifact/CLAIMS.md` listed those as uncharged. Read both at the **base** commit and confirm the contradiction existed. If it did not, the change is unjustified even if the new text is true.

**B. Governance supersession.**
- `DD-20260725-005` supersedes the A4 selection ordering, and its central factual claim is that selecting the historical route requires a checked *universal* B2 impossibility proof. Verify against the accepted PRELOGIC report (blob `086abee6279cb0fa8ed01975abc5cdbd4e0dfb27`) and the handoff dossier. Quote the exact quantifier.
- The same entry asserts that no recorded decision requires the paper to contain an A4 selection, and that `DD-20260722-003` was never accepted onto `main`. Verify both by search, including the possibility that an equivalent requirement is recorded under a different name.
- It records a standing rule that derived text yields to the accepted input it came from, on the stated grounds that this is the fourth instance of a defect family. Check whether "fourth" is defensible or whether the instance count is convention-dependent, and whether the rule as worded could license discarding a legitimately amended contract.
- `DD-20260725-004` supersedes the 2026-07-07 plan partly on the grounds that its A3 sketch specifies unit-cost word rank/select primitives, which `DD-20260717-C05-001` rejected. Verify both halves at their sources (the plan lives at commit `25626847233db16c7dbae638f299f3807f648031` on branch `docs/unimpeachable-rmq-plan`, not on `main`).

**C. Roadmap amendments.**
- S1 is flipped deferred → ACTIVE on the stated ground that its only prerequisite, M1, is closed and integrated. Verify that M1 is in fact closed on `main`, and that S1's prerequisite was in fact only M1.
- The S1 rung's original blocker sentence is left in place while the new gate-results document asserts it is wrong in both directions (a chunking decoder exists; a uniform-width theorem is false because sentinel words are empty lists). **Verify both halves independently** — `chunkPayloadWords` and `flattenPayloadWords_chunkPayloadWords` in `RMQ/Core/SuccinctSpace/WordStore.lean`, and `BoundedPayloadWordStore.ofChunksWithSentinel` in the same file. Then judge whether leaving the refuted sentence in the rung while contradicting it elsewhere is acceptable, or whether it is itself a drift defect.
- The E1 rung amendment describes an unmerged lane's theorem as kernel-complete. Verify at `648e51247f6c07663008ba2955a98e03b4a1ba4f` that the named theorem exists and is `sorry`/`axiom`-free, without auditing the lane's substance.

**D. The consequential factual claim in the delta.**
`E1_ENDGAME_WEEK1_GATE_RESULTS.md` §0 asserts that the `210` headline cost literal has never been accepted by a fresh blind audit; that the last accepting verdict is A04 (2026-07-14) at literal `328`; that every step of `328 → 76 → 207 → 210` carries a REJECT or `blocked`; and that two rejected/blocked targets are ancestors of `main`. **Verify or refute this independently.** It is the single claim in the delta most likely to change what the project does next, and it was produced by an agent rather than by a human reading the audit lineage. Check the audit reports on `main` and on the `codex/a0*` branches, and check ancestry with `git merge-base --is-ancestor`.

**E. General.**
- Treat claim-drift policy and its allowlists as auditable, not as ground truth. The delta reports "1,472 hits, 0 strict failures"; reproduce it.
- Look for renamed caveats, wrappers, prose that technically parses but misleads, and work that advances a different goal than the one claimed.
- Cite exact evidence for every finding **and every positive claim**. A declaration name is not evidence; expand the definition.
- Where the delta marks something as narrative-tier or unverified, do not report it as a defect merely for being unverified — report whether the marking is honest and whether a reader could mistake it for established.

**F. What we may have missed.**
The delta claims to enumerate the gaps between today's repository and a publication-ready artifact, in `RMQ_ENDGAME_PLAN.md` §6 (a twelve-row checklist). Independently ask: what would a hostile reviewer of the eventual submission attack that appears in neither the checklist nor the gap register? Report anything genuinely missing as a P1/P2 finding with evidence. This is the one place where you are asked to look beyond the delta.

Checks:
- `powershell -ExecutionPolicy Bypass -File scripts/project_skill_preflight.ps1 -GovernanceRef f0c7232a8a52b8d61ead5e96d72a8a849bc094b5 -AllowNoRequiredSkills -RuntimeProjectSkills "<actual>"`
- `git log --oneline bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4..0e71b828ae975ba42881edf4c023813e80f070a0`
- `git diff --name-only bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4 0e71b828ae975ba42881edf4c023813e80f070a0`
- `git diff bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4 0e71b828ae975ba42881edf4c023813e80f070a0 -- README.md artifact/CLAIMS.md`
- `lake env lean` on any module you need to expand; `lake build` only if a narrow target requires it.
- `powershell -ExecutionPolicy Bypass -File scripts/claim_drift_scan.ps1 -Strict`
- After the report exists: rerun strict claim drift, `scripts/design_decision_check.ps1 -Strict -Base HEAD~1`, and `git diff --check HEAD^..HEAD` **on the tree containing your report**. A pass from before the report was written does not certify the report commit. If your report must quote a forbidden current-claim phrasing as a counterexample, paraphrase it rather than widening any allowlist.

Report:
- Begin with findings, severity-ordered P0 → P3, each with exact file:line / theorem / command evidence.
- State explicitly, as separate verdicts: (1) are the two changed public sentences true and supported; (2) are the two supersessions lawful and factually grounded; (3) are the roadmap amendments accurate; (4) is the `210` acceptance-chain claim correct.
- List stale objections you considered and dismissed, with why.
- Give verification outcomes for every command run, including timings.
- Close with the single best next target for this project given what you found, and an explicit recommendation: ACCEPT the delta, ACCEPT WITH CORRECTIONS (list them exactly), or REJECT.
- Do not call anything accepted or integrated; coordinator disposition follows your report.
