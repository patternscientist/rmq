# C06 coordinator adjudication: the endgame audit chain

Adjudicator: C06 (Claude runtime). Date: 2026-07-25.
Governed base: `bc5851ad7a0e6a14cfab89745b0fd0707cf6a0e4`, tree
`e182bd19531060a422e881ce8889279a1f0494bf`.

This record dispositions a five-round exchange and is the coordinator artifact
the corrected roadmap delta depends on. **It records no acceptance of any
theorem, authorizes no merge or push, and makes no public claim.**

## 1. The chain

| # | Artifact | Author | Disposition |
|---|---|---|---|
| 1 | Endgame plan delta `0e71b828…` | C06 (Claude) | **REJECTED.** Preserved immutable. |
| 2 | A09 fresh-blind audit `930a610…` | Codex | Findings largely sustained; two corrections below. |
| 3 | Codex coordinator audit of A09 | Codex | Sustained. |
| 4 | Architecture judgment (packed cell-probe) | Codex | Adopted as **feasibility candidate**, not accepted. |
| 5 | Codex audit of C06's response | Codex | **Sustained in full**; five defects were mine. |
| 6 | `RMQ_ENDGAME_ROADMAP.md` | Codex | **Accepted as coordination policy** with two corrections and three Day-0 amendments, applied in this delta. |

## 2. Defects in C06's own work, sustained

Recorded because the coordinator authored the rejected candidate and must not
be the only reviewer of that fact.

1. **B2SUFF overstatement.** I wrote that the probe "established" header
   sufficiency. Verified: `git branch -a --list '*B2SUFF*'` and
   `git log --all --grep=B2SUFF` return nothing — no branch, commit,
   declaration inventory, or replay exists. It was an agent session promoted
   from tier-(c) process evidence to tier-(a). Corrected standing:
   **non-durable partial evidence, 14/25 geometry representatives.**
   Further, `G24 by rfl` proves only that a size-derived mirror unfolds; it
   does not prove counted-header decoding, universal branch factorization,
   constant serialized arity, width fit, actual consumption, or shape
   elimination.
2. **Provenance.** I proposed repairing on the rejected branch, which would
   have made the rejected candidate, the audit commission, and the audit
   report ancestors of the replacement. This delta is built from clean `main`
   instead, per the roadmap's own Git-hygiene rule 4.
3. **"G5-G9 unchanged" was false.** Under a packed target every lane shifts:
   allocation replaces payload/2n as the space metric; the harness must report
   physical packed-cell probes; novelty becomes a conjunction; manuscript
   sections must stay parameterized until the gate resolves; and evidence
   consolidation must distinguish U3+M1 acceptance from packed acceptance.
4. **Continuation audit proposed where a fresh audit is required.**
   `AUDIT_PROTOCOL.md:56-57` verbatim: *"This is token-efficient but not an
   independent final gate."* A09's frozen prompt also excluded evaluating
   strategy, so the packed architecture was outside its scope entirely.
5. **Wrong citation for the cost semantics.** I attributed weight semantics to
   `isWordPrimitive`. Verified `RMQ/Core/WordRAM.lean:171-175`:
   `nonSyntheticWeight` assigns `readWord/wordRank/wordSelect ↦ 1` and
   `synthetic ↦ 0`, while `isWordPrimitive` is a classifier that *includes*
   the synthetic marker. Conclusion unchanged, citation corrected.

## 3. Corrections against A09, sustained

- A09 extended its dead-cell criticism to `DD-20260725-003`. That is wrong:
  raw width-`w` all-ones decodes to `2^w − 1`, and only the historical
  shifted `decodeRead` yields `2^w` — which is exactly the decoder
  `DD-20260725-003` forbids for raw B3 cells. **Remove the false dead-cell
  width blocker; retain `DD-20260725-003`'s B3-owned ROM/flat-read decision.**
- A09's categorical claim that no fresh-blind audit accepted `210` is too
  strong. The M1 fresh-blind audit positively reconstructed `129 + 81 = 210`
  and marked `REQ-M1R5-COST-210-DERIVATION | PASS`
  (`docs/internal/audit_reports/2026-07-22_M1_R5_R9_fresh_blind.md:122,223`).
  The surviving gap is narrower and still real: **no fresh-blind audit covers
  the whole `328 → 76 → 207 → 210` migration and release surface.**
- Provenance disclosure: the A09 report commit is parented on `67fb79e`, not
  on its audit target `0e71b828`. Its final-tree checks therefore certify a
  target-descendant tree, and its strict design check failed only on an
  untracked `.claude/settings.local.json` in the auditor's worktree — an
  environment artifact, not a report defect.

## 4. Attribution ledger

Correcting my own earlier misattribution:

- **A09** first identified the two missing physical-model attacks —
  allocated-capacity accounting and valid-query probe totality
  (`2026-07-25_A09_endgame_plan_audit.md:348`).
- **The architecture judgment** first isolated the decisive gap: the canonical
  evaluator receives the full semantic shape for free. Verified at the exact
  function — `queryTraceResultWithStore` passes `(cartesianShape xs)` into the
  trace (`RMQ/Core/SuccinctRMQClassic.lean:200-207`).
- **C06's plan** identified neither. Three weeks of campaigning, two research
  fleets, and a twelve-row checklist did not surface the free-shape input.

## 5. Corrections applied to the roadmap in this delta

- **Policy identity pinned as a Git blob**, not a working-tree SHA-256. The
  same file yields `155BEB68…` on a Windows CRLF checkout and `a5b3bb63…` from
  the LF blob bytes; CI runs Ubuntu, so the CRLF pin would have failed for a
  Linux auditor. Now `blob 437e37e171d974c4821d6e38c0115025a2fe4e02`,
  16,717 bytes. Same hazard class as the `.gitattributes -text` rule.
- **B1 field count corrected** from "48 fixed fields" to six computational and
  forty-seven proof-only fields
  (`1727de15:docs/internal/DESIGN_DECISIONS.md:4872-4873`), which strengthens
  the passage's own point.
- **Three Day-0 amendments**: front-load `EG-CP-F03` inside Stage F; add a
  named sub-fallback if the U3 audit itself fails; budget CI wall-clock
  separately from focused engineer-days, citing `WDD-20260725-011`.

## 6. Verification performed for this adjudication

Base tree, policy version, all nine cited theorem anchors, all nine frontier
commit identities, the 18-path current-surface inventory (independently
derived from `currentFactSurfacePathRegex` and matched against the roadmap's
list), the free-shape premise at its exact function, the `nonSyntheticWeight`
table, the B1 field count at the B1 commit, and the absence of any B2SUFF
artifact. One suspicion of mine was **refuted** on inspection: U2's commit
`4f7ec8be`, whose subject line looks unrelated, is recorded as the accepted U2
target at `docs/internal/RMQ_FINAL_ROADMAP.md:131-134`.

## 7. Standing dispositions

1. `0e71b828…` stays rejected and immutable; `930a610…` stays as evidence.
2. The packed cell-probe target is `FEASIBILITY_CANDIDATE` — not accepted, not
   ratified, not `READY_TO_EXECUTE`.
3. U3+M1 is the fallback, and may not be called a certified floor until U3's
   fresh-blind acceptance audit closes or is subsumed by a rigorously scoped
   release audit.
4. B2, B3, B4, A4, and the `648e512` companion are banked research, frozen for
   this runway, and none is a V1 gate. No route is called impossible.
5. Claim-prose repair runs on its own docs branch, not in this delta.
6. This roadmap governs only after its own independent audit and owner
   ratification.
