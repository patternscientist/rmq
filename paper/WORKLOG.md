# Paper Substrate Worklog

Branch: `codex/eg-cp-paper-evidence-r1`
Base: `1490c97b399d136bad4e18953441da433d130d4d` (clean, verified)
Governance: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified ancestor of base)
Scope: private manuscript/evidence substrate under `paper/` only. No edits to
`README.md`, `docs/WHAT_IS_PROVED.md`, `docs/FAMILY_SUMMARY.md`, artifact or
headline claim surfaces, Lean sources, validation, or replay. No Lean/Lake or
aggregate gate runs while `EG-CP-ALLSIZE-R1` is active. No architecture choice
is made here; the packed all-size result stays provisional and appears only at
one marked insertion point.

## 2026-08-05 Session start: governance, preflight, reading

- Verified working tree clean at exactly `1490c97b...`; created branch
  `codex/eg-cp-paper-evidence-r1` from that base; confirmed the governance
  commit is an ancestor of HEAD.
- Ran `scripts/project_skill_preflight.ps1` with
  `-GovernanceRef f0c7232a...` in explicit no-role mode
  (`-AllowNoRequiredSkills`), runtime catalog
  `rmq-audit-prompt,rmq-coordinator,rmq-proof-sprint`: **PASS**. The runtime
  RMQ skill catalog is present; none of the three role skills covers
  standalone manuscript authoring, so this task runs in the no-role mode that
  its commissioning instruction authorizes. This lane records no coordinator
  acceptance, no integration, and no roadmap closure.
- Read in full or in the relevant sections: `AGENTS.md`,
  `docs/internal/RMQ_ENDGAME_ROADMAP.md` (manuscript/evidence lanes, frozen
  target model, Stage F rows, release wording), `docs/internal/AUDIT_PROTOCOL.md`,
  `docs/PAPER_THEOREM_MAP.md`, `docs/PAPER_CLAIM_CORRESPONDENCE.md`,
  `docs/WHAT_IS_PROVED.md`, `docs/PAPER_MAIN_THEOREM.md`,
  `docs/PAPER_MODEL_ADEQUACY.md`, `docs/PAPER_RELATED_WORK.md`,
  `docs/RELATED_WORK_AND_LIMITATIONS.md`, `docs/TRUST_BASE.md`, `CITATION.cff`.
- Verified by direct source inspection at the base commit that the load-bearing
  declarations exist where the claim maps say they do, including:
  `buildPayload_length`, `overhead_littleO`, `queryCost_eq : queryCost = 210`
  (`RMQ/Core/SuccinctRMQClassic.lean`),
  `exactRMQ_tight_fixed_length_payload_space_bound_doubled_catalan_slack`
  and `logSlackLower`/`doubledLogSlackLower`
  (`RMQ/Core/EncodingLowerBound.lean`),
  `concreteBPNativeSuccinctRMQPrincipledAllSizeChargedTraceCost_eq`,
  `..._readWord_only`, `..._nonSyntheticWeight_sum_le_210`
  (`RMQ/Core/SuccinctFinalRAM.lean`), reviewer physical/store-parametric
  theorems (`RMQ/Core/SuccinctFinal/RAM/ReviewerPhysical.lean`,
  `RMQ/Core/SuccinctFinalStoreParam.lean`), manifest adequacy
  (`RMQ/Core/SuccinctFinalSemanticProvenanceAdequacy.lean`), machine
  certificate (`RMQ/Core/SuccinctFinalModelAdequacy.lean`), chunk caps
  (`RMQ/Core/SuccinctClose/RelativeRmmMacro/ChargedFringeChunks.lean`,
  `ChargedWordChunks.lean`, `ChargedSameBlockChunks.lean`,
  `ChargedTableRegime.lean`), spoke capstones
  (`RMQ/Core/RankSelectPublic/Capstones.lean`,
  `RMQ/Core/BPNavigationPublic.lean`), and
  `LittleOLinear` (`RMQ/Core/SuccinctSpace/Asymptotics.lean`).
- Confirmed `scripts/claim_drift_scan.ps1` scans `README.md`, `artifact`, and
  `docs` only; `paper/` is outside the registered fact-surface scope, so this
  substrate cannot drift a registered public claim surface by construction.
  The 18-surface policy inventory is deliberately untouched.
- Web-verified the bibliography entries not already pinned by repo docs:
  Liu-Yu (STOC 2020, arXiv:2004.05738), M. Liu (arXiv:2111.02318),
  Tanaka-Affeldt-Garrigue (ICFEM 2016, DOI 10.1007/978-3-319-47846-3_16),
  Nipkow (FSCD 2016, LIPIcs 52, DOI 10.4230/LIPIcs.FSCD.2016.4),
  Navarro-Sadakane (ACM TALG 10(3), 2014). A one-query sweep of the Isabelle
  AFP did not surface a succinct rank/select entry; recorded strictly as a
  search limitation in `RELATED_WORK_LEDGER.md`, never as evidence of absence.
- Toolchain: TinyTeX with `pdflatex` and `latexmk` is present on this machine,
  so the PDF build gate applies and will be exercised.

## 2026-08-05 Deliverables 1-3 landed

- `references.bib`: 23 entries, field policy stated at the top (omit any
  field not verified; no invented pages/volumes/DOIs).
- `rmq.tex`: full draft, 12 sections, 34 distinct `\ledger` anchors, one
  `ARCHITECTURE_RESULT_PENDING` marker (Section 9.1, via `\verb`), no other
  literal occurrence of that token in the manuscript.
- `THEOREM_LEDGER.md`: 34 rows (2 reference-semantics, 20 upper-bound and
  adequacy, 2 lower-bound, 3 spokes, 1 PROVISIONAL_ARCHITECTURE, 6 OPEN),
  each ACCEPTED_BASE row pinned to `1490c97b...` with declaration and file
  verified by direct grep/read this session (line references included where
  read directly: Spec.lean:34/:48, SuccinctRMQClassic.lean:114/:1198/:1233/
  :1240/:1256/:1282/:1324, EncodingLowerBound.lean:1650/:1654/:1840/:1878,
  ReviewerPhysical.lean:1474, SuccinctFinalRAM.lean:9349,
  RankSelectPublic/Capstones.lean:244, BPNavigationPublic.lean:1666,
  WordRAM.lean:280).

## Planned deliverable order

1. `references.bib` (verified primary sources; every key cited).
2. `rmq.tex` (full draft; one `ARCHITECTURE_RESULT_PENDING` insertion point).
3. `THEOREM_LEDGER.md` (claim-by-claim mapping, exact commit).
4. `RELATED_WORK_LEDGER.md` (receipts and search limitations).
5. `EVIDENCE_MATRIX.md` (frozen rows).
6. `README.md` and `check_paper.ps1`; then checker + PDF build + hygiene.

## 2026-08-05 Deliverables 4-6 landed; checks green

- `RELATED_WORK_LEDGER.md`: receipts for all 23 bibliography entries with
  per-entry verification method (repo-doc / web / background), the
  bibliographic field-omission policy, and five explicit search
  limitations; no absence inference is drawn anywhere.
- `EVIDENCE_MATRIX.md`: seven frozen rows; EV-01 through EV-06 CLOSED,
  EV-07 blocked only on the independently accepted architecture result.
- `README.md`, `check_paper.ps1`, `.gitignore` landed.
- `check_paper.ps1` first run found one real defect: the preamble comment
  documented the anchor macro with a literal that matched the anchor
  regex. Fixed the comment (not the checker), re-ran:
  **`CHECK-PAPER: RESULT: PASS`, exit 0** -- 23/23 citation closure both
  directions, 39 unique labels with all refs resolving, 13 forbidden
  patterns clean over 7 files, 34 anchors <-> 34 ledger rows with legal
  statuses, exactly one insertion-point marker in `rmq.tex`.
- PDF build: `latexmk -pdf rmq.tex` under TinyTeX (pdfTeX, TeX Live 2026)
  **exit 0**, producing `rmq.pdf` (14 pages); final `rmq.log` contains
  zero undefined citations or references (first-pass warnings before the
  bibtex rerun are latexmk's normal fixpoint behavior). Remaining
  overfull-hbox warnings come from long verbatim Lean identifiers and are
  cosmetic only.
- Build artifacts are git-ignored; the tree carries only the eight
  intended sources.
