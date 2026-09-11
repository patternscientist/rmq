# Paper Substrate Worklog

Branch: `codex/eg-cp-paper-evidence-r1`
Base: `1490c97b399d136bad4e18953441da433d130d4d` (clean, verified) -- HISTORICAL,
deliberately not moved by later repins: a session log records what was true when
the session ran. The substrate's current base pin lives in `README.md` and
`THEOREM_LEDGER.md`. Annotated 2026-08-16 because this is the only full-SHA base
in `paper/` that a repin does not touch, so an unmarked third SHA reads like a
straggler from the repin rather than a record.
Governance: `f0c7232a8a52b8d61ead5e96d72a8a849bc094b5` (verified ancestor of base)
Scope: private manuscript/evidence substrate under `paper/` only. No edits to
`README.md`, `docs/WHAT_IS_PROVED.md`, `docs/FAMILY_SUMMARY.md`, artifact or
headline claim surfaces, Lean sources, validation, or replay. No Lean/Lake or
aggregate gate runs while `EG-CP-ALLSIZE-R1` is active. No architecture choice
is made here; the packed all-size result stays provisional and appears only at
one marked insertion point.

**HISTORICAL (annotated 2026-08-16).** That sentence describes the session this
log records, not the current tree. The result was accepted (Stage A, 2026-08-07)
and absorbed into `rmq.tex` Section 9 as a theorem in the RC-4 round; there is
no marked insertion point left. Like the `Base:` SHA above, it is left standing
as a record rather than rewritten.

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
  verified by direct grep/read this session -- **one of those line references
  was wrong; see the 2026-08-16 correction below** -- (line references included
  where read directly: Spec.lean:34/:48, SuccinctRMQClassic.lean:114/:1198/:1233/
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

## 2026-08-07 -- repin, retraction, and checker hardening

Base moved `1490c97b...` -> `745a3c5b...` by rebase (183 commits). All 11 cited
files and all 58 cited Lean declarations were verified to still exist at the new
base before anything else was touched; the dead-code sweep and file split that
happened in between broke no anchor.

Two statements were **false**, not stale, and were retracted: `rmq.tex:229`
("the current mainline theorems do not bound this quantity") and `rmq.tex:809`
("no current theorem bounds the full allocated capacity ... by 2n+o(n)"). Stage
A field 8 `allocation_two_n_plus_rho` proves exactly that bound. Repinning also
turned five hedged statements false, since they were scoped "at the base
commit"; those were repaired in the same edit.

Checker hardened before writing any new prose, because the old forbidden list
contained no pattern for the framings retired from the repository's public
surfaces on 2026-08-07, so a redraft could have reintroduced them and still
passed. Defects closed, each found by audit:

- multi-word patterns were matched only against raw text, and `rmq.tex` is
  hard-wrapped at 110 columns, so a banned phrase split across a newline
  evaded the scan. Now matched against a whitespace-normalized copy too.
- no model-vocabulary patterns at all. Added eight, with an attribution
  allowance: a cited description of prior work is legitimate ("Fischer and
  Heun~\cite{FischerHeun11} gave the ... constant-time succinct RMQ ...");
  the same phrase unattributed is not. Priority claims get no allowance --
  a citation does not license "we are the first".
- the ledger status guard compared two totals and could not see a row that
  lost its status while another gained a spare. Now per-row.
- status comparison used `-notcontains`, which is case-insensitive, so
  `open` and `Accepted_Base` were legal. Now `-cnotcontains`.
- the label section printed "all refs resolve" unconditionally, immediately
  after reporting an unresolved ref. Success lines are now printed only when
  the section recorded no failure. This is how a green log came to be cited
  as evidence for a property the script had just contradicted.
- cross-reference checking covered only `\ref`, silently ignoring `\cref`,
  `\eqref`, `\autoref`, `\pageref` and starred forms. Latent, now closed.

Verification. `-SelfTest` adds 16 detector cases, all passing, each
corresponding to one audited defect. End-to-end injection: six violation
classes were appended to a throwaway copy and all six produced exit 1. The
decisive comparison, on identical input containing a priority claim wrapped
across a newline: the **old** checker exits 0 (`RESULT: PASS`), the new one
exits 1 with "split across a line wrap".

The hardened checker also caught a live hit on its first run --
`constant-time succinct` at `rmq.tex:767` -- which inspection showed to be a
correctly attributed description of Fischer and Heun, and which motivated the
attribution allowance rather than a weakening of the pattern.

`check_paper.ps1 -SelfTest` exit 0; `latexmk` clean rebuild exit 0, 15 pages,
zero undefined citations or references.

## 2026-08-16 -- correction to the declaration-verification inventory above

The inventory says every listed line reference was "verified by direct
grep/read this session". **`SuccinctRMQClassic.lean:1324` was not right at
`1490c97b`, the base this log names.** At that commit `:1324` is
`theorem queryCostedWithStore_eq_of_orderedReadFootprint`, while the row that
cites it (`L-UB-12`) names
`queryTraceResultWithStore_eq_of_orderedReadFootprint`, which is at `:1298`.
The other 17 references resolve.

The pointer was corrected in `THEOREM_LEDGER.md` during the RC-4 round, and
this sentence -- which asserts the pointers were checked -- was left standing.
That is the same defect the round found in `paper/README.md` and recorded as
DD-20260816-110: **fixing a claim at its origin is not fixing the claim.** It
was found by a third audit, not by the round that corrected the pointer.

Line references are now machine-checked by `paper/check_citations.ps1`, which
covers `THEOREM_LEDGER.md`. This log is not covered; the correction above is a
one-time manual pass over its 18 references, not a standing guarantee.

## 2026-09-11 -- the fully charged packed query enters the manuscript as a candidate; repin to `3849ecbb`

- Governance: branch `codex/fully-charged-packed-query-v1`, Lean work based on
  `4639223b` (`audit-v1-rc-6`, governance). The owner
  decided that the manuscript covers the PQ1 candidate theorem in this task.
  The paper commit is a child of `3849ecbb` and changes no Lean library file.
- Why: at `3849ecbb`, `import RMQPaper` supplies
  `RMQ.Headlines.succinctRMQFullyChargedPackedQuery`, while `rmq.tex`, pinned
  to `0665b494`, called instruction-level charging future work (Section 3,
  Section 11 item 1, Section 12) and ledger row `L-OPEN-06` said no
  instruction-level machine existed.
- Edits: Section 9.2 (Theorem 9.2, candidate), with the machine, primary
  sources for its operations, and integer division and remainder stated as an
  explicit assumption; the abstract, Section 1.1 (lead-in and item 6), 1.2
  and 1.3; Section 3 (six quantities, allocated bits, charge-policy scope,
  model paragraph); the Section 7 import closure; a Section 8 replay
  sentence; the Section 9 introduction and the second reading of Theorem
  9.1; the Section 10 cost paragraph; Section 11 items 1, 3 and 6; Section
  12. Ledger rows `L-PQ-01` (including the certificate fields `specResult`,
  `noFailedLoads` and `invalidGuardSteps`) and `L-OPEN-07` added,
  `L-OPEN-06` amended, and the orphan fragment at the end of `L-ARCH-01`
  removed. Eight bibliography entries added, each with a receipt in
  `RELATED_WORK_LEDGER.md`. The 38 full-SHA pins moved; `L-PQ-01` adds a
  39th.
- Pre-commit review. Two independent reviews of the uncommitted draft raised
  21 issues, all addressed before commit. The substantive ones: Section 9.2
  said the span decoder divides a bit position by "a cell width held in a
  register"; the divisor is the word width `W(n)`, metadata word 6, loaded
  into a register (`SpanAssembly.lean`, the `div` and `mod` of `spanBlock`),
  and `DD-20260911-PQ1-020` corrects `DD-20260911-PQ1-018`, which said the
  same. Several statements lacked the representable-endpoint premise
  (`halt`, `result` and the safety fields hold for endpoints below
  `2 ^ W(n)`; the six-step
  invalid bound also covers larger endpoints, but only as a fact about the
  unbounded evaluator). The `2 ^ 28` threshold is now marked as arithmetic
  from the definitions, not a kernel-checked statement. Three phrasings
  outside Section 9 described Theorem 9.1 by its model, against `EV-07`;
  they now name it by label only, and the `EV-07` entry lists every added
  reference. The `ACCEPTED_BASE` label of `L-PQ-01` asserts only the first
  clause of its definition, and the ledger now says so. The `BMM97`
  booktitle carried a workshop ordinal taken from a citing paper's reference
  list (tier T3) and is now Crossref's container title.
- Checks on the working tree of the paper commit, whose Lean library files
  are byte-identical to `3849ecbb`: `paper/check_paper.ps1 -SelfTest` exit 0
  (35 cite keys and 35 bibliography entries; 41 labels and 87
  cross-references; 36 anchors and 36 rows; 57 declaration names equal to the
  decl-check list; 30/0/6; 27 source citations resolve);
  `paper/check_citations.ps1` and its `-SelfTest` exit 0;
  `scripts/claim_drift_scan.ps1 -Strict` exit 0 with 0 strict failures;
  `git diff --check` exit 0; `git diff --quiet` against `3849ecbb` over the
  Lean library roots, `lakefile.toml`, `lake-manifest.json` and
  `lean-toolchain` exit 0; `latexmk -pdf rmq.tex` in a scratch copy exit 0,
  20 pages, no undefined citation or reference, and the same 23 overfull
  boxes, at the same widths, as the `rmq.tex` committed at `3849ecbb`.
- Lean checks for this move, run on a tree whose Lean library files are
  byte-identical to `3849ecbb`: `lake build` and `lake build RMQPaper` exit 0
  (up to date); `lake env lean scripts/axiom_check.lean` exit 0 (1,163 axiom
  records, 30 of them axiom-free); `scripts/headline_axiom_check.lean` exit 0
  (114 records; `RMQ.Headlines.succinctRMQFullyChargedPackedQuery` depends on
  `propext`, `Classical.choice` and `Quot.sound`);
  `scripts/wordram_axiom_check.lean` exit 0 (348 records); no record in the
  three inventories names any axiom other than those three;
  `scripts/independence_check.lean` passes (three cap-supplying theorems
  checked against the eight charged declarations);
  `scripts/ledger_decl_check.lean` passes (57 names present, negative control
  absent).
- Not done in this commit: the novelty search was not extended; the step
  counts printed by the runtime fixtures are not stated in the manuscript,
  because no committed check asserts them. `scripts/paper_topology_lint.ps1`
  refuses a dirty tree, so it runs after the commit.
