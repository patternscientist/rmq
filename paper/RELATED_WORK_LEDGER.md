# Related-Work Ledger

Receipts for every precedent and related-work statement in `paper/rmq.tex`
and for every entry in `paper/references.bib`. Each receipt records the
source, date, the result actually attributed to it in the manuscript, and
how the attribution was verified in this session. Verification methods:

- **repo-doc**: pinned by an accepted repository claim map at base commit
  `1490c97b399d136bad4e18953441da433d130d4d`
  (`docs/PAPER_RELATED_WORK.md`, `docs/RELATED_WORK_AND_LIMITATIONS.md`,
  `docs/internal/RMQ_ENDGAME_ROADMAP.md` primary-precedent list).
- **web**: verified against the open web during this session (2026-08-05);
  the specific fact checked is stated in the receipt.
- **background**: standard bibliographic knowledge, cross-consistent with
  the repo docs but not independently re-verified this session; any field
  in `references.bib` not covered by a receipt at this level of confidence
  was omitted from the entry rather than guessed.

No receipt below is used to claim that anything is absent from the
literature. Absence claims are out of scope for this ledger; see the
Search Limitations section.

## RMQ and Fischer-Heun

- **Fischer & Heun 2011** (`FischerHeun11`), SIAM J. Comput. 40(2),
  465-492. Result used: systematic succinct RMQ preprocessing with
  `2n + o(n)` bits and constant query time in the standard model; the
  classical setting motivating the repository's contract. Verification:
  repo-doc + background (journal/volume/pages standard).
- **Fischer 2010** (`Fischer10`), LATIN 2010, LNCS 6034; extended version
  arXiv:0812.2775. Result used: non-systematic optimal-succinctness RMQ
  representation; the model vocabulary the pending packed cell-probe
  target follows. Verification: repo-doc (the endgame roadmap names this
  paper and the arXiv id as primary precedent) + background for the LNCS
  volume; pages omitted from the bib entry as unverified.
- **Vuillemin 1980** (`Vuillemin80`), CACM 23(4), 229-239. Result used:
  Cartesian trees. Verification: background (standard).
- **Gabow, Bentley & Tarjan 1984** (`GBT84`), STOC 1984, 135-143. Result
  used: Cartesian-tree/RMQ-LCA reduction techniques. Verification:
  background (standard).
- **Harel & Tarjan 1984** (`HarelTarjan84`), SIAM J. Comput. 13(2),
  338-355. Result used: first linear-preprocessing constant-time LCA line;
  ancestor of the Euler-tour reductions the repository formalizes.
  Verification: background (standard).
- **Bender & Farach-Colton 2000** (`BFC00`), LATIN 2000, LNCS 1776, 88-94.
  Result used: simplified RMQ/LCA equivalence via Euler tours and the
  +-1 depth structure. Verification: background (standard).

## Cartesian trees, balanced parentheses, succinct trees

- **Munro & Raman 2001** (`MunroRaman01`), SIAM J. Comput. 31(3), 762-776.
  Result used: succinct balanced-parentheses representation of static
  trees with navigation. Verification: background (standard).
- **Navarro & Sadakane 2014** (`NavarroSadakane14`), ACM Trans. Algorithms
  10(3). Result used: fully-functional succinct trees via range-min-max
  structures; cited as the fuller navigation library the repository does
  not claim. Verification: **web** (journal, volume 10, issue 3, year 2014
  confirmed this session); article-number field omitted as unverified.
- **Navarro 2016** (`Navarro16`), Compact Data Structures, Cambridge
  University Press. Result used: modern reference for the succinct-toolkit
  vocabulary. Verification: repo-doc + background.

## Succinct rank/select

- **Jacobson 1989** (`Jacobson89`), FOCS 1989, 549-554. Result used:
  rank/select dictionaries for static trees and graphs; the style of the
  repository's plain-bitvector spoke. Verification: background (standard).
- **Clark 1996** (`Clark96`), PhD thesis, University of Waterloo. Result
  used: constant-time select with sublinear redundancy. Verification:
  background (standard).
- **Raman, Raman & Rao 2002** (`RRR02`), SODA 2002, 233-242. Result used:
  compressed indexable dictionaries (FID) with enumerative block codes;
  the line the fixed-weight compressed/FID spoke follows. Verification:
  background (standard).

## Cell-probe and word-RAM lower bounds

- **Liu & Yu 2020** (`LiuYu20`), STOC 2020; arXiv:2004.05738. Result used:
  first lower bound for succinct RMQ redundancy: query time `O(t)` forces
  space `2n + n/(log n)^{O(t^2 log^2 t)}`-type bounds in the cell-probe
  model with word size Theta(log n). Verification: **web** (authors
  Mingmou Liu and Huacheng Yu, STOC 2020 venue, arXiv id, and result shape
  confirmed this session); proceedings page numbers and DOI omitted as
  unverified.
- **Liu 2021** (`Liu21`), arXiv:2111.02318. Result used: sharpened, nearly
  tight lower bounds (`2n - 1.5 log n + n/(log n)^{O(t log^2 t)}`).
  Verification: **web** (arXiv id, year, sole author, result shape
  confirmed this session). Cited as an arXiv preprint only; no venue is
  asserted because none was verified.
- Manuscript discipline: the repository mechanizes neither result; the
  manuscript says so explicitly (ledger row L-OPEN-05) and never conflates
  its counting lower bound with these cell-probe bounds. The repository's
  own accepted docs (`docs/PAPER_MAIN_THEOREM.md` Lower-Bound Scope)
  mandate exactly this restraint. Verification: repo-doc.

## Verified data structures in proof assistants

- **Tanaka, Affeldt & Garrigue 2016** (`TAG16`), ICFEM 2016,
  DOI 10.1007/978-3-319-47846-3_16. Result used: Coq verification of the
  Jacobson rank algorithm for succinct data structures with extraction to
  OCaml. Verification: **web** (title, authors, venue, DOI confirmed this
  session); LNCS volume number omitted as unverified.
- **Affeldt, Garrigue, Qi & Tanaka 2019** (`AGQT19`), ITP 2019, LIPIcs
  141, article 5, DOI 10.4230/LIPIcs.ITP.2019.5. Result used: Coq/
  SSReflect verification of tree algorithms for succinct data structures
  (LOUDS and related), connected to executable extraction. Verification:
  repo-doc (the endgame roadmap pins the DOI and the four authors) +
  **web** (DOI and LIPIcs volume corroborated by search hits this
  session).
- Priority posture: this precedent line already states priority for
  mechanized succinct-structure verification in its setting (per the
  repository memory/claim docs and the papers' own abstracts); the
  manuscript therefore makes no priority claim and conditions any novelty
  wording on a completed search log. Verification: repo-doc.
- **Nipkow 2015** (`Nipkow15`), ITP 2015, LNCS 9236. Result used: verified
  amortized complexity analyses in Isabelle/HOL. Verification: background
  (standard); pages omitted.
- **Nipkow 2016** (`Nipkow16`), FSCD 2016, LIPIcs 52, article 4,
  DOI 10.4230/LIPIcs.FSCD.2016.4. Result used: verified functional
  data-structure analyses (search trees, priority queues; automated
  functional-correctness proofs, manual amortized bounds). Verification:
  **web** (venue, LIPIcs volume, DOI, content summary confirmed this
  session).
- **Gueneau, Chargueraud & Pottier 2018** (`GCP18`), ESOP 2018, LNCS
  10801. Result used: formalized asymptotic complexity claims via
  deductive program verification (time credits, big-O discipline).
  Verification: background (standard).
- **Chargueraud & Pottier 2019** (`CP19`), J. Autom. Reasoning 62. Result
  used: verified correctness and amortized complexity of union-find in
  separation logic with time credits; flagship of the time-credit
  tradition. Verification: background (standard); issue/pages omitted.
- **Zhan & Haslbeck 2018** (`ZhanHaslbeck18`), IJCAR 2018. Result used:
  verified asymptotic time complexity of imperative programs in
  Isabelle/HOL. Verification: repo-doc (named in
  `docs/RELATED_WORK_AND_LIMITATIONS.md`) + background; series/volume
  omitted.
- **de Moura & Ullrich 2021** (`MouraUllrich21`), CADE-28, LNCS 12699.
  Result used: the Lean 4 system itself. Verification: background
  (standard).
- **Archive of Formal Proofs** (`AFP`), https://isa-afp.org. Used only as
  the venue whose coverage the search plan must sweep. Verification: site
  existence is background; see limitations below for what was and was not
  searched.

## Search limitations (explicit)

1. **AFP**: one web query for succinct rank/select entries was run this
   session and surfaced no such entry. This is a single-query sweep, not a
   browse of the AFP topic index; it must not be read as evidence that no
   AFP entry exists. The full novelty log the endgame roadmap requires
   (AFP, Rocq/Coq package corpus, Lean libraries including Mathlib and
   CSLib-adjacent work, ITP/CPP/JAR/JFP proceedings, the Affeldt
   succinct-structure lineage, and current verified low-level algorithm
   work) has not been completed in this session, and nothing here
   substitutes for it.
2. **Rocq/Coq corpus**: only the Tanaka/Affeldt/Garrigue/Qi lineage was
   verified. No systematic sweep of the Coq opam package index or of
   `affeldt-aist` repositories was performed here.
3. **Lean corpus**: no systematic sweep of Mathlib, the Lean community
   repositories, or recent ITP/CPP artifacts for RMQ or succinct-structure
   mechanizations was performed here.
4. **Proceedings sweeps**: ITP/CPP/JAR/JFP tables of contents were not
   systematically swept this session.
5. Consequently the manuscript's novelty wording is conditional
   everywhere: it attributes established precedent affirmatively, claims
   no priority, and defers any stronger statement to the completed search
   log. Any future tightening of novelty wording requires extending this
   ledger first, with receipts.

## Bibliographic field policy

`references.bib` includes only fields verified at the **repo-doc**,
**web**, or confident **background** level; where confidence was lacking
(specific pages, article numbers, DOIs, LNCS volumes noted above), the
field was omitted from the entry rather than filled in. No field in
`references.bib` was invented, and no entry cites a source that was not
checked at one of the three levels.
