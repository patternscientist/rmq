# Related-Work Ledger

Receipts for every precedent and related-work statement in `paper/rmq.tex`
and for every entry in `paper/references.bib`. Each receipt records the
source, date, the result actually attributed to it in the manuscript, and
how the attribution was verified in this session. Verification methods:

- **repo-doc**: pinned by an accepted repository claim map at base commit
  `3849ecbb53bbedfcd679352cc68d095fa5a304c2`
  (`docs/PAPER_RELATED_WORK.md`, `docs/RELATED_WORK_AND_LIMITATIONS.md`,
  `docs/internal/RMQ_ENDGAME_ROADMAP.md` primary-precedent list).
- **web**: verified against the open web during this session (2026-08-05);
  the specific fact checked is stated in the receipt.
- **background**: standard bibliographic knowledge, cross-consistent with
  the repo docs but not independently re-verified this session; any field
  in `references.bib` not covered by a receipt at this level of confidence
  was omitted from the entry rather than guessed.
- **source** (first used 2026-09-11): checked against the paper itself -- a
  publisher scan or an author-hosted copy of the published text -- with the
  pages read stated in the receipt. The field-policy section below already
  named this tier; this list did not, until the first receipt used it.

No receipt below is used to claim that anything is absent from the
literature. Absence claims are out of scope for this ledger; see the
Search Limitations section.

## RMQ and Fischer-Heun

- **Fischer & Heun 2011** (`FischerHeun11`), SIAM J. Comput. 40(2),
  465-492. Result used: the **non-systematic** (encoding) `2n + o(n)`-bit
  constant-time succinct RMQ scheme, Thm. 5.8 / Cor. 5.9, which answers
  without consulting the original array; the classical setting motivating
  the repository's contract. FH11 covers **both** settings -- its Thm. 3.7
  is a genuine systematic constant-time scheme -- so it must not be
  relabelled wholesale as "the non-systematic scheme" either. Verification:
  repo-doc + background (journal/volume/pages standard); setting corrected
  against FH11's abstract and its Section 5 title, "Optimal Preprocessing
  in the Non-Systematic Setting". **Corrected 2026-08-12:** this row
  previously called FH11 the *systematic* scheme -- a confirmed factual
  error recorded with its evidence in `paper/NOVELTY_LOG.md` section 5.3
  and shipped unrepaired through two release candidates.
- **Fischer & Heun 2007** (`FischerHeun07`), ESCAPE 2007, LNCS 4614,
  459-470. Result used: the systematic `2n + o(n) + |A|`-bit constant-time
  scheme -- what the manuscript's systematic sentence should have cited.
  Verification: web (DOI 10.1007/978-3-540-74450-4_41). **Never cite this
  entry for a lower bound.**
- **Fischer 2010** (`Fischer10`), LATIN 2010, LNCS 6034; extended version
  arXiv:0812.2775. Result used: the preliminary LATIN 2010 version of
  FH11's Section 5, and the explicit statement of the classical counting
  lower bound in its Section 1.1. **It is a word-RAM paper** -- its
  Section 2 declares "the standard word-RAM model" and charges the
  computation the cell-probe convention makes free -- so it is **not** the
  source of the cell-probe convention and must not be cited for it.
  Verification: repo-doc (the endgame roadmap names this paper and the
  arXiv id as primary precedent) + background for the LNCS volume; pages
  omitted from the bib entry as unverified. **Corrected 2026-08-12:** this
  row previously credited it with "the model vocabulary the pending packed
  cell-probe target follows"; see `paper/NOVELTY_LOG.md` section 5.4.
- **Gal & Miltersen 2007** (`GalMiltersen07`), Theor. Comput. Sci. 379(3),
  405-417. Result used: the origin of the free-computation cell-probe
  convention -- charging only for reading bits, not for computation -- and
  of the systematic/index vocabulary; now the citation carrying that
  convention in Section 9. Author order is Gal then Miltersen. Do **not**
  attribute the term "encoding data structure" to them. Verification: web
  (DOI 10.1016/j.tcs.2007.02.047).
- **Sadakane 2007** (`Sadakane07`), J. Discrete Algorithms 5(1), 12-22.
  Result used: the earliest non-systematic succinct RMQ -- a `4n + o(n)`
  balanced-parentheses encoding of the Cartesian tree with an `o(n)`-bit
  LCA computation therein; the setting, though not the mechanism, that the
  repository's construction shares. Verification: web (DOI
  10.1016/j.jda.2006.03.011). The paper body has not been read here and the
  ISAAC 2002 precursor has not been checked, so **2007 must not be asserted
  as a priority date**.
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
  session); LNCS volume number omitted as unverified. **Akira** Tanaka --
  a different author from the Kazunari Tanaka of `AGQT19`.
- **Tanaka, Affeldt & Garrigue 2018** (`TAG18`), J. Inf. Process. 26,
  54-72, DOI 10.2197/ipsjjip.26.54. Result used: the same lineage's
  machine-checked counted bits-examined bound for the rank algorithm --
  the closest precedent for charging a succinct query. Verification: web
  (DOI, journal, volume, pages).
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

## Word-RAM instruction-set authority (added 2026-09-11)

Receipts for the eight entries cited in `rmq.tex` Section 9.2 as authority for
the machine model of the fully charged packed query (`L-PQ-01`). They support
statements about what each source's model contains, and one statement about
what none of them lists: no research paper below names integer division or
remainder among its standard instructions (`PatrascuThorup14` supports them
only by implication), so the manuscript states them as an explicit
assumption. Each source was read on 2026-09-11 in the
version named; where the read version is a preprint or report, the published
text was not read. Bibliographic fields not named in a receipt were taken from
Crossref on the same date (tier **web**).

- **Cook & Reckhow 1973** (`CookReckhow73`), J. Comput. Syst. Sci. 7(4),
  354-375, DOI 10.1016/S0022-0000(73)80029-7. Result used: the random access
  machine with a fixed program whose instructions include loading a constant,
  addition, subtraction, register-indirect load and store, and a conditional
  transfer, under a cost function that may be identically one; under that
  uniform cost each instruction costs a bounded number of units (at most
  two), not exactly one. Cited for load-immediate, addition, subtraction,
  indirect load and branching only: the machine deliberately omits
  multiplication, has no division, shifts or Boolean operations, and has
  unbounded registers with no word size. Verification: **source** (publisher
  scan hosted on the first author's homepage, pp. 354-356 including
  Table I); issue number and DOI **web**.
- **Fredman & Willard 1993** (`FredmanWillard93`), J. Comput. Syst. Sci.
  47(3), 424-436, DOI 10.1016/0022-0000(93)90040-4. Result used: b-bit words
  with at most 2^b items; unit-cost addition, subtraction, multiplication,
  comparison and bitwise AND, with OR and XOR derived (pp. 425-426); integer
  division only in a separate extension (Section 6); the warning (p. 424)
  that unit cost on operands far longer than the input is a misuse; and the
  observation (Section 8) that multiplication is not in AC^0. Its
  multiplication returns a two-word product, which the manuscript notes the
  modeled machine lacks. Verification: **source** (publisher scan, pp.
  424-436); issue number and DOI **web**.
- **Brodnik, Miltersen & Munro 1997** (`BMM97`), in *Algorithms and Data
  Structures*, LNCS 1272, 426-439, DOI 10.1007/3-540-63307-3_80; also BRICS
  Report RS-97-12. Result used: the trans-dichotomous unit-cost basic
  instruction set -- direct and indirect addressing, conditional jump,
  addition, subtraction, bitwise Boolean operations, and left and right
  shifts -- with multiplication deliberately left out of unit cost; cited
  for those instructions and as the model without unit-cost multiplication
  for which nothing is claimed. Verification: **web** (BRICS report read,
  report pp. 2-4; the LNCS text was not read; volume, pages and DOI from
  Springer's chapter page and Crossref; the booktitle is Crossref's container
  title, re-read on 2026-09-11).
  **Corrected 2026-09-11, before commit.** The booktitle first read
  "Proceedings of the 5th International Workshop on Algorithms and Data
  Structures (WADS '97)", and this receipt said the ordinal came from the
  reference list of `HMP01`. A citing paper's reference list is tier T3,
  which `NOVELTY_LOG.md` section 0.2 bars from `references.bib`. Re-reading
  Crossref showed its record names the volume only as *Algorithms and Data
  Structures* (with the LNCS series), with no workshop name, ordinal or
  acronym, so none of those three had a T1 or T2 receipt here and all three
  were dropped from the bibliography. That this is the WADS 1997 proceedings
  is background (T4) and stays out of `references.bib`.
- **Andersson, Hagerup, Nilsson & Raman 1998** (`AHNR98`), J. Comput. Syst.
  Sci. 57(1), 74-93, DOI 10.1006/jcss.1998.1580. Result used: a unit-cost RAM
  with w-bit words for any w >= log n; the requirement, called conservative
  there, that intermediate results fit in w bits; and a shift whose distance
  is held in a second word. It lists no division instruction. Verification:
  **web** (author preprint read, whose header gives the journal, volume and
  pages; the published text was not read).
- **Hagerup, Miltersen & Pagh 2001** (`HMP01`), J. Algorithms 41(1), 69-85,
  DOI 10.1006/jagm.2001.1171. Result used: the name "multiplication model"
  for the unit-cost word RAM whose operations are addition, bitwise Boolean
  operations, shifts and multiplication (Section 1). It lists no division.
  Verification: **web** (the authors' accepted manuscript read; the
  published text was not read).
- **Patrascu & Thorup 2014** (`PatrascuThorup14`), FOCS 2014, 166-175, DOI
  10.1109/FOCS.2014.26; also arXiv:1408.3045. Result used: the word RAM as a
  model of what can be implemented in C, with unit-cost word operations,
  every integer in one word, and w >= log n (Section 1). Its support for
  division and remainder is by that implication only; it lists no division
  instruction. Verification: **web** (arXiv v2 read, which states it is the
  FOCS paper in different formatting; the FOCS typeset text was not read).
- **Mehlhorn & Sanders 2008** (`MehlhornSanders08`), Algorithms and Data
  Structures: The Basic Toolbox, Springer, DOI 10.1007/978-3-540-77978-0.
  Result used: the machine model of Section 2.2, whose one-step instructions
  include integer division and remainder alongside multiplication, shifts,
  bitwise Boolean operations and comparisons, on cells of logarithmically
  many bits (pp. 23-25). The only verified source that lists division and
  remainder explicitly; a textbook, cited only for that convention.
  Verification: **source** (the authors' copy of Chapter 2 read); publisher,
  year and DOI **web** (Springer's book page and Crossref).
- **Andersson, Miltersen & Thorup 1999** (`AMT99`), Theor. Comput. Sci.
  215(1-2), 337-344, DOI 10.1016/S0304-3975(98)00172-8; preliminary version
  BRICS Report RS-96-30. Result used: multiplication is not an AC^0
  operation, unit cost for operations outside AC^0 is questionable, and the
  standard AC^0 instructions are addition, comparison, bitwise Boolean
  operations and shifts; cited only to scope the model, for which nothing is
  claimed on AC^0-only instruction sets. Verification: **web** (BRICS report
  read, report pp. 1-3; the journal text was not read).
- Not added, and why: Hagerup's STACS 1998 word-RAM survey was seen only as an
  abstract, so no instruction list is attributed to it; Miltersen's ICALP 1996
  paper and Thorup's SODA 2003 paper were seen only as abstracts, and the
  scoping they would support is carried by `BMM97` and `AMT99`, which were
  read.

## Search limitations (explicit)

1. **AFP**: 27 full-text queries for succinct rank/select and RMQ entries
   were run, plus three exhaustive topic enumerations and direct reads of
   theory sources; none surfaced such an entry. **The residual gap is real
   and is the reason this remains a limitation rather than a negative
   result:** the AFP search indexes entry abstracts, not `.thy` sources, so
   the roughly 5.35M lines of proof text were not grepped; nine of the ten
   Algorithms subtopics and most non-CS topics were not enumerated. It must
   not be read as evidence that no AFP entry exists.
   (**Corrected 2026-08-12:** this item previously described "one web
   query", which understated the work actually done and was flagged in
   `paper/NOVELTY_LOG.md` section 5.13. The limitation itself stands.)
2. **Rocq/Coq corpus**: only the Tanaka/Affeldt/Garrigue/Qi lineage was
   verified. No systematic sweep of the Coq opam package index or of
   `affeldt-aist` repositories was performed here.
3. **Lean corpus**: no systematic sweep of Mathlib, the Lean community
   repositories, or recent ITP/CPP artifacts for RMQ or succinct-structure
   mechanizations was performed here.
4. **Proceedings sweeps**: ITP/CPP/JAR/JFP tables of contents were not
   systematically swept this session.
5. **Instruction-level cost** (appended 2026-09-11): the fully charged packed
   query (`L-PQ-01`) was added after this search. Instruction-level and
   program-step cost mechanizations were not swept for it (see
   `paper/NOVELTY_LOG.md` section 7), and the manuscript draws no comparison
   or absence inference about it. The machine-model receipts above are not a
   search result and license no such inference.
6. Consequently the manuscript's novelty wording is conditional
   everywhere: it attributes established precedent affirmatively, claims
   no priority, and defers any stronger statement to the completed search
   log. Any future tightening of novelty wording requires extending this
   ledger first, with receipts.

## Bibliographic field policy

`references.bib` fields carry one of four receipts, and `references.bib`'s
own header now names the same four: **source** (checked against the paper
itself), **web** (an explicit web check recorded here), **repo-doc**
(pinned by an accepted repository claim map), and **background** (not
independently re-verified). Where none of these applied -- specific pages,
article numbers, DOIs, LNCS volumes noted above -- the field was omitted
rather than filled in.

**Corrected 2026-08-12.** This section previously named three tiers and
asserted that "no field in `references.bib` was invented". Both statements
were wrong, and they were wrong together. The header and this ledger named
*different* trios, so `background` -- the tier most entries actually rest
on -- was licensed by neither; and one field was in fact invented: the
`ZhanHaslbeck18` title carried a `/HOL` fragment that the true title does
not have, on a `background` receipt. It is corrected, and the tier that
produced it is now named explicitly in both documents.

The general rule this establishes: a field policy that does not name its
weakest tier cannot flag the entries that depend on it, and a blanket "no
field was invented" is a claim about every field at once -- exactly the
kind of universal statement that should be a checked property or not made.
Nothing here checks bibliographic truth; `paper/check_paper.ps1` verifies
citation-key closure, not that a title matches its paper.
