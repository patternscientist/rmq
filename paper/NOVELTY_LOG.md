# Novelty Log

**Document:** `paper/NOVELTY_LOG.md`
**Companion to:** `paper/rmq.tex`, `paper/references.bib`, `paper/RELATED_WORK_LEDGER.md`
**Manuscript base commit:** `e3362d4f0300b3b0aef22d104ed67844d80134a0`
**Search date:** 2026-08-07
**Status:** first completed novelty search. This log supersedes the "search log not yet complete" hedge in `rmq.tex` §1.2 and §10 only to the extent stated in §3 below; it does **not** license any unconditional priority claim.

---

## 0. How to read this document

### 0.1 The discipline

Every statement of the form "we did not find X" in this document means exactly that: **no search modality we ran surfaced X**. It never means "X does not exist". The literature we could not reach is enumerated per modality in §1 and summarised in §6.3. A reader who wants to defeat a claim in §3 should start with the limitations, not with the findings — the limitations are where the defeaters would be.

Where a candidate claim did not survive, it is named and retired in §4 rather than quietly weakened.

### 0.2 Verification tiers

The six search modalities reported findings with a binary label (`verified-this-session` / `background-not-reverified`). That label is too coarse, because it conflates "I fetched and read the PDF" with "I saw the title in a search-result listing". This log re-tiers everything:

| Tier | Meaning |
|---|---|
| **T1 — Primary** | The source document itself (PDF, published page, or source file) was fetched and read this session. |
| **T2 — Index** | Bibliographic fields confirmed against a structured record (dblp, DOI resolution, OpenAlex, Semantic Scholar, publisher landing page) but the document body was not read. |
| **T3 — Search-result** | Only a search-result listing, or a citing paper's reference list, was seen. Fields at this tier must not enter `references.bib`. |
| **T4 — Background** | Believed on prior knowledge; not re-verified this session. |

An item may be T1 for its abstract and T3 for its page numbers. Where that happens the log says so.

### 0.3 What was actually proved, for calibration

Nothing in §3 may be read as stronger than the underlying artifact. For the record, the development at the base commit proves:

- A Mathlib-free Lean 4 payload bound of at most `2n + o(n)` bits for exact RMQ over `List Int`, with exact leftmost-minimum answers and uniform rejection of invalid queries.
- A uniform charged-trace bound of **210** events in an explicit trace model, and a derived cap of **427** attempted aligned `w(n)`-bit cell probes for a packed cell-probe representation whose complete allocated capacity is `2n + o(n)`. Computation *between* probes is free; controller dispatch, decoding, arithmetic, comparisons and branching are **uncharged**. This is a cell-probe result — not word-RAM instruction time, not preprocessing time, not measured runtime.
- A mechanized information-theoretic lower bound: any fixed-length payload-only exact RMQ encoding needs `2n − 1.5 log₂ n − O(1)` bits, in doubled-Catalan-slack integer form.
- Preprocessing complexity for the succinct construction is **unproved and unclaimed**.

---

## 1. Search record

Six modalities were run. Counts: **93 item-records** returned (7 / 12 / 9 / 20 / 22 / 23 across the modalities below), of which **36** underwent an independent adversarial verification pass. Item-records duplicate across modalities; roughly 70 distinct sources were touched.

---

### 1.1 Modality A — the Coq/Rocq succinct-data-structure lineage

**Scope.** The Tanaka / Affeldt / Garrigue / Qi line and everything descending from it: papers, artifacts, citation graph, and the group's non-English and workshop output.

**Queries run (abbreviated; full list retained in the search transcript).**

```
Tanaka Affeldt Garrigue "succinct data structures" Coq ICFEM 2016 rank
Affeldt Garrigue Qi Tanaka succinct data structures Coq citing "Proving Tree Algorithms" later work 2021 2022 2023
Xuanrui Qi succinct data structures Coq thesis formalization complexity
formally verified "range minimum query" Coq OR Lean OR Isabelle proof assistant succinct
github Coq OR Lean formalization "range minimum query" RMQ Cartesian tree verified library proof
"cell probe" model formalized proof assistant machine-checked lower bound query cost Coq Lean Isabelle
mechanized information-theoretic lower bound data structure Catalan "2n bits" proof assistant formalized succinctness
"succinct data structures" formal verification proof assistant 2024 2025 2026 mechanized space bound o(n) redundancy
machine-checked verified succinct rank select bitvector Verus F* Agda Lean implementation space overhead proof 2023 2024 2025
verified Cartesian tree lowest common ancestor formalization Coq Lean Isabelle "Fischer-Heun" OR "sparse table" RMQ
"rank_spaceD1" OR "tanaka-akira/succinct" Coq rank space lemma succinct
```

Direct fetches (T1): the ICFEM 2016 author preprint (19 pp., read end to end); the LIPIcs ITP 2019 PDF (19 pp., read end to end); arXiv:1904.02809 abs and PDF; `github.com/affeldt-aist/succinct` repo metadata, full recursive git tree, `opam`, README, and the **complete 259-line source of `jacobson_rank_complexity.v` read line by line**; the J-STAGE page and full PDF of *Safe Low-level Code Generation in Coq* (JIP 2018); the Coq Workshop 2019 extended abstract (2 pp.) and its 22-slide deck; Semantic Scholar and OpenAlex citation graphs for both papers; the CPP 2025 BWT page; Louis Cheung's dblp page.

**What was found.**

- ICFEM 2016 proves Jacobson `rank` only — functional correctness against `rank b i s := count_mem b (take i s)`, plus storage-requirement lemmas, plus OCaml extraction over an explicitly *unverified* bitstring library that uses `Obj.magic`. No `select`, no trees, no RMQ, no Cartesian trees, no LCA. Time is handled by **benchmarking** (§6.2: "Execution seems constant-time (0.83 µs on average)"); §7 concedes formal verification of time complexity would be "more convincing" and is not done.
- ITP 2019 proves LOUDS navigation and dynamic bit vectors as red-black trees. Its single machine-checked size statement is exact: `Lemma size_LOUDS t : size (LOUDS t) = 2 * number_of_nodes t - 1`. Its own Conclusion defers complexity to future work and states that for dynamic bit vectors "we will first need to properly define a framework for space and time complexity."
- The 2021 artifact repository contains **no** RMQ, Cartesian-tree, LCA, balanced-parentheses, or Euler-tour file (verified against the complete recursive git tree, not a root listing). `jacobson_rank_complexity.v` proves exact closed-form real-valued equalities (`storage_for_first_level_dir`, `storage_for_second_level_dir`), contains **15 global `Axiom` declarations** (log laws, the `nat2ulst` encoder and its length, and an int/adjust block), and imports no asymptotics library. The `opam` file declares exactly two dependencies (`coq`, `coq-mathcomp-ssreflect`), so mathcomp-analysis — the only Landau/`littleo` library in that ecosystem — is **not in the build at all**. The file is absent from ITP 2019's Table 2 and is therefore not part of the refereed contribution.
- **The single most important discovery in this modality:** *Safe Low-level Code Generation in Coq Using Monomorphization and Monadification*, Tanaka, Affeldt & Garrigue, **Journal of Information Processing 26:54–72, DOI 10.2197/ipsjjip.26.54, 2018** — §6.5.2 "The Complexity of rank Function" **machine-checks query cost** in a monadic bit-counting model: `RankInitNumBitsExamined` (bits examined by `rank_init` is O(n)) and `RankLookupNumBitsExamined` (bits examined by `rank_lookup` is O(1), bounded by 64). §3.4.3 machine-checks operation counts for `rev`/`rev'`. This is the item that kills a claim we had been carrying. See §2.3 and §4.
- Forward-citation sweep found exactly one non-trivial descendant outside the group: the Cheung / Moffat / Rizkallah Isabelle line (BWT, suffix arrays), which is functional-correctness-only.

**What could NOT be established.**

1. **Forward-citation coverage is demonstrably incomplete, and this is the most serious gap in the modality.** OpenAlex reports `cited_by_count = 1` for ITP 2019 and 4 for ICFEM 2016; Semantic Scholar reports 4 and 3. Those numbers are implausibly low for a 2016/2019 ICFEM-and-ITP pair and indicate poor indexing, not a quiet literature. Google Scholar was not reachable. A citing paper that mechanizes an asymptotic bound or a cost model could exist and be invisible to every query run.
2. **The ICFEM 2016 artifact itself was never inspected.** The code URL in the paper (`https://staff.aist.go.jp/tanaka-akira/succinct/index.html`) returns HTTP 404 and no mirror surfaced. The exhibited lemma `rank_spaced1` does **not** appear in the 2021 repository, so the 2021 repo is a re-done development, not the 2016 one. It is therefore formally possible that the lost 2016 artifact contained an asymptotic statement the 2021 rewrite dropped. **This directly weakens our sharpest available finding and is the reason claim §4.2 is retired rather than defended.**
3. The Springer page for ICFEM 2016 was never retrieved (303 redirect to the identity provider). LNCS volume 10009 and pages 243–260 come from dblp plus ITP 2019's own reference [24] — good corroboration, not the publisher record. Note that a second verifier in this session reached the *opposite* conclusion about whether volume 10009 clears our field policy; see §5.9.
4. Non-English and workshop-grey literature was **not** swept. A JSSST 2018 Japanese-domestic version of the tree-algorithms paper surfaced and was not read. Xuanrui Qi's thesis, if one exists, was not located.
5. The Coq/Rocq opam package index and other `affeldt-aist` repositories (notably `infotheo` and `seplog`, which the artifact's own comments cite as the homes of the proofs it axiomatizes) were **not** swept.

---

### 1.2 Modality B — other proof assistants (Isabelle/AFP; ACL2, HOL4, PVS, Agda, Why3, Dafny, F*)

**Scope.** Everything outside Coq and Lean.

**Queries run.** Twenty-seven AFP full-text queries were run through the site's own search (which indexes titles, abstracts, authors, topics):

```
succinct | rank select | balanced parentheses | wavelet tree | lowest common ancestor
bitvector | compact data structure | Euler tour | LOUDS | FM-index | cell probe | probe
word RAM | Elias-Fano | information-theoretic lower bound | bits per node | range minimum
Cartesian tree | bit vector | entropy | compressed | space efficient | Jacobson | Catalan
tree encoding | query time | trace model
```

Plus exhaustive topic enumerations: **Computer science / Data structures (all 75 entries)**, Computer science / Algorithms (full top-level listing 2007–2026), Computer science / Algorithms / Graph (all 24). Plus the AFP statistics page (1016 entries, 604 authors, ~5,350,600 LOC). Plus direct reads of AFP theory sources (`BurrowsWheeler/Rank_Util.html`, `Select_Util.html`, VEB `VEBT_Space.thy` / `VEBT_Bounds.thy`, `Comparison_Sort_Lower_Bound.thy`, `Source_Coding_Theorem.thy`, `Prefix_Free_Code_Combinators` and `Frequency_Moments` outline PDFs). Plus the full front matter and 27-chapter table of contents of *Functional Data Structures and Algorithms: A Proof Assistant Approach* (Nipkow ed., ACM Books 2025). Plus ~20 web searches over ACL2, HOL4, PVS, Agda, Why3, Dafny, F*.

**What was found.**

- `succinct` returns **3 AFP hits, all ordinary-English usage** (Kurz & Abdulaziz 2018; Kleppmann et al. 2018; Nipkow 2011). `rank select`, `balanced parentheses`, `wavelet tree`, `lowest common ancestor`, `bitvector`, `compact data structure`, `Euler tour`, `LOUDS`, `FM-index`, `cell probe`, `probe`, `word RAM`, `Elias-Fano`, `information-theoretic lower bound`, `bits per node` all return **no results**.
- **Eberl, "Lower bound on comparison-based sorting algorithms", AFP 2017** (submitted 15 March 2017; BSD; depends on Landau Symbols, List Index, Stirling's formula). Reifies the algorithm as `datatype 'a sorter = Return "'a list" | Query 'a 'a "bool ⇒ 'a sorter"` with `primrec count_queries` charging `Suc` per `Query`, worst case as a `Max` over an ordering set, and proves `log 2 (fact (length xs)) ≤ real (count_wc_queries Rs sorter)` plus the asymptotic `count_queries_bigomega : … ∈ Ω(λn. n * ln n)`. Eberl himself credits the decision-tree model to Cormen et al. (CLRS, 2nd ed., 2001). **This is a mechanized structural anti-oracle discipline from 2017.**
- **Ammer & Lammich, "van Emde Boas Trees", AFP 2021.** Proves timing bounds with **explicit constants** (`T_member t x ≤ (1+height t)*15`, and `T_member t x ≤ 30 + 15 * lb (lb u)`), refines them into Imperative HOL with Time so that the manually defined timing functions leave the trusted base, **and proves a space theorem** — `space_bound : invar_vebt t n ⟹ u = 2^n ⟹ space t ≤ 12 * u`, in datatype-constructor units, linear in universe size. Also proves build-time bounds (`T_buildup n ≤ 26 * u`), ground our succinct spoke explicitly leaves unproved.
- **Karayel, "A Combinator Library for Prefix-Free Codes", AFP 2022** — machine-checked per-value **bit-length** results, compositional: `bit-count-append`, `dependent-bit-count`, `elias-gamma-bit-count`, `exp-golomb-bit-count-exact`, `int-bit-count`, `set-bit-count-est`. Paired, same author, **same submission date**, with **AFP "Formalization of Randomized Approximation Algorithms for Frequency Moments"** (linked publication: Karayel, ITP 2022, LIPIcs 237, 21:1–21:21, DOI 10.4230/LIPIcs.ITP.2022.21), which proves `f0-exact-space-usage` (bit-count ≤ a space-usage function) chained to `f0-asymptotic-space-complexity`, an **asymptotic space bound in bits stated in Landau O-notation**. Karayel's ITP 2022 abstract describes the library as existing "for the verification of space complexities."
- **Hibon & Paulson, "Source Coding Theorem", AFP 2016** (filed under *Mathematics / Probability theory*, which is why data-structure searches miss it). Proves `theorem rate_lower_bound: shows "𝖧(X) ≤ code_rate enc X"` plus `theorem McMillan`. This is a genuine mechanized information-theoretic lower bound on **expected** code-word length for a **variable-length** code relative to a **source distribution**.
- **Blanchette, "The Textbook Proof of Huffman's Algorithm", AFP 2008**, journal version *Proof Pearl: Mechanizing the Textbook Proof of Huffman's Algorithm*, JAR 43(1):1–18, 2009, DOI 10.1007/s10817-009-9116-y. Proves `optimum_huffman`, minimality of weighted path length among comparable trees. Blanchette's own Related Work names an earlier Coq formalization: **Laurent Théry, "A Correctness Proof of Huffman Algorithm", October 2003**, and "Formalising Huffman's Algorithm", TR CS 034/2004, University of L'Aquila — so mechanized Huffman optimality dates to **2003**, five years before the AFP entry.
- **Cheung & Rizkallah, "Formalised Burrows-Wheeler Transform", AFP 2025** (submitted 17 January 2025) is the only AFP entry with theories literally named `Rank_Util`, `Select_Util`, `Rank_Select`. Reading the sources resolves the scare: `definition rank :: "'a list ⇒ 'a ⇒ nat ⇒ nat" where "rank s x i ≡ count_list (take i s) x"`, with `select` a three-case list recursion. These are LF-mapping ingredients — rank of a *character* in a *prefix* — not succinct dictionaries. No bitvector, no directory, no redundancy, no constant-time claim. Note the bibliographic trap: the AFP entry is "Formalis**ed**" (Cheung & Rizkallah); the CPP 2025 paper is "Formaliz**ed**" (Cheung, **Moffat**, Rizkallah, DOI 10.1145/3703595.3705883, pp. 187–197). The CPP abstract explicitly positions compressed-index work as **future**: the formalization "provides the necessary foundation for verifying the various algorithms for compression and text search that operate on BWT-transformed sequences."
- The 27-chapter ACM Books *FDSA* volume — the flagship Isabelle data-structures reference, covering "both functional correctness and running time analysis" — has **no** chapter on succinct or compact structures, rank/select, bitvectors, RMQ, Cartesian trees, or LCA. Its cost model is step-counting functions (Appendix B, "Time Functions"): time, never space in bits and never memory probes.

**What could NOT be established.**

1. **The AFP search indexes abstracts, not theory content — and this demonstrably matters.** Searching `rank select` over the AFP returns **no results**, yet the Burrows-Wheeler entry ships theories named `Rank_Util`, `Select_Util`, `Rank_Select`. Stopping at the search box would have produced a false negative. Mitigation was three exhaustive topic enumerations plus direct theory-source reads. **We did not enumerate all 1016 entries and did not grep the ~5.35M lines of AFP proof text.** A succinct construction could still be buried inside an entry whose abstract never says so. Closing this properly requires downloading the AFP tarball and grepping the sources; that was not done.
2. **Topics not enumerated:** Automata and Formal Languages (77), Security (55) + Cryptography (16), Semantics and Reasoning (38), Programming Languages and all subtopics, Concurrency, Data Management Systems, Functional Programming (26), Combinatorics (55), Probability Theory (33), and nine of the ten Algorithms subtopics. Note that *Source Coding Theorem* sits under Mathematics/Probability theory — direct proof that relevant material hides in unexpected topics.
3. **Non-Isabelle provers were web-searched only; their corpora were never enumerated.** For ACL2, HOL4, PVS, Agda, Why3, Dafny and F* we ran targeted searches and found nothing on succinct structures, rank/select indices, or RMQ. **This is the weakest part of the entire novelty search.** We did not open, browse or grep: the ACL2 community books, the HOL4 examples tree, the PVS NASA libraries, `agda-stdlib` or the Agda package index, the Why3 gallery, the `dafny-lang` corpus, or the F* / HACL* / EverParse repositories. Web search does not reliably index source repositories. **Nothing licenses a statement that no succinct structure exists outside Coq and Lean.**
4. ITP, CPP, JAR, JFP, FM, ICFEM, VSTTE, TACAS and NASA Formal Methods tables of contents were **not** swept year by year. The CPP 2025 TOC was seen incidentally.
5. `dl.acm.org` returned HTTP 403 for the CPP 2025 BWT paper and Springer redirected ICFEM 2016 to an authentication endpoint.
6. Two 2026-dated RMQ-theory items surfaced and were **not** chased: arXiv 2601.13195 "Quantum Data Structure for Range Minimum Query", and arXiv 2603.25914, an `Ω((log n / log log n)²)` cell-probe lower bound for dynamic Boolean data structures. Neither is a formalization, but they indicate the classical RMQ literature is still moving in 2026 and our background citations may be stale.
7. All queries were in English.

---

### 1.3 Modality C — the Lean ecosystem

**Scope.** Mathlib, CSLib, the Lean community repositories, and Lean-wide GitHub code search.

**Queries run.** Fifteen web searches plus ~25 `gh search code --language=lean` probes:

```
rangeMinimum | RMQ | cartesianTree (0) | succinct | succinct structure (0)
balanced parentheses | amortized | cellProbe (0) | DFUDS (0) | LOUDS | Jacobson
sparseTable | eulerTour | lowestCommonAncestor (0) | wordRAM (0) | probeCount
bitsUsed (0) | spaceBound | rangeMin | minIndex | queryCost | rankSelect (0)
selectOne rank (0)
gh search code --repo leanprover-community/mathlib4: Catalan | complexity
gh search repos: succinct --language=lean | rmq --language=lean
```

Plus direct fetches of Mathlib doc pages (`Catalan`, `Catalan/Basic`, `Catalan/Tree`, `Pigeonhole`, `InformationTheory/Hamming`, `Data/Nat/Choose/Central`), Loogle name queries, the full recursive git trees of `Shreyas4991/Algolean` and `leanprover/cslib`, and raw source of `Algolean/Models/ReadOnlyVec.lean`, `Algolean/QueryModel.lean`, `Algolean/LowerBounds/ComparisonSort.lean`, `Algolean/Complexity/Basic.lean`, `Cslib/Algorithms/Lean/TimeM.lean`, `Cslib/Algorithms/Lean/MergeSort/MergeSort.lean`.

**What was found.**

- **Algolean** (artifact name; the GitHub description is "A library of algorithms and complexity theory written in Lean using a lightweight free monad framework called the 'query-combinator' model"). `CITATION.cff` v1.0.0, released 2026-03-17, **six authors**: Shreyas Srinivas (CISPA), Ethan Ermovick, Tanner Duve, Bashar Hamade, Johannes Tantow, Samuel Schlesinger. Apache-2.0. Depends on CSLib (rev v4.31.0). **This is the most dangerous item found anywhere in the search.** Verbatim:
  ```lean
  inductive ReadOnlyVec (α : Type) : Type → Type _ where
    | read (a : Vector α n) (i : Fin n) : ReadOnlyVec α α
  def ReadOnlyVec.natCost : Model (ReadOnlyVec α) ℕ where
    evalQuery | .read a i => a[i]
    cost _ := 1
  ```
  That is a Lean 4 model in which indexed reads are the charged primitive at one unit each — a cell-probe-shaped read-charging model, already public. It also proves a machine-checked counting lower bound, `cmpSort_lower_bound : … worstTime P ≥ (n / 2) * Nat.log 2 (n / 2)`, by pigeonhole/decision tree, with `sorry`-free proof.
- **CSLib**, arXiv:2602.04846v1 [cs.LO], 4 Feb 2026, eight authors (Barrett, Chaudhuri, Montesi, Grundy, Kohli, de Moura, Rademaker, Yingchareonthawornchai). Self-identifies as a **white paper**. `TimeM` is a cost monad with an admittedly untrusted `time` field. Three statements matter directly: (i) "by giving users control over tick placement, the framework enables experimentation with different cost models"; (ii) "it cannot directly prove statements of the form 'no algorithm can solve problem X faster than f(n)'"; (iii) "In the longer run, we plan to complement this approach with heavier-weight methods that formalize complexity via **explicit RAM and query models**" — i.e. explicit query models are stated **future** work.
- **Mathlib** already has the Catalan infrastructure: `BinaryTree.treesOfNumNodesEq_card_eq_catalan`, `catalan_eq_centralBinom_div`, `Nat.succ_mul_catalan_eq_centralBinom`, `Nat.four_pow_le_two_mul_self_mul_centralBinom`, `Nat.four_pow_lt_mul_centralBinom`, `DyckWord.card_dyckWord_semilength_eq_catalan`, plus the `Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to` pigeonhole family. Chaining the `centralBinom` inequalities yields `4^n ≤ 2n(n+1)·catalan n` — the direct analogue of our `shapeCount_quadratic_lower`.
- **complexitylib** (Samuel Schlesinger; Apache-2.0; head of `dev` = `645b5676bdd64c6b7a36f80ab8e763055c7e89d9`, 2026-07-29) machine-checks `DSPACE`/`NSPACE` with big-O, a `Complexity.LittleO`, the deterministic time hierarchy theorem, Hoare-style space judgements, and — not previously noticed — `Circuits/Shannon.lean`, a mechanized counting/pigeonhole circuit lower bound.
- **CLRS-Lean** (`TankTechnology`; individual account, blog identifies **Anjie Xu**, Peking University; created 2026-06-23; no license) reports 30/35 chapters and 1326/1326 selected theorems, with real machine-checked cost results at scale (Strassen `Θ(n^lg 7)`, randomized SELECT, union-find amortized traversal, parallel work/span, Fibonacci-heap degree, van Emde Boas `O(log log u)`, dynamic tables). Its docs state that "full RAM/pseudocode semantics remain a future refinement target."
- **Zero** hits for RMQ, Cartesian trees, rank/select dictionaries, balanced-parentheses navigation, succinct or bit-counted representations, or any theorem bounding the bits of a data structure's payload, anywhere in the Lean corpus reached.

**What could NOT be established.**

1. GitHub code search indexes only a subset of repositories and only indexed branches. It matched fuzzily: the `RMQ` query returned unrelated identifiers such as `AllowsTermQ5`, so a genuinely named RMQ development could rank below the noise floor. Zero-result queries are weak evidence at best.
2. **A tool defect invalidated part of the sweep and was caught mid-session.** `gh search code` silently returns **empty** for quoted phrases and for inline `repo:` qualifiers. First attempts at `"succinct data structure"`, `"balanced parentheses"`, `"time credit"`, `"binary tree"` and repo-scoped Mathlib queries all returned nothing **for this reason** and are **not** valid negative results. The important ones were re-run unquoted; the phrase queries `succinct data structure` and **`time credit` were NOT re-run in a valid form**, so Lean-side time-credit / separation-logic-style cost work is **unswept**.
3. **Lean Zulip was not searched natively.** The archive is only partially indexed by web search. Any Lean succinct-structure or RMQ discussion living only in Zulip would have been missed.
4. **Reservoir, the Lean package registry, was not enumerated.** This is the single highest-value follow-up for the Lean modality.
5. Mathlib's `InformationTheory` namespace was checked only via the `Hamming` module page. Whether Mathlib now has entropy / KL machinery is **not** established and must not be asserted either way.
6. Mathlib's absence of algorithmic complexity theory rests on one repo-scoped keyword search, not a module-index audit.
7. Batteries/std were not audited directly.
8. CLRS-Lean's claimed union-find inverse-Ackermann bound was **not** confirmed at source; two extractions of the same files gave inconsistent readings (`CostedExecution.lean` yields only a logarithmic bound, `≤ ops.length * (2 * Nat.log2 n + 3)`, while `InverseAckermann.lean` reportedly carries the α bound). **Do not assert either that CLRS-Lean proves the α bound or that it fails to.**
9. No repository was built, no Lean proof was kernel-checked by us, and no claimed theorem was confirmed `sorry`-free by us.

**Incidental, not prior art, flagged for the coordinator.** `gh search repos rmq --language=lean` returned exactly one hit: `patternscientist/rmq`, marked **PUBLIC**, updated 2026-08-07 — the operator's own account. If that repository is genuinely public it is a public disclosure with a date, bearing on both the public-claim-sync roadmap item and any future priority framing. Its visibility should be confirmed deliberately rather than by accident.

---

### 1.4 Modality D — mechanized cost frameworks

**Scope.** Every tradition of mechanized cost reasoning: time credits, AARA, cost-aware type theory, refinement-with-time, monadic tick models, and mechanized complexity theory.

**Queries run.** ~30 web searches, including:

```
mechanized cell-probe model proof assistant formalization data structure lower bound
Guéneau Charguéraud Pottier "time credits" separation logic asymptotic complexity O filters
formal verification "cell probe" cost model Coq Lean charging memory accesses computation between probes free
Atkey "amortised resource analysis" separation logic mechanized Coq
formalization "I/O complexity" OR "external memory model" Isabelle Coq verified counting memory accesses
Iris "time credits" heap_lang mechanized complexity Mével Jourdan Pottier
calf "cost-aware logical framework" Niu Sterling Grodin Harper POPL 2022 decalf 2024 Agda cost model
mechanized word-RAM model proof assistant "time invariance thesis" Forster Kunze
verified cost model soundness adequacy "cannot cheat" mechanized complexity proof trace faithfulness oracle access
"cell probe" OR "probe complexity" formalized proof assistant Lean Coq Agda mechanized data structure query lower bound 2024 2025 2026
mechanized proof "number of memory accesses" OR "word reads" constant bound data structure query verified store model charged reads
"time credits" separation logic charge only heap accesses reads model "cell probe" alternative cost metric Iris CFML
```

T1 fetches: the CSLib PDF (pp. 1–16); the calf POPL 2022 PDF; the ITP 2019 LIPIcs PDF; the anonymous ICFP '26 submission PDF (pp. 1–3); arXiv abs pages for 2309.11056 and 1802.01336; the `Comparison_Sort_Lower_Bound` AFP entry and its outline PDF; `uds-psl/coq-library-complexity` repo page, full recursive tree, README, and raw `ONotation.v` and `SpaceBoundsTime.v`; Guéneau's publication page; Grodin's publications page; the ITP 2025 accepted-papers page.

**What was found.**

- **calf**, Niu, Sterling, Grodin & Harper, *Proc. ACM Program. Lang.* 6, POPL, Article 9, 31 pp., DOI 10.1145/3498670 (Jan 2022). Agda-mechanized. Restricted charging is calf's **declared framework-level stance**, not a case study: "we do not associate a particular cost semantics to calf itself but instead promote the use of calf as a cost-aware metalanguage for expressing algorithm-specific/non-uniform cost models"; "a common cost model for sorting algorithms counts the number of comparisons, which does not account for the cost of (e.g.) constructing lists… This is the prevailing perspective we take in calf." Also proves an internal **noninterference** property: input/output behaviour cannot depend on cost.
- The **time-credit branch** (Guéneau–Charguéraud–Pottier ESOP 2018 pp. 533–560 DOI 10.1007/978-3-319-89884-1_19; Charguéraud–Pottier JAR 62(3):331–365 DOI 10.1007/S10817-017-9431-7; Mével–Jourdan–Pottier ESOP 2019; Pottier–Guéneau–Jourdan–Mével thunks/debits; Atkey ESOP 2010). Important correction to a framing we had been using: ESOP 2018 does **not** charge every step — verbatim, "certain operations, such as calling a function or entering a loop body, cost one unit of time, and **every other operation costs nothing**." It is an abstract source-step model that charges only designated events. **"They charge every step, we charge only probes" is therefore not a valid distinguisher.**
- **`coq-library-complexity`** (uds-psl; created 2019-05-07, last push 2023-07-14) machine-checks **little-o** (`ino`, a reals-free formulation), Cook–Levin (Gäher & Kunze, ITP 2021, LIPIcs 193, art. 20, pp. 20:1–20:18), the time hierarchy theorem, the time-invariance thesis (Forster, Kunze, **Smolka**, Wuttke, ITP 2021, art. 19), and TM **space** bounds. It contains no cell-probe model, no data structure, and no query-cost accounting against an encoding.
- **Danielsson, POPL 2008, pp. 133–144** is the acknowledged ancestor of the annotation/tick-monad style that CSLib reuses — ~18 years of precedent for the technique.
- **No mechanized cell-probe cost bound was found** — charging memory probes into a modeled store with computation between probes free — for any data structure, in any proof assistant. This negative rests on three *affirmative* receipts rather than on search silence: (i) CSLib (Feb 2026) states explicit RAM/query models are **future** work and that its framework cannot prove lower bounds; (ii) `coq-library-complexity`, the most mature mechanized complexity corpus, confirmedly contains no cell-probe model and no data-structure query complexity; (iii) the Affeldt/Garrigue/Qi/Tanaka succinct line proves correctness only, with complexity deferred by its own conclusion.

**What could NOT be established.**

1. **The Iris/CFML case-study corpus was not enumerated.** We did not browse `iris-project.org`'s publication list, the Iris Coq development, or the CFML case-study index. Iris and CFML have real heaps; a development that instruments time credits to charge only heap loads would be the direct refutation and would most likely be a case study or artifact rather than a titled paper. **This is the single most likely place a defeater is hiding.**
2. **The Zhan–Haslbeck cost model was not characterised.** Only the abstract of arXiv:1802.01336 was read; whether Imperative HOL with Time charges array/heap reads distinctly from other steps is unknown. The paper body and associated AFP entries must be read before any statement of the form "no one charges memory reads" is made.
3. Nipkow's "Verified Algorithm Analysis" project page (`www21.in.tum.de`) refused the connection. Search results indicate its case studies include lower bounds on comparison-based sorting, list-update algorithms, root-balanced trees and QuickSort comparison counts — i.e. more mechanized restricted-charge analyses than we could enumerate.
4. `dl.acm.org` returned HTTP 403 for the decalf record, so its volume/issue/article/DOI are unknown and are **omitted**, not guessed.
5. One item is **anonymous and under review**: "A Lightweight Approach to Formal Algorithmic Complexity (Functional Pearl)", an ICFP '26 submission hosted on Utrecht webspace, naming no authors, acceptance unknown. It cannot be cited as-is and must be re-checked before submission.
6. One item's year is **unresolved on purpose**: Pottier/Guéneau/Jourdan/Mével "Thunks and Debits in Separation Logic with Time Credits" — Guéneau's own page lists 2023; the iris-project.org filename says `2024-popl-…`. **Do not cite with a year until resolved.**
7. Proceedings TOCs were not swept (only ITP 2025 accepted papers).

---

### 1.5 Modality E — the classical succinct-RMQ literature

**Scope.** Verification of every classical citation in `references.bib`, plus a check for classical work we are missing, plus a recency check.

**Queries run.** ~30 targeted bibliographic searches (Fischer–Heun, Fischer, Vuillemin, Gabow–Bentley–Tarjan, Harel–Tarjan, Bender–Farach-Colton, Jacobson, Clark, Munro–Raman, Raman–Raman–Rao, Sadakane, Navarro–Sadakane, Navarro, Liu–Yu, Liu, Gál–Miltersen, Pătrașcu, Golynski, Davoodi–Raman–Satti, Munro–Nicholson–Benkner–Wild, plus recency sweeps for 2025/2026 succinct RMQ). T1 reads: the authors' own Fischer–Heun PDF (`ae.iti.kit.edu/download/rmq.pdf`, title page + §1 + §5 + conclusions); arXiv:0812.2775v3 (Fischer 2010) extracted and read; arXiv:2004.05738 (Liu–Yu) pp. 1–4; the SEA 2017 LIPIcs paper; the Gál–Miltersen BRICS RS-03-44 preprint, text extracted; dblp records for essentially every classical entry.

**What was found.**

- **A confirmed factual error in `rmq.tex`.** Fischer & Heun 2011 §1.1 defines the nomenclature, and its abstract states: "In setting (2), we give a data structure of size 2n + o(n) bits and query time O(1)" — setting (2) being where "the input array is only available at construction time". Table 1.1 marks the `2n + o(n)` rows (Thm 5.8, Cor 5.9) `(**)` = **non-systematic**, and §5 is literally titled "Optimal Preprocessing in the Non-Systematic Setting." Independently corroborated by Baumstark–Gog–Heuer–Labeit, SEA 2017 (LIPIcs 75, art. 12): the FH11 index answers "without consulting the original array." **Our related-work paragraph calls it systematic.** See §5.3.
- Fischer 2010 is **a preliminary version of FH11's §5** (FH11's first-page footnote names LATIN 2010; FH11's reference [17] is Fischer 2010). So the systematic/non-systematic contrast our sentence draws across the two citations is not merely reversed — **it is nonexistent**: both are non-systematic.
- **Fischer 2010 declares itself a word-RAM result on page 1 and in §2**: "Throughout this article, we use the standard word-RAM model of computation, where fundamental arithmetic operations on words consisting of Θ(log n) consecutive bits can be computed in O(1) time." The string "cell probe" occurs **once** in the whole document, inside the title of its reference [17]. **Citing `Fischer10` for the cell-probe convention is wrong.** See §5.4.
- **Fischer 2010 states the counting lower bound explicitly**, p. 3: "the information-theoretic lower bound (for non-systematic schemes) of 2n − Θ(log n) bits… any scheme must use at least log(C(2n−1,n−1)/(2n−1)) = 2n − Θ(log n) bits." Our manuscript calls this bound "implicit in the classical literature." **It is explicit.** See §5.6.
- **Liu 2021** (arXiv:2111.02318, CoRR-only, confirmed twice at dblp) already carries the exact constant: `2n − 1.5 log n + n/(log n)^{O(t log² t)}`.
- **Four classical papers are missing from `references.bib`** and at least two are load-bearing:
  - **Sadakane, "Succinct data structures for flexible text retrieval systems", J. Discrete Algorithms 5(1):12–22, 2007, DOI 10.1016/j.jda.2006.03.011** — the **first non-systematic succinct RMQ** (`4n + o(n)`, O(1) query), built by **BP encoding of the Cartesian tree plus an o(n) LCA computation therein**. That is precisely the recipe family our §5.1 describes. A precursor exists: Sadakane, "Space-Efficient Data Structures for Flexible Text Retrieval Systems", ISAAC 2002, pp. 14–24, DOI 10.1007/3-540-36136-7_2 — **we could not verify whether the RMQ structure already appears in the 2002 version**, which matters because it would move the priority date.
  - **Fischer & Heun, ESCAPE 2007, LNCS 4614, pp. 459–470, DOI 10.1007/978-3-540-74450-4_41** — the actual **systematic** `2n + o(n) + |A|` constant-time scheme. **Citation hazard:** its abstract advertises a `2n − o(n)` lower bound; Fischer 2010 footnote 2 reports that claimed min-probe-model bound as **wrong** (attributed to a personal communication from S. Srinivasa Rao, Nov 2007). **Never cite it for a lower bound.**
  - **Gál & Miltersen, "The cell probe complexity of succinct data structures", Theor. Comput. Sci. 379(3):405–417, 2007, DOI 10.1016/j.tcs.2007.02.047** (earlier: ICALP 2003, pp. 332–344, DOI 10.1007/3-540-45061-0_28). Source of the systematic/non-systematic nomenclature we use uncited, **and** of the free-computation-between-probes convention: verbatim, "The time t of the query algorithm is the number of bits it reads in φ(x)"; "as we only charge for reading bits in φ(x), not for computation". Note: the term "**encoding** data structure" is **not** theirs (5 occurrences, all ordinary usage) — attribute only systematic / non-systematic / index.
  - **Pătrașcu, "Succincter", FOCS 2008, pp. 305–313** — `O(n/log^c n)` redundancy at constant query time. Relevant because the classical redundancy frontier is `n/polylog n` while our overhead envelope is proved only little-o-linear.
- Recency: **Munro, Nicholson, Benkner & Wild, "Hypersuccinct Trees", ESA 2021, DOI 10.4230/LIPIcs.ESA.2021.70** achieves worst-case-optimal `2n + o(n)` **and drops below 2n on average** (reported `1.736n + o(n)` in expectation for random permutations); Hamada et al., ESA 2024 (arXiv:2407.00573) implements average-case-optimal RMQ "spending less than 2n bits". Davoodi, Raman & Satti, COCOON 2012 give two further distinct `2n + o(n)` Cartesian-tree representations. Nothing in the classical literature is machine-checked.

**What could NOT be established.**

1. **Paywalls.** `epubs.siam.org` and `sciencedirect.com` returned HTTP 403. The SIAM Fischer–Heun text was read from the **authors' own PDF**, not the publisher record. **The Sadakane JDA 2007 paper itself was never read**; its fields rest on Fischer 2010's printed reference list, the dblp record, and citing summaries. Springer chapter pages for Fischer 2010 and Bender–Farach-Colton bounced through auth redirects.
2. Whether the ISAAC 2002 Sadakane precursor already contains the RMQ structure is **unknown**.
3. Fields that could **not** be raised to primary confidence and must stay omitted: Clark 1996 (no dblp record found; no repository copy reached; **the middle initial "R." was not confirmed by any source — the thesis scan front matter showed "David Clark"**); Golynski SODA 2009 page range (search summary only); the ICALP 2003 LNCS volume for Gál–Miltersen.
4. **Not swept:** 2-D RMQ and encoding complexity; the bounded-alphabet RMQ encoding line (CPM 2025 / TCS 2026); dynamic RMQ; the Ferrada–Navarro practical-engineering line; Pătrașcu–Viola and the succinct-rank lower-bound line; and the `[DRS17]` reference Liu–Yu list among the RMQ state of the art, which was never resolved to a paper.

---

### 1.6 Modality F — bibliographic integrity of `references.bib` and `rmq.tex`

**Scope.** Independent field-by-field verification of all 23 `references.bib` entries, plus verification of the three specific manuscript defects the audit brief named.

**Queries run.** 20 dblp API queries (one per entry, plus reformulations after two HTTP 500s), plus direct fetches of the ICFEM 2016 author preprint, the ITP 2019 LIPIcs PDF, the ITP 2019 dblp record, the FSCD 2016 DROPS entity and opus pages, arXiv:1802.01336, and four general web searches for Clark 1996, Navarro 2016, and AFP coverage.

**What was found.** Detailed in §5. Headline: **one hard factual error in `references.bib`** (`ZhanHaslbeck18` title), **three manuscript prose defects**, one entry typed without disclosing that it is a two-page invited-talk abstract, and a systematic mismatch between the bib header's stated field policy and the ledger's.

**What could NOT be established.**

1. **The AFP question remains unresolved in this modality.** `isa-afp.org/search/?q=succinct` is JavaScript-driven and returned nothing parseable; three general searches surfaced only unrelated entries. (Modality B did far better; see §1.2. The ledger's limitation item 1 should be *rewritten*, not deleted.)
2. Springer blocked (303 auth redirect) for ICFEM 2016, so **the LNCS volume number reported by a search summary as 10009 was NOT independently confirmed in this modality** — while modality A concluded it *is* verified. See §5.9 for the disagreement.
3. **Single-database reliance.** Most fields rest on dblp alone. dblp's API returned HTTP 500 twice. **Series volume numbers (LNCS 1776, 6034, 9236, 10801, 12699) are not confirmed by dblp at all** — they are only *consistent with* DOI ISBN prefixes, which is inference, not verification.
4. A **methodological hazard worth recording**: one WebFetch of `https://arxiv.org/pdf/1802.01336` returned a **fabricated title** ("Verifying Efficient Algorithms in Isabelle/HOL") together with a case-study list not in the abstract. It was caught by cross-checking against dblp and discarded. **PDF-derived bibliographic fields must be cross-checked against a structured record before entering the bibliography.**

---

## 2. Prior art that constrains us

Each item below genuinely narrows what we may write. Items are ordered by how much they constrain.

### 2.1 The frozen constraint — mechanized succinct data structures (T1)

**Akira Tanaka, Reynald Affeldt, Jacques Garrigue, "Formal Verification of the rank Algorithm for Succinct Data Structures", ICFEM 2016.** Receipt: author preprint fetched and read end to end (19 pp.), plus dblp record `conf/icfem/TanakaAG16`. Tier **T1** (body), **T2** (venue/pages).

Abstract and Conclusion both state, verbatim: *"To the best of our knowledge, this is the first application of formal verification to succinct data structures."*

**Restriction.** No claim of the form "first mechanized succinct data structure", in any phrasing, at any scope broader than RMQ. Already frozen; restated here so it cannot drift back.

**A sharper trap than the abstract.** §2.2 promises formality: *"It can be shown (and we will do it formally in Sect. 5.3) that the directories require only n/log₂ n + 2n log₂ log₂ n / log₂ n [∈] o(n) bits."* A referee can quote that one sentence — with its parenthetical and its literal set-membership in `o(n)` — against **any** unqualified priority claim about mechanized sublinear redundancy. Any rebuttal must engage §2.2 **and** §5.3, not §5.3 alone.

### 2.2 Affeldt, Garrigue, Qi & Kazunari Tanaka, ITP 2019 (T1)

Receipt: full LIPIcs PDF read (19 pp.); DROPS entity page; dblp `conf/itp/AffeldtGQT19`. Tier **T1**.

Abstract: *"While both representations are well-known, we believe this to be their first formalization and a needed step towards provably-safe implementations of big data."* — scoped to LOUDS and dynamic bit vectors, hedged.

**Restriction.** (a) Their priority claim is **narrower** than TAG16's; do not describe the two papers jointly as "stating priority for mechanized succinct-structure verification". (b) The four authors are **not** "the same team plus Qi" — see §2.3 and §5.1.

### 2.3 The two Tanakas (T1) — a manuscript defect, not a prior-art constraint

Receipts, all T1, three independent: (i) ITP 2019 page 1 lists **Kazunari** Tanaka, Graduate School of Mathematics, Nagoya University; (ii) ITP 2019's own Acknowledgements thank *"the projects' participants, in particular **Akira Tanaka** for his comments on code extraction"* — Akira Tanaka is **acknowledged, therefore not an author**; (iii) ITP 2019 reference [24] lists ICFEM 2016 as *"Akira Tanaka, Reynald Affeldt, and Jacques Garrigue."*

So ICFEM 2016 = Akira Tanaka + Affeldt + Garrigue (three). ITP 2019 = Affeldt + Garrigue + Qi + Kazunari Tanaka (four). The common core is **Affeldt + Garrigue only**. `references.bib` is correct on both entries; `rmq.tex` is not. Repair in §5.1.

### 2.4 Query cost IS already machine-checked for a succinct structure (T1) — the hardest constraint found

**Akira Tanaka, Reynald Affeldt, Jacques Garrigue, "Safe Low-level Code Generation in Coq Using Monomorphization and Monadification", Journal of Information Processing 26:54–72, DOI 10.2197/ipsjjip.26.54, 2018.** Receipt: J-STAGE article page + full-text PDF read (pp. 54–69) + dblp `journals/jip/TanakaAG18`. Tier **T1**.

§6.5.2, titled "The Complexity of `rank` Function", machine-checks:

```
RankInitNumBitsExamined b s          -- bits examined by rank_init is O(n)
RankLookupNumBitsExamined b s i :
  let aux := rank_init b s in let n := bsize s in
  rank_lookupM aux i = (i %% (bitlen n).+1, rank_lookup aux i)
                                     -- bits examined by rank_lookup is O(1), max 64
```

§3.4.3 machine-checks operation counts for `rev`/`rev'` via a writer monad `counter_with A := nat * A`. The Conclusion claims time complexity of `rank` as a contribution.

**Restriction.** **Drop any "first machine-checked query-cost bound for a succinct data structure" formulation entirely.** It is dead. The residual differences are real but must be stated as differences, not firsts: their counted quantity is bits examined by one instrumented subroutine (`bcount`), the reduction from that subroutine to total cost is prose (footnote *12: "The time cost of operations other than bcount is proportional to bcount's at most"), the model is an ad-hoc writer monad rather than a named cost model, the monadification transformation is itself unverified (§3.2.5), and no space bound is proved. None of that makes our bound a first.

### 2.5 Machine-checked asymptotic space bounds in bits already exist (T1)

**Emin Karayel, "A Combinator Library for Prefix-Free Codes", AFP, submitted 8 April 2022**, together with **"Formalization of Randomized Approximation Algorithms for Frequency Moments", AFP, same submission date**, linked publication **Karayel, ITP 2022, LIPIcs 237, 21:1–21:21, DOI 10.4230/LIPIcs.ITP.2022.21**. Receipts: both AFP entry pages and both machine-generated outline PDFs read in full; DOI resolved at drops.dagstuhl.de. Tier **T1**.

Verbatim from the Frequency_Moments outline:

```
theorem f0-exact-space-usage:
  … AE ω in Ω. bit-count (encode-f0-state ω) ≤ f0-space-usage (n, ε, δ)
theorem f0-asymptotic-space-complexity:
  f0-space-usage ∈ O[at-top ×F at-right 0 ×F at-right 0](λ(n, ε, δ). …)
```

Karayel's ITP 2022 abstract describes the combinator library as existing *"for the verification of space complexities."*

**Restriction.** **Retire outright** any wording of the form "first machine-checked asymptotic space bound on an encoded data structure", "first mechanized bit-accounting framework", or "first machine-checked little-o space statement". The AFP has contained a complete bit-accounting → asymptotic-space-complexity pipeline since April 2022. Cite the **pair** plus the ITP 2022 paper, never the combinator library alone.

**This finding, combined with §2.1's `o(n)` sentence, is why the repository-memory framing "our novelty is the machine-checked ASYMPTOTIC o(n)" is retired in §4.2.**

### 2.6 Mechanized charged-query / anti-oracle disciplines predate us (T1)

**Manuel Eberl, "Lower bound on comparison-based sorting algorithms", AFP, submitted 15 March 2017.** Receipts: AFP entry page (twice) and the 10-page outline PDF exposing the Isabelle source; also fetched from the afp-devel GitHub mirror. Tier **T1**.

```isabelle
datatype 'a sorter = Return "'a list" | Query 'a 'a "bool ⇒ 'a sorter"
primrec count_queries :: "('a × 'a) set ⇒ 'a sorter ⇒ nat" where
  "count_queries _ (Return _) = 0"
| "count_queries R (Query a b f) = Suc (count_queries R (f ((a, b) ∈ R)))"
```

Eberl **self-describes this as a mechanization of textbook practice**, citing Cormen–Leiserson–Rivest–Stein, *Introduction to Algorithms*, 2nd ed., 2001: *"Cormen et al. [1] use a similar 'decision tree' model."*

**Restriction.** Claim **nothing** for the technique of reifying an algorithm so that its only chargeable interaction with the outside is an explicit counted event. It is 2017 AFP practice mechanizing 2001 textbook practice, and it is defeated twice over.

**One asymmetry we may state accurately, and must state carefully.** Eberl uses the reified model to prove a **lower** bound by counting, where the datatype *is* the object being universally quantified over — the discipline is definitional and carries no soundness risk. We use a same-shaped model for an **upper** bound, which creates a vacuity hazard with no analogue in Eberl: one must show the exhibited algorithm's free controller is not smuggling in information the charged probes are supposed to pay for, and that the charged trace corresponds to reads from a real bounded store. Those obligations are the actual work, and Eberl incurs none of them. **State this as a scope difference, never as a deficiency in Eberl's work** — a lower bound over an abstract algorithm class has nothing to be adequate *to*.

**Note an internal disagreement:** two independent verifiers adjudicated this same entry and reached opposite `threatens` verdicts (modality B: false; modality D: true). We record the disagreement rather than resolving it in our favour.

### 2.7 Read-charging cost models already exist in Lean 4 (T1)

**Algolean**, six authors (Srinivas, Ermovick, Duve, Hamade, Tantow, Schlesinger), `CITATION.cff` v1.0.0, 2026-03-17, Apache-2.0. Receipts: full recursive git tree; raw `ReadOnlyVec.lean`, `QueryModel.lean`, `ComparisonSort.lean`, `Complexity/Basic.lean`, `AddWriter/Basic.lean`, `CITATION.cff`, `lakefile.toml`. Tier **T1**.

**Restriction.** Retire, in Lean specifically: "first cost model in Lean", "first probe counting in Lean", "first cell-probe-shaped read-charging model in Lean", "first mechanized counting/pigeonhole lower bound in Lean".

**What we may still say, precisely.** Algolean's cost is a **scalar aggregate** (`Prog.time` returns a single `Cost` via `AddWriter.tell`), **not an emitted trace**; the array is carried **inside the query constructor**, so there is no separately threaded physical store and no erasure or store-parametricity theorem; its lower bound is stated over `Prog (SortOps (Fin n))`, a **comparison** model, so **no theorem in Algolean connects its lower-bound layer to its read-charging layer**; `Complexity/Basic.lean` contains **no asymptotic notation at all** (no `IsLittleO`, no `Asymptotics`); and there is no bit-level space accounting anywhere in the tree.

### 2.8 Mechanized cost results in Lean at scale already exist (T1/T2)

**CSLib** (arXiv:2602.04846v1, 4 Feb 2026, eight authors) — but cite it as a **white paper**: *"In this white paper, we introduce CSLib"*, and Figure 4's `mergeSort_time` is marked `-- Proof omitted` in the paper. The proof does exist and is `grind`-closed **in the repository**, so cite the repo for the theorem and the arXiv paper for the position. **complexitylib** (Schlesinger; pin commit `645b5676bdd64c6b7a36f80ab8e763055c7e89d9`). **CLRS-Lean** (Anjie Xu; 30/35 chapters, 1326/1326 selected theorems, no license).

**Restriction.** Retire "first verified algorithms with complexity in Lean" and any implication that Lean lacks cost infrastructure. Our "Mechanized cost analysis" paragraph, which lists only Isabelle and Coq traditions, is a soft target and should acknowledge the Lean-native line (§5.10).

### 2.9 Explicit-constant machine-checked cost bounds already exist (T1)

**Ammer & Lammich, "van Emde Boas Trees", AFP, 2021-11-23.** `T_member t x ≤ (1+height t)*15`; `T_insert … *23`; `T_succ … *27`; `T_pred … *29`; `T_member t x ≤ 30 + 15 * lb (lb u)`; imperative triples `T[5+5*height t]`; build bounds `T_buildup n ≤ 26 * u` and `T_vebt_buildupi n ≤ 10*2^n`; space theorem `space t ≤ 12 * u` in constructor units; refinement into Imperative HOL with Time (framework by **Haslbeck & Zhan**, not by Ammer & Lammich).

**Restriction.** Do not present explicit-constant machine-checked cost accounting as itself novel. Do not credit the trusted-base-shrinking refinement technique to Ammer & Lammich — the manuscript already correctly cites `ZhanHaslbeck18`. Also correct an internal note: VEB space is **linear** in the universe (`≤ 12·u`), **not** superlinear; and it **does** prove preprocessing/build bounds, ground we explicitly leave unproved.

### 2.10 Mechanized encoding-length lower bounds and encoding optimality already exist (T1)

- **Hibon & Paulson, "Source Coding Theorem", AFP, 2016-10-19**, `rate_lower_bound : 𝖧(X) ≤ code_rate enc X`. **Important scope correction to our own internal note:** this bounds the **expectation** of codeword length for a **variable-length** code relative to a **source distribution**. It is not a worst-case bound on the size of a fixed-length encoding. Do not describe it as "a lower bound on encoding size" in the ledger — that would make the ledger itself inaccurate.
- **Blanchette, Huffman, AFP 2008** / **JAR 43(1):1–18, 2009**, and behind it **Laurent Théry's Coq formalization, October 2003 / TR CS 034/2004**. `optimum t = (∀u. consistent u → alphabet t = alphabet u → freq t = freq u → cost t ≤ cost u)`. Note `cost` here is a **false friend**: it denotes weighted path length (encoding length), not query cost.

**Restriction.** Any claim about mechanized information-theoretic or encoding-optimality lower bounds must concede these by name. The defensible residue is narrow (§3.4).

### 2.11 Classical RMQ constraints (T1)

- **Sadakane, JDA 5(1):12–22, 2007** — first non-systematic succinct RMQ, `4n + o(n)`, BP-of-Cartesian-tree + LCA. **Restriction:** we share Sadakane's *setting* and *family*, not his *mechanism* (his `4n` comes from n "fake" leaves to obtain an index↔parenthesis mapping; our BP code is exactly `2n` and recovers the mapping by rank/select over close parentheses). Cite him as the originator of the setting; **do not** write "we formalize Sadakane's architecture".
- **Fischer 2010, p. 3** states the `2n − Θ(log n)` counting bound **explicitly**, with the binomial formula. **Liu 2021** carries the exact `1.5 log n` constant. **Restriction:** "implicit in the classical literature" is unsupportable; and no drift toward presenting the `1.5` constant or the `2n − 1.5 log n − O(1)` form as our sharpening.
- **Munro–Nicholson–Benkner–Wild, ESA 2021** go **below 2n on average**. **Restriction:** "essentially optimal" must carry a worst-case qualifier.
- **Pătrașcu, FOCS 2008** puts the classical redundancy frontier at `n/polylog n`, against our unquantified little-o-linear envelope. **Restriction:** the §10 item-4 disclaimer is load-bearing and should name the actual classical figure.
- **Gál & Miltersen, TCS 379(3):405–417, 2007** originates both the systematic/non-systematic vocabulary we use uncited and the free-computation-between-probes convention.

### 2.12 Adjacent Isabelle work that looks threatening on first contact (T1)

**Cheung & Rizkallah, AFP "Formalised Burrows-Wheeler Transform" (2025)** ships `Rank_Util`, `Select_Util`, `Rank_Select`. A referee opening the artifact will ask. The resolution — plain `count_list (take i s) x` over a list, no bitvector, no directory, no space claim — belongs in the ledger, because the abstract-level assertion "rank/select is absent" is **false of the development** even though it is true of the abstract.

---

## 3. Defensible claims

Each claim below is stated in the weakest form the evidence supports. Every one is conditional on §1's limitations. **None of them is a "first".**

### 3.1 No mechanized RMQ data structure was found

> We are not aware of a prior machine-checked formalization of range minimum query as a data-structure problem, in any proof assistant.

**Why it survives.** Coq: the affeldt-aist lineage's complete recursive git tree contains no path matching `rmq`, `cartesian`, `lca`, `range`, or `min`, and the ITP 2019 bibliography (all 25 entries read) mentions no RMQ, Cartesian-tree or LCA work. Isabelle: 27 AFP full-text queries plus three exhaustive topic enumerations plus the 27-chapter *FDSA* TOC return nothing. Lean: `gh search code` for `rangeMinimum`, `RMQ`, `cartesianTree`, `sparseTable`, `eulerTour`, `lowestCommonAncestor` returns nothing on point; Loogle reports zero Mathlib declarations containing "succinct", and zero containing both "Cartesian" and "tree"; CLRS-Lean returns 0 for `RMQ`, `"range minimum"`, `succinct`, `bitvector`, `"lowest common ancestor"`, with all `Cartesian` and `LCA` hits false positives (Cartesian *product*; `residualCapacity`, `scrollCandidates`).

**What it is conditional on.** Everything in §1.2 limitation 3 (six prover corpora web-searched only), §1.3 limitations 1–4 (GitHub search coverage, the `gh` quoting defect, Zulip, Reservoir), §1.1 limitation 1 (broken forward-citation indexing), and §1.2 limitations 1–2 (AFP sources not grepped). **Phrase it as "we are not aware of", never as "there is no".**

### 3.2 The conjunction was not found anywhere

> We did not find any development, in any proof assistant, that exhibits all three of the following for the same problem in the same artifact: (i) a machine-checked payload-bit bound of the succinct form `2n + o(n)`; (ii) machine-checked exact answers (here, leftmost minimum) for every valid query; and (iii) a machine-checked information-theoretic lower bound on the encoding length of the same problem.

**Why it survives.** Every *individual* ingredient is occupied territory and is conceded above: bit-length accounting (§2.5), asymptotic space in bits (§2.5), charged queries (§2.6), read charging (§2.7), encoding-length lower bounds (§2.10), exact-answer functional correctness (ubiquitous). What we did not find is the conjunction. Karayel has (i)-shaped bit asymptotics with no data structure and no lower bound; Hibon–Paulson has an information-theoretic lower bound with no structure; Eberl has a lower bound on *queries* with no space quantity defined at all (we read all 10 pages: no occurrence of *bit, bits, space, memory, word, cell, probe, encode, decode, succinct, redundancy, store, array*); the Coq succinct line has (ii) and a prose (i) but no lower bound; VEB has cost and a constructor-unit space bound but no bits and no lower bound.

**Weakest honest form.** This is a claim about a *combination in one artifact*, which is a weak kind of novelty. State it as such.

### 3.3 The model-adequacy package was not found

> We did not find, in any proof assistant, a cost model that combines: an emitted event trace in which every charged event is an attempted word read; a physical word list that erases exactly to the public payload; store-parametricity under agreement on the execution's ordered read footprint; and checked mutation witnesses showing the store is genuinely observed.

**Why it survives, and the four concessions it must carry.**
1. **Eberl 2017** already reifies an algorithm so that only counted oracle queries convey information — and credits CLRS. The technique is not ours.
2. **Algolean** already charges indexed reads at unit cost in Lean 4 — but yields a **scalar** `Cost`, not a trace; carries the array inside the query constructor rather than threading a store; and proves no erasure, parametricity, or mutation theorem.
3. **calf** already enforces a *noninterference* discipline (`Calf.Noninterference.oblivious/constant/optimization`: any function from an intensional type to an extensional type is internally equal to a constant function) — a related but distinct discipline, and calf explicitly flags a stronger adequacy theorem "à la Blelloch and Greiner" as future work.
4. **VEB / Haslbeck–Zhan** already discharge hand-written timing functions into Imperative HOL with Time, removing them from the trusted base — a trusted-base-shrinking argument of the same spirit, done in 2018–2021.

So the defensible residue is the **specific four-part package**, particularly the erasure + store-parametricity + mutation-witness triple against a *declared bit-level store*, not the idea of a charged-event model. State it that way or not at all.

### 3.4 A worst-case encoding-length lower bound for a query problem was not found elsewhere

> We did not find a mechanized worst-case lower bound on the encoding length of a data structure for a query problem. The mechanized lower bounds we found are either bounds on query/comparison count (Eberl 2017; Algolean; complexitylib's Shannon circuit bound), or bounds on *expected* codeword length relative to a source distribution (Hibon & Paulson 2016), or weighted-path-length optimality among comparable trees (Blanchette 2008; Théry 2003).

**Why it survives.** Because the three cited families are each a different quantity: comparison count is not bits of state; expected code rate under a distribution is not worst-case fixed-length capacity; weighted path length among *comparable* trees is a per-instance minimality, and Blanchette's own §5.4 states the formalization "says nothing about the algorithm's application for data compression."

**What it must concede.** The bound itself is classical and **explicit** in Fischer 2010 p. 3, and its exact leading terms including the `1.5` are in Liu 2021. What is ours is the mechanization in integer arithmetic without rationals, plus clause (iii) of Theorem `thm:lower` — a concrete `2n`-bit attaining decoder rather than a bare counting existential. That is a mechanization delta, not a mathematical one, and must be labelled as such.

### 3.5 No mechanized cell-probe cost bound was found

> We did not find a mechanized cell-probe cost bound — charging aligned memory probes into a modeled store with computation between probes free — for any data structure, in any proof assistant.

**Why it survives, on three affirmative receipts rather than search silence.** (i) CSLib, the flagship Lean cost paper of Feb 2026, states that formalizing complexity "via explicit RAM and query models" is future work and that its framework cannot prove lower bounds. (ii) `coq-library-complexity`, the most mature mechanized complexity corpus in any assistant, confirmedly contains no cell-probe model, no data-structure query complexity, and no memory-probe accounting (its single file named `Probe.lean` is a TM head-walk routine, explicitly not cell-probe complexity). (iii) The Affeldt/Garrigue/Qi/Tanaka succinct line proves correctness only, with complexity deferred by its own conclusion.

**What it is conditional on.** §1.4 limitations 1 and 2 — the Iris/CFML case-study corpus was never enumerated, and the Zhan–Haslbeck cost model was never characterised. **Either could contain the defeater.** Until an Iris/CFML sweep and a read of the Imperative-HOL-with-Time cost semantics are done, this claim is the most fragile in §3 and should carry that caveat in the manuscript.

### 3.6 The claim we will *not* make about our own bound's shape

> The combination of an explicit uniform constant probe cap with a separately proved allocated-capacity bound of `2n + o(n)` bits over the same representation was not found elsewhere.

Stated only in that conjoined form. **Explicit-constant machine-checked cost bounds are not novel** (VEB's 15/23/27/29/30/26/10/13; JIP 2018's `≤ 64` bits examined). **Allocated-capacity accounting in bits is not novel** (Karayel). Only the pairing, against one packed object, is what we did not find.

### 3.7 Weak but factual

> The development is Mathlib-free Lean 4.

True by construction; a portability/trust-base fact, not a research contribution. Included only so it is not confused for one.

---

## 4. Claims explicitly retired

Each is named and killed. None may be reintroduced without new receipts.

**R1. "First mechanized succinct data structure" (any scope).** Killed by TAG16's abstract and Conclusion. Already frozen; restated. *(T1)*

**R2. "Our novelty is the machine-checked *asymptotic* `o(n)`, rather than succinctness or `2n`."** — the repository-memory framing. **Retired, on two independent grounds.**
(a) Karayel's `Frequency_Moments` machine-checks an asymptotic space bound **in bits, in Landau notation**, and has since April 2022 (§2.5).
(b) The Coq-line counter-argument cannot be closed: although the 2021 artifact's storage results are exact closed-form equalities, contain no asymptotics library, and are package-level incapable of stating `o(n)` (mathcomp-analysis is not in `opam`), **the ICFEM 2016 artifact itself was never inspected** — its URL 404s and the exhibited lemma `rank_spaced1` does not appear in the 2021 repo, so the 2021 repo is a re-done development. It is formally possible the lost 2016 artifact contained an asymptotic statement. Combined with §2.2's "we will do it formally", this is not defensible ground.

**R3. "First machine-checked query-cost bound for a succinct data structure."** Killed by JIP 2018 §6.5.2 (`RankLookupNumBitsExamined`, `RankInitNumBitsExamined`). *(T1)*

**R4. "First machine-checked asymptotic space bound on an encoded data structure" / "first mechanized bit-accounting framework."** Killed by Karayel, AFP 2022 + ITP 2022. *(T1)*

**R5. "First cost model in Lean" / "first probe counting in Lean" / "first cell-probe-shaped read-charging model in Lean."** Killed by Algolean `ReadOnlyVec.natCost`. *(T1)*

**R6. "First mechanized information-theoretic / pigeonhole lower bound in Lean."** Killed by Algolean `cmpSort_lower_bound` and complexitylib `Circuits/Shannon.lean`. *(T1)*

**R7. "First verified algorithms with complexity in Lean."** Killed by CLRS-Lean, CSLib, complexitylib, Algolean. *(T1)*

**R8. Novelty for the technique of reifying an algorithm as a charged-event tree.** Killed twice: Eberl AFP 2017, and Eberl's own attribution to CLRS 2001. *(T1)*

**R9. Novelty for a noninterference / cost-cannot-leak discipline.** Killed by calf POPL 2022, where it is a mechanized theorem family, not a slogan. *(T1)*

**R10. Novelty for explicit-constant machine-checked cost bounds.** Killed by VEB AFP 2021 and JIP 2018. *(T1)*

**R11. Novelty for the Catalan counting infrastructure.** Killed by Mathlib (`treesOfNumNodesEq_card_eq_catalan`, `succ_mul_catalan_eq_centralBinom`, `four_pow_le_two_mul_self_mul_centralBinom`, `DyckWord.card_dyckWord_semilength_eq_catalan`) and by AFP `Catalan Numbers` (Eberl 2016). *(T1)*

**R12. "The counting bound is implicit in the classical literature."** Retired: it is **explicit** in Fischer 2010 p. 3 with the binomial formula, and its exact leading terms including `1.5` are in Liu 2021. *(T1)*

**R13. "`2n + o(n)` is essentially optimal."** Retired unless qualified **worst-case**: Hypersuccinct Trees (ESA 2021) drops below `2n` in expectation, and Hamada et al. (ESA 2024) implement it. *(T1/T2)*

**R14. "We charge only probes, whereas the time-credit tradition charges every step."** Retired as a distinguisher: ESOP 2018 charges only function calls and loop-body entries — "every other operation costs nothing." Restricted charging is also calf's declared framework-level stance. *(T1)*

**R15. "The Coq succinct line proves no complexity results."** Retired: `jacobson_rank_complexity.v` proves storage formulas, and JIP 2018 proves counted query cost. *(T1)*

**R16. "There is no cell-probe / succinct / RMQ mechanization."** Retired as a *form of words* everywhere. Replaced throughout by "we did not find". *(methodological)*

**R17. "End-to-end."** Retired as our weakest word (long-standing internal note; nothing this session rehabilitates it). If the artifact does not run from source text to compiled code with a machine-checked chain, do not say end-to-end.

**R18. "We formalize Sadakane's architecture."** Retired: same setting and family, different mechanism (his `4n` comes from fake leaves; ours is exactly `2n` with rank/select over close parentheses). *(T1/T2)*

**R19. "The single descendant of the Coq succinct line in six years."** Retired before it was written: Semantic Scholar shows four citations of ITP 2019, three of them non-self (BWT CPP 2025; Karayel AFP 2022 frequency moments; Schellhorn et al. VSTTE 2022). A referee with a Semantic Scholar tab open refutes it in thirty seconds. *(T2)*

**R20. Any absence claim about the AFP.** Retired: the AFP search indexes abstracts, not theory sources, and the Burrows-Wheeler entry is a live demonstration that this produces false negatives. *(T1, self-demonstrated)*

---

## 5. Bibliography repairs

Every repair below quotes the current text. Line numbers are at the base commit.

### 5.1 `rmq.tex` — the Tanaka conflation (two locations, HIGH)

**Current, §1.2 (≈ lines 151–153):**
> `Coq/SSReflect succinct-data-structure line of Tanaka, Affeldt, Garrigue,`
> `and Qi~\cite{TAG16,AGQT19}`

**Replace with:**
> `Coq/SSReflect succinct-data-structure line of Akira Tanaka, Affeldt and`
> `Garrigue~\cite{TAG16}, continued by Affeldt and Garrigue with Qi and`
> `Kazunari Tanaka~\cite{AGQT19}`

**Current, §10 "Mechanized succinct data structures" (≈ lines 790–793):**
> `The closest precedent is the Coq/SSReflect line of Tanaka, Affeldt, and`
> `Garrigue, who verified the Jacobson rank algorithm with extraction to`
> `OCaml~\cite{TAG16}, extended with Qi to tree algorithms over LOUDS and`
> `related succinct representations~\cite{AGQT19}.`

**Replace with:**
> `The closest precedent is the Coq/SSReflect line begun by Akira Tanaka,`
> `Affeldt and Garrigue, who verified the Jacobson rank algorithm with`
> `extraction to OCaml~\cite{TAG16} and later machine-checked a counted`
> `bits-examined bound for it~\cite{TAG18}, and continued by Affeldt and`
> `Garrigue with Xuanrui Qi and Kazunari Tanaka, who formalized tree`
> `algorithms over LOUDS and dynamic bit vectors~\cite{AGQT19}. The two`
> `Tanakas are different authors.`

`references.bib` is **correct** on both entries and needs no change here. Use given names for both Tanakas at least once. Do not write "extended with Qi": ITP 2019 **drops** Akira Tanaka and **adds two** authors.

### 5.2 `rmq.tex` — the priority-attribution overreach (HIGH)

**Current (≈ lines 793–795):**
> `Those papers already state`
> `priority for mechanized succinct-structure verification in their setting;`
> `accordingly, this draft claims no such priority.`

**Replace with:**
> `Tanaka, Affeldt and Garrigue state that, to the best of their knowledge,`
> `theirs is ``the first application of formal verification to succinct data`
> `structures''~\cite{TAG16}; Affeldt, Garrigue, Qi and Tanaka similarly`
> `believe their LOUDS and dynamic-bit-vector developments to be the first`
> `formalizations of those representations~\cite{AGQT19}. Accordingly, this`
> `draft claims no priority for mechanized succinct-structure verification.`

Rationale: the plural "those papers … state priority … in their setting" is unsupportable at that scope. TAG16 makes a general (hedged) claim; AGQT19's is scoped to two specific representations and in fact cites the earlier work for rank. Both abstracts are now T1-verified verbatim, so the ledger's "Priority posture" row can be upgraded from repo-doc-only.

### 5.3 `rmq.tex` — Fischer–Heun mislabelled "systematic" (HIGH, referee-visible)

**Current (≈ lines 764–770):**
> `Fischer and`
> `Heun~\cite{FischerHeun11} gave the systematic $2n + o(n)$-bit,`
> `constant-time succinct RMQ preprocessing scheme, and`
> `Fischer~\cite{Fischer10} the non-systematic optimal-succinctness variant`
> `whose model vocabulary the packed cell-probe result of`
> `Section~\ref{sec:pending} follows.`

**Replace with:**
> `Fischer and Heun~\cite{FischerHeun07} gave the systematic`
> `$2n + o(n) + \len{A}$-bit constant-time scheme; the non-systematic`
> `(encoding) $2n + o(n)$-bit constant-time scheme, which answers without`
> `consulting the array, is Fischer and Heun's~\cite[Thm.~5.8,`
> `Cor.~5.9]{FischerHeun11}, with Fischer~\cite{Fischer10} its preliminary`
> `LATIN~2010 version. The earliest non-systematic succinct RMQ is`
> `Sadakane's $4n + o(n)$ balanced-parentheses encoding of the Cartesian`
> `tree with an $o(n)$-bit LCA computation therein~\cite{Sadakane07}, whose`
> `setting --- though not whose mechanism --- the construction of`
> `Section~\ref{sec:architecture} shares.`

**Do not** take the alternative repair of simply relabelling `FischerHeun11` as "the non-systematic scheme": FH11 covers **both** settings (its Thm 3.7 is a genuine systematic constant-time scheme at `|A| + 2n − Θ(n lg lg n / lg n)` bits), so that would introduce a new error. The `RELATED_WORK_LEDGER.md` FischerHeun11 row (lines 25–29) repeats the same error and must be updated with it.

### 5.4 `rmq.tex` — cell-probe convention mis-sourced to Fischer 2010 (MEDIUM–HIGH)

**Current, §9 (≈ lines 703–705):**
> `standard convention in which succinct RMQ upper and lower bounds are`
> `usually read~\cite{Fischer10,LiuYu20}`

**Replace with:** `…usually read~\cite{GalMiltersen07,LiuYu20}`

Rationale: Fischer 2010 §2 declares "the standard word-RAM model of computation, where fundamental arithmetic operations on words consisting of Θ(log n) consecutive bits can be computed in O(1) time" — it **charges** the computation the cell-probe convention makes free, and the string "cell probe" appears exactly once in the document, inside a reference title. Gál & Miltersen is the origin of both the free-computation convention ("we only charge for reading bits in φ(x), not for computation") and the systematic/index vocabulary we use uncited. The same substitution applies to the "model vocabulary" clause repaired in §5.3.

Also acceptable, and arguably better: `rmq.tex` line ≈ 86 currently reads `in a word-RAM or cell-probe model~\cite{FischerHeun11,Fischer10}`. That disjunction is **defensible as written** (both cited papers are word-RAM), but would read more precisely as word-RAM for both, with the cell-probe convention sourced separately.

### 5.5 `rmq.tex` — the Catalan-counting citation (LOW)

**Current (≈ lines 86–88):**
> `the answer function determines the Cartesian tree shape of`
> `the input, of which there are Catalan-many~\cite{Vuillemin80,GBT84}.`

GBT84 introduces the Cartesian tree and the RMQ↔LCA route; the **counting** argument as a space bound is spelled out in Fischer 2010 §1.1. Add `Fischer10` (or `Sadakane07`) alongside. Also add a worst-case qualifier before "essentially optimal" (line ≈ 85) and, optionally, cite Hypersuccinct Trees for the average-case regime.

### 5.6 `rmq.tex` — "implicit" is wrong (MEDIUM)

**Current, §10 Lower bounds (≈ lines 785–787):**
> `The information-theoretic bound mechanized here`
> `(Section~\ref{sec:lower}) is the counting bound implicit in the classical`
> `literature.`

**Replace with:**
> `The information-theoretic bound mechanized here`
> `(Section~\ref{sec:lower}) is the classical counting bound, stated`
> `explicitly by Fischer~\cite[\S1.1]{Fischer10} as`
> `$\log\binom{2n-1}{n-1}/(2n-1) = 2n - \Theta(\log n)$ and sharpened with`
> `its exact leading constants by Liu~\cite{Liu21}; what is new here is its`
> `mechanization in integer arithmetic together with a concrete $2n$-bit`
> `attaining decoder.`

### 5.7 `references.bib` — `ZhanHaslbeck18` title is factually wrong (HIGHEST-SEVERITY BIB ERROR)

**Current (lines 203–204):**
```bibtex
  title     = {Verifying Asymptotic Time Complexity of Imperative Programs in
               {Isabelle/HOL}},
```

**Replace with:**
```bibtex
  title     = {Verifying Asymptotic Time Complexity of Imperative Programs in
               Isabelle},
```

The true title has **no** `/HOL`. Confirmed twice independently: dblp `conf/cade/ZhanH18` (IJCAR 2018, LNCS 10900, pp. 532–548, DOI 10.1007/978-3-319-94205-6_35) and arXiv:1802.01336, whose abstract opens "We present a framework in Isabelle for verifying asymptotic time complexity of imperative programs." This is an **invented title fragment** — exactly the failure the bib header's policy forbids — and its ledger receipt is `repo-doc + background`, i.e. the tier the header never licenses (§5.11). Likely contamination source: the sibling Haslbeck & Lammich, "Refinement with Time — Refining the Run-Time of Algorithms in **Isabelle/HOL**", ITP 2019, which genuinely carries `/HOL`. Fields now addable: `series = {Lecture Notes in Computer Science}`, `volume = {10900}`, `pages = {532--548}`, `publisher = {Springer}`, `doi = {10.1007/978-3-319-94205-6_35}`. The existing `booktitle` ordinal "9th" is **correct**; do not "fix" it.

### 5.8 `references.bib` — `Nipkow16` is a two-page invited-talk abstract (MEDIUM)

Confirmed T1 from the PDF's own title page, which carries the metadata line `Category   Invited Talk`; pages `4:1--4:2`; the body is two sections and an 11-item reference list with **no** theorem, definition, lemma or equation. **Note the receipt carefully:** the DROPS landing page and dblp do **not** show the invited-talk designation (dblp lists it under "Conference and Workshop Papers"; TUM's repository calls it "Conference contribution (peer-reviewed)"). **Cite the PDF, not the landing page**, or a referee checking dblp will find the claim unsupported.

**Add:** `pages = {4:1--4:2}` and `note = {Invited talk; extended abstract. Article 4, DOI 10.4230/LIPIcs.FSCD.2016.4}`.

**Also:** `rmq.tex` (≈ lines 806–807) currently cites `\cite{Nipkow15, Nipkow16}` as "Nipkow's amortized analyses of functional structures". Nipkow16 is an umbrella over **both** the amortized ITP 2015 work and the *non*-amortized ITP 2016 search-tree automation, so "amortized analyses" is loose as applied to it. The substantive citations are ITP 2015 and ITP 2016; Nipkow16's own reference list identifies them:
- `[6]` Nipkow, *Amortized complexity verified*, ITP 2015, LNCS 9236, pp. 310–324 — this independently confirms `Nipkow15`'s volume **and** supplies the pages the ledger omits.
- `[7]` Nipkow, *Automatic functional correctness proofs for functional search trees*, ITP 2016, LNCS — **uncited in our manuscript**; add it if the automation content is wanted.

### 5.9 `references.bib` — TAG16 fields, with a recorded disagreement

Two verifiers reached opposite conclusions this session about whether the ICFEM 2016 LNCS volume clears our field policy:

- **Modality A:** volume **10009** and pages **243–260** are verified, via dblp `conf/icfem/TanakaAG16`, Affeldt's own BibTeX page (`series = "Lecture Notes in Computer Science", volume = 10009, pages = 243--260`), and a search result confirming ICFEM 2016 = LNCS 10009 (ISBN 978-3-319-47845-6, eds. Ogata, Lawford, Liu). Recommends lifting the ledger's "LNCS volume number omitted as unverified" hedge.
- **Modality F:** the volume "10009" was seen **only in a search-result summary**; Springer returned a 303 auth redirect; recommends the field stay omitted.

**We record the disagreement and take the conservative route:** add `pages = {243--260}` (corroborated at dblp and in ITP 2019's reference [24], both T2/T1) and **leave the LNCS volume omitted** pending a single fetch of either the Springer record or Affeldt's BibTeX page by one auditor. This is a five-minute check; it should be done rather than adjudicated.

### 5.10 `references.bib` — missing entries

**Must add (load-bearing):**

| Key | Entry | Tier |
|---|---|---|
| `Sadakane07` | K. Sadakane, "Succinct data structures for flexible text retrieval systems", *J. Discrete Algorithms* 5(1):12–22, 2007, DOI 10.1016/j.jda.2006.03.011 | T2 (paper body never read; check the ISAAC 2002 precursor before asserting 2007 as a priority date) |
| `FischerHeun07` | J. Fischer, V. Heun, "A New Succinct Representation of RMQ-Information and Improvements in the Enhanced Suffix Array", ESCAPE 2007, LNCS 4614, pp. 459–470, DOI 10.1007/978-3-540-74450-4_41 | T1 (abstract) / T2 |
| `GalMiltersen07` | A. Gál, P. B. Miltersen, "The cell probe complexity of succinct data structures", *Theor. Comput. Sci.* 379(3):405–417, 2007, DOI 10.1016/j.tcs.2007.02.047 | T1 (BRICS RS-03-44 preprint read) / T2 |
| `TAG18` | A. Tanaka, R. Affeldt, J. Garrigue, "Safe Low-level Code Generation in Coq Using Monomorphization and Monadification", *J. Inf. Process.* 26:54–72, 2018, DOI 10.2197/ipsjjip.26.54 | T1 |

Note for `Gál`: the surname carries an acute accent (`G\'al`); author order **Gál then Miltersen** (the Aarhus PURE portal reverses it; the paper and dblp do not). Do **not** attribute the term "encoding data structure" to them.

**Should add (defensive — removes soft targets):** `Patrascu08` (Succincter, FOCS 2008, pp. 305–313); `Eberl17` (AFP, Comparison_Sort_Lower_Bound); `Karayel22a` (AFP, Prefix_Free_Code_Combinators) and `Karayel22b` (ITP 2022, LIPIcs 237, 21:1–21:21, DOI 10.4230/LIPIcs.ITP.2022.21); `AmmerLammich21` (AFP, van Emde Boas Trees); `HibonPaulson16` (AFP, Source Coding Theorem); `NSGH22` (calf, *PACMPL* 6 POPL art. 9, DOI 10.1145/3498670); `CSLib26` (arXiv:2602.04846, cs.LO, no venue); `Algolean26` (software artifact, CITATION.cff v1.0.0, 2026-03-17, six authors, repository URL — **no venue may be asserted**; arXiv `all:Algolean` returns 0 results and dblp shows none); `CheungMoffatRizkallah25` (CPP 2025, DOI 10.1145/3703595.3705883, pp. 187–197).

**May add (recency):** `MNBW21` (Hypersuccinct Trees, ESA 2021, DOI 10.4230/LIPIcs.ESA.2021.70); `DRS12` (COCOON 2012); `Golynski09` (SODA 2009 — **pages unverified, omit them**).

### 5.11 `references.bib` — the field-policy header is inaccurate (LOW, systemic)

**Current (lines 2–5):**
> `% Field policy: only fields verified against the source, the repository's`
> `% accepted claim maps, or an explicit web check recorded in`
> `% RELATED_WORK_LEDGER.md are included.`

The header names three tiers; `RELATED_WORK_LEDGER.md` names a **different** three (repo-doc / web / background). So the header names a tier the ledger never uses ("verified against the source": **0 entries**) and the ledger uses a tier the header never licenses ("background"). Measured across all 23 entries at the base commit:

- **background as the sole basis: 13/23 (57%)** — Vuillemin80, GBT84, HarelTarjan84, BFC00, MunroRaman01, Jacobson89, Clark96, RRR02, Nipkow15, GCP18, CP19, MouraUllrich21, AFP.
- **background relied on for at least one field: 17/23 (74%)** — the above plus FischerHeun11, Fischer10, Navarro16, ZhanHaslbeck18.
- **any web check: 6/23 (26%)**. **any repo-doc: 5/23 (22%)**. **both: 1/23**. **verified against the source: 0/23.**

Either reading of "majority" holds. **The one tier the header does not license is the tier that produced the one outright factual error (§5.7).** Repair: rewrite both documents to name four tiers explicitly, with "background: not independently re-verified" stated plainly in `references.bib` itself.

Separately, the header's claim that only verified fields are included is **false as written even where the data is right**: thirteen entries carry precise volume/number/page fields whose sole receipt was background. Every one of them was checked against dblp this session and **all are correct**. The cheapest honest repair is to **upgrade the receipts** using this session's verification rather than delete correct fields. Fields now verified and addable: `TAG16` pp. 243–260; `AGQT19` pp. 5:1–5:19; `Fischer10` pp. 158–169 + DOI 10.1007/978-3-642-12200-2_16; `LiuYu20` pp. 1402–1415 + DOI 10.1145/3357713.3384260; `NavarroSadakane14` art. 16, pp. 16:1–16:39, DOI 10.1145/2601073; `CP19` issue 3, pp. 331–365, DOI 10.1007/S10817-017-9431-7; `GCP18` pp. 533–560 + DOI 10.1007/978-3-319-89884-1_19; `MouraUllrich21` pp. 625–635 + DOI 10.1007/978-3-030-79876-5_37; `Nipkow15` pp. 310–324 + DOI 10.1007/978-3-319-22102-1_21; `Navarro16` ISBN 9781107152380.

### 5.12 Traps a well-meaning future editor must not "fix"

1. **`AGQT19` article number.** The arXiv PDF (1904.02809v2) self-labels "Article No. **28**; pp. 28:1–28:19" with DOI `…ITP.2019.28`, and its running heads read `28:x`. The **authoritative DROPS record**, confirmed by resolving DOI 10.4230/LIPIcs.ITP.2019.5, is **Article 5, pp. 5:1–5:19**. Our bib is **correct**; anyone verifying via the arXiv PDF will be tempted to change it to 28, which would be wrong.
2. **`Nipkow16` and `Eberl17` PDF dates.** The AFP-served PDFs carry build dates of "February 6, 2026". That is the AFP rebuild date, not authorship. Cite 2016 and 2017.
3. **`Clark96` middle initial.** No source seen this session confirms "R." (the thesis scan front matter showed "David Clark"), no dblp record was found, and no UWSpace catalogue record was reached. **Verify or drop the initial.** This is the weakest receipt in the entire bibliography.
4. **BWT spelling split.** AFP entry = "Formalis**ed**", Cheung & Rizkallah (two authors). CPP paper = "Formaliz**ed**", Cheung, **Moffat**, Rizkallah (three authors). Get both right if both are cited.
5. **`Nipkow15` journal version.** Nipkow & **Brinkop**, "Amortized Complexity Verified", *J. Autom. Reason.* 62(3):367–391, DOI 10.1007/s10817-018-9459-3. dblp and Springer present it as **2019** (issue dated March 2019); the DOI infix is `-018-`; Semantic Scholar wrongly returns 2015. Cite 2019 if cited. The journal version is a real extension (it adds pairing heaps — Brinkop's contribution, corroborated by the separate Brinkop & Nipkow AFP `Pairing_Heap` entry, submitted 2016-07-14). The maintained formalization is the AFP entry `Amortized_Complexity` (Nipkow, submitted 2014-07-07), which **predates both papers**.
6. **`Blanchette` Huffman.** If cited, the citable venue is the journal version: "Proof Pearl: Mechanizing the Textbook Proof of Huffman's Algorithm", *J. Autom. Reason.* 43(1):1–18, 2009, DOI 10.1007/s10817-009-9116-y. The AFP **entry** title ("The Textbook Proof of Huffman's Algorithm") differs from the **document** title inside the PDF ("An Isabelle/HOL Formalization of the Textbook Proof of Huffman's Algorithm"). Do not conflate.
7. **`FischerHeun07` must never be cited for a lower bound** (§5.3).
8. **`Algolean` and `CSLib` have no venue.** Cite the artifact and the arXiv preprint respectively; assert no venue for either.
9. **Do not record an arXiv ID for `GCP18`.** Neither dblp nor the author page lists one, and `arXiv:1802.03098` — an ID one might plausibly derive — is an unrelated computer-vision paper.

### 5.13 `rmq.tex` — the AFP paragraph and the ledger's limitation item 1

**Current (≈ lines 818–821):**
> `The Isabelle Archive of Formal Proofs~\cite{AFP} hosts many`
> `verified data-structure analyses; our search of it for succinct`
> `rank/select or RMQ entries is recorded, with its limitations, in the`
> `related-work ledger.`

The manuscript sentence is **correct as written** and needs no change — it points at the ledger rather than asserting a negative. **The ledger, however, must be updated**: limitation item 1 currently describes "one web query", whereas this session ran 27 AFP full-text queries plus three exhaustive topic enumerations plus direct theory-source reads. **Update the description; keep the limitation.** The residual gap is real and must be stated: the AFP search indexes abstracts, not `.thy` sources; the ~5.35M lines of proof text were not grepped; nine of ten Algorithms subtopics and most non-CS topics were not enumerated.

### 5.14 `rmq.tex` — the "Mechanized cost analysis" paragraph is a soft target

**Current (≈ lines 803–809)** lists only Isabelle and Coq traditions (`Nipkow15`, `Nipkow16`, `CP19`, `GCP18`, `ZhanHaslbeck18`). A referee who knows the Lean ecosystem can fault the omission of Lean-native cost work. Add one sentence acknowledging `CSLib26`, `Algolean26`, `complexitylib` and CLRS-Lean. This **strengthens** the existing contrast, because those efforts are squarely in the tradition the paragraph already distinguishes itself from — CLRS-Lean's own docs call full RAM/pseudocode semantics "a future refinement target", and CSLib's own paper concedes its tick annotations are unverified against execution.

The paragraph should also be corrected on one point: it says the cited efforts "tie cost to program steps of an executable or deeply embedded program." That is right for `ZhanHaslbeck18` and `CP19`, but `GCP18` charges only **designated** source constructs, and calf charges only a **chosen operation class** by design. Rewrite to distinguish *what* is charged rather than *how much*.

### 5.15 One item deliberately withheld from the manuscript

An internal reading suggests that `Axiom nat2ulst_length : ∀ z m, (z < expn 2 m)%nat → size (nat2ulst z) = m` in `jacobson_rank_complexity.v` may be inconsistent as stated (instantiating `z := 0` at `m := 1` and `m := 2` would give `1 = 2`). **This was not checked in a kernel and must not appear in the manuscript.** It attacks an unrefereed supplementary file by colleagues, it needs a machine check before it could be asserted responsibly, and our position stands on scope differences without it. Held as an internal note only.

Relatedly, the axiom list in that file must **not** be characterised as a smear: line 69 carries the author comment `(* NB: proofs can be found in logb.v in https://github.com/affeldt-aist/infotheo/ *)` and line 79 `(* NB: proofs can be found in listbit_correct.v in https://github.com/affeldt-aist/seplog/ *)`. The log laws and the encoder are axiomatized **there** to avoid a heavy dependency, not because nobody proved them.

---

## 6. Verification tiers and what a green novelty log establishes

### 6.1 Counts

| Modality | Item-records | Adversarially verified | Flagged threatening by reporter | Retained a threatening verdict |
|---|---|---|---|---|
| A — Coq/Rocq succinct lineage | 7 | 6 | 2 | 1 |
| B — other provers (AFP + six others) | 12 | 6 | 7 | 1 |
| C — Lean ecosystem | 9 | 6 | 4 | 1 |
| D — cost frameworks | 20 | 6 | 3 | 1 |
| E — classical RMQ | 22 | 6 | 6 | 2 |
| F — bibliographic integrity | 23 | 6 | 2 | 0 |
| **Total** | **93** | **36** | **24** | **6** |

By tier (re-tiered from the searchers' binary labels; see §0.2):

- **T4 — background, not re-verified: 3 item-records.** (TAG16 as re-listed in modality B; AGQT19 as re-listed in modality C; the AFP as a venue in modality F.)
- **T3 — search-result only: at least 5 item-records self-flagged as such** (Mével/Jourdan/Pottier ESOP 2019; Atkey ESOP 2010; Carbonneaux/Hoffmann/Reps/Shao CAV 2017; Haslbeck & Lammich ITP 2019; the Golynski SODA 2009 page range). **None of these five may supply a field to `references.bib`.**
- **T1/T2 — the remaining ~85 item-records.** The split between "PDF/source read" and "structured record only" was **not separately audited** and is not reported here as a number, because doing so from the search transcripts would be a guess. Where a specific claim in §2 or §3 rests on a T1 read, the receipt names the document and what was read.

Every item in §2 that imposes a wording restriction is **T1**.

### 6.2 Disagreements recorded rather than resolved

Two adjudications produced conflicting results this session and are left open:

1. **Eberl, `Comparison_Sort_Lower_Bound`** — modality B verified `threatens=false`; modality D verified `threatens=true`. Both read the same source. The disagreement is about how much of a wording restriction the entry imposes, not about the facts. §2.6 states the restriction at the stronger reading.
2. **ICFEM 2016 LNCS volume 10009** — modality A holds it verified; modality F holds it unverified. §5.9 takes the conservative route and flags the check as outstanding.

### 6.3 What a green novelty log does and does not establish

**It establishes:**

- That six independent search modalities, running roughly 200 queries and reading ~40 primary documents and source files, did not surface a prior mechanization of RMQ as a data-structure problem in any proof assistant.
- That a specific set of "first" formulations is **dead**, each killed by a named T1 receipt (§4). The project is materially more constrained after this search than before it: **five** claim families we had been carrying are retired, including two — machine-checked query cost for a succinct structure (§2.4) and machine-checked asymptotic space in bits (§2.5) — that were retired by evidence we went looking for and found against ourselves.
- That the bibliography contains one hard factual error, three manuscript prose defects, four missing load-bearing classical citations, and a stated field policy that does not describe its own practice.

**It does not establish:**

- **That any of the retired claims could not be retired further, or that any surviving claim is a first.** Nothing in §3 is stated as a first. Every claim in §3 is of the form "we did not find".
- **That the corpora we could not reach are empty.** The unswept regions are large and named: the Iris/CFML case-study corpus (§1.4 lim. 1 — the most likely home of a defeater for §3.5); the AFP's ~5.35M lines of theory source (§1.2 lim. 1–2); six non-Isabelle prover corpora that were web-searched only (§1.2 lim. 3); Reservoir and Lean Zulip (§1.3 lim. 3–4); the Coq/Rocq opam index and `affeldt-aist/infotheo` and `seplog` (§1.1 lim. 5); ITP/CPP/JAR/JFP/POPL/ICFP/ESOP tables of contents (all modalities); non-English venues (§1.1 lim. 4, §1.2 lim. 7).
- **That the forward-citation picture is trustworthy.** OpenAlex and Semantic Scholar disagree with each other by a factor of four on the same paper, and both report implausibly low counts. Google Scholar was unreachable. A citing paper that mechanizes exactly what we claim not to have found could exist and be invisible to every query run.
- **That the artifacts we read are correct.** No repository was built. No Lean, Coq or Isabelle proof was kernel-checked by us. No claimed theorem was confirmed `sorry`-free or `Admitted`-free by us. Where we report what a file contains, we report what its text says.
- **That the negative results will stay true.** CSLib's roadmap targets an undergraduate algorithms syllabus by end of 2026 and complexity theory in 2027; Algolean's most recent commit at check time was 3 August 2026; CLRS-Lean is six weeks old and pushed daily. Every Lean negative in this log is **dated, not permanent**, and should be re-run before submission.

**The correct posture for the manuscript remains conditional.** This log converts "the search log is not yet complete" into "the search log is complete to the boundary stated in §1, and here is that boundary". It does not convert any claim into a priority claim, and no future tightening of novelty wording is licensed without extending this log first, with receipts.