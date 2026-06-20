# Succinct RMQ: Audit, Research, and Capstone Plan (2026-06-20)

Audit of the latest round + a research-backed plan, with citations, for closing
the genuine `2n + o(n)`-bit, `O(1)`-query BP-native succinct RMQ theorem.
Companion to the worker-visible spec `docs/SUCCINCT_FINAL_PATH.md` and the round
log `docs/AUDIT_AND_A_DESIGN.md`.

## 1. Audit of the latest round

**State.** Build green; trust clean (0 non-standard axioms across the full
curated `scripts/axiom_check.lean`). The Lean source is unchanged from the prior
audit (two-level rank + two-level select genuinely landed: concrete canonical
constructors, `wordSize ≤ machineWordBits = log₂ n + 1`, derived `cost_le_four`,
o(n) overhead, exact). The new commit is `docs/SUCCINCT_FINAL_PATH.md` (+ 3
`axiom_check` entries for new select forcing-lemmas).

**Verdict: this was a real round, not filler.** Instead of another abstract
wrapper, the loop did two valuable things:

1. **Proved design-constraining *negative* theorems** that prune the cheap-but-
   wrong shortcuts to the capstone:
   - `SuccinctCloseProposal.blockPairMacroDirectory_not_sufficient` — a macro
     keyed only by the endpoint close-block pair is *not exact* (concrete
     counterexample: 4-node right spine, `blockSize = 3`).
   - `SuccinctCloseProposal.denseAllCloseBPCloseLCAOverhead_not_littleO` — the
     dense all-close endpoint fallback is exact and charged but its payload is
     *not* `o(n)`.
   - `SuccinctSelectProposal.…shared_aligned_read_word_forces_same_wordIndex`
     and `…shared_local_locator_forces_same_selected_wordIndex` /
     `…contradicts_distinct_selected_wordIndex` — a select locator that reads one
     *aligned* payload word can only serve occurrences whose selected bit lies in
     that one chunk, so the "one-entry/one-aligned-word" select shortcut cannot
     be exact across chunks.
2. **Wrote a precise capstone spec** (`SUCCINCT_FINAL_PATH.md`) pinning the final
   theorem shape and three concrete components, with explicit invalid/valid stop
   points.

These negatives are load-bearing: they are exactly the anti-vacuity guards that
stop a future worker from "closing" the capstone with an insufficient or
non-`o(n)` construction. This matches the recommendation from the prior audit
(freeze components; build toward a concrete witness).

**Stop-appropriateness: appropriate.** The loop hit a genuine design fork (the
select locator), proved the minimal blocker, documented it, and stopped — a
"valid stop point" by the project's own rules. One caveat for *next* round: this
was a characterize-and-spec round with no new positive capstone progress. That is
legitimate **once**. The next round must land a concrete *component builder*
(Component 1 or 2 below), not more specs or more negatives — otherwise the
component-deepening anti-pattern reasserts itself.

## 2. Where the frontier sits

The remaining distance is the **capstone assembly**. `SUCCINCT_FINAL_PATH.md`
decomposes it correctly into three parts:

- **C1 — descriptor-based select** (replace the disproven one-aligned-word
  locator with a charged word-choosing descriptor);
- **C2 — concrete macro/micro BP close-LCA** (replace the abstract `macroCosted`
  with a real BP-excess/RMQ macro + charged endpoint-fringe micro repair,
  avoiding both the disproven endpoint-pair key and the non-`o(n)` dense table);
- **C3 — final join** binding `bpCode` (2n bits) + payload-live rank + C1 + C2
  into one concrete family whose profile proves `LittleOLinear overhead`,
  `payload.length = 2n + overhead`, `cost ≤ queryCost`, and
  `erase = scanWindow` — with the lower-bound tie
  `logSlackLower n ≤ 2n + overhead n`.

Each is well-defined; none needs new mathematics. The risk is purely execution
discipline (keep them concrete and payload-live).

## 3. Research: the canonical structures, mapped to each component

The good news from the literature: **every component has a textbook-canonical
construction.** The project does not need to invent anything; it needs to
formalize known designs. Mapping:

### C1 — select: two-level sampling with a word-choosing descriptor

The disproven shortcut is fixed by the standard constant-time `select`: a coarse
sample of every `k`-th one-bit (the "locator"/descriptor), then a per-block
descriptor that resolves down to the word containing the `i`-th one, then a
single in-word select. This is exactly the
`coarse locator → local descriptor → word-choice → wordSelect` query shape the
spec asks for.

- Jacobson established `o(n)`-bit constant-time rank/select [Jacobson 1989].
- Clark gave the first clean constant-time `select` directory [Clark 1996].
- Vigna's `rank9`/`select9` is the cleanest *implementable* version — two-level
  sampling with the per-block descriptor that locates the target word using only
  aligned reads; this is the precise blueprint for the charged descriptor
  [Vigna 2008]. The `o(n)` overhead is the sampling metadata (one sample per
  `k = Θ(log n)` ones).

### C2 — macro: the range min-max tree over the BP excess

This is the single most useful pointer. RMQ on the original array = LCA in the
Cartesian tree = an RMQ on the **excess sequence** of the balanced-parentheses
(BP) encoding between the two endpoints. The canonical succinct structure for
exactly this is the **range min-max tree (rmM-tree)** of Navarro & Sadakane: a
tree of per-block `min`/`max`-excess summaries, with all BP navigation
operations (`findclose`, `enclose`, and crucially **RMQ/LCA**) reduced to a
handful of constant-time primitives on polylog-sized blocks, in `2n + o(n)` bits
[Navarro–Sadakane 2014]. This *is* "a real BP-excess/RMQ macro over block
summaries whose answer is repaired by charged local micro queries" — the spec's
own description. Recommendation: **make C2's macro a static rmM-tree** (block
min-excess summaries + a sampled/sparse table over them); this directly dodges
both disproven designs (it is endpoint-*offset* sensitive, and the summaries are
`o(n)`).

### C2 — micro: ±1-RMQ Four-Russians table (you already have the pattern)

The in-block "endpoint-fringe repair" is the classic ±1-RMQ micro table: blocks
of `½·log n`, a precomputed table over all *normalized* block patterns (only
`O(√n)` distinct patterns ⇒ `o(n)` table, `O(1)` lookup) [Bender–Farach-Colton
2000]. **You already have a concrete precedent in-repo**: the Fischer–Heun layer's
`Cartesian.Microtable` over `signatureUniverse`/`shapeUniverse`, with
`signatureUniverse_length` already proven `o(n)`-budgeted and sound/complete
lookups. Reuse that concrete pattern for the micro codebook rather than
discharging the abstract obligation from scratch — that converts the "concrete
codebook" task into instantiating an object you have already built once.

### C3 — final scheme: Fischer–Heun is the target; keep the lower-bound tie

The headline theorem (`2n + o(n)` bits, `O(1)` query, array available only at
construction) is exactly the Fischer–Heun result [Fischer–Heun 2011]. Their own
construction (the 2d-Min-Heap BP/DFUDS encoding + ±1-RMQ) is the alternative if
the rmM-tree route stalls. Keep the lower-bound tie `logSlackLower n ≤ 2n +
overhead` in the final statement: pairing the `2n + o(n)` *upper* construction
with the formalized `2n − O(log n)` *lower* bound in one development is a genuine
differentiator (see §4).

### Formalization-design prior art

Affeldt, Garrigue & Tanaka formalized rank/select and LOUDS trees in
Coq/SSReflect, including the two-level directory and constant-time arguments
[Affeldt et al. 2019; `affeldt-aist/succinct`]. Their `rank_select.v` /
`louds.v` show how to structure the level decomposition and the storage/space
accounting cleanly in a proof assistant — worth mirroring for C1/C2. Navarro's
textbook is the consolidated reference for all of the above [Navarro 2016].

## 4. The gap this fills (positioning)

Cross-checking the formalization landscape confirms the gap is real and
specific:

- **No proof assistant has a succinct RMQ/LCA-via-BP-excess with a cost model.**
  Affeldt et al. (Coq) cover rank/select + LOUDS, *not* RMQ/LCA via the excess
  sequence, and *not* with a derived machine-step cost.
- **No formalized RMQ lower bound exists anywhere**; this project already has the
  `2n − O(log n)` Catalan-counting lower bound.
- **CSLib (Lean)** has neither succinct structures nor lower bounds.

So a Lean `2n + o(n)` / `O(1)` succinct RMQ that (a) is payload-live (the query
reads the counted bits), (b) uses a *derived* Θ(log n)-machine-word cost model,
and (c) ships with a matching formalized lower bound, would be novel across all
proof assistants — not merely a Lean port of known Coq work.

## 5. Recommended next moves (in order)

1. **C1 first** — it is the most contained and the blockers are sharpest. Build
   `descriptorSelectDataOfChunks` modeled on Vigna `select9` two-level sampling;
   prove `selectCosted_exact`, `cost ≤ const`, `auxPayload.length ≤
   o(n)-overhead`, and the `word_choice_exact` descriptor lemma. One concrete
   builder, payload-live, slightly loose constant OK.
2. **C2 macro as a static rmM-tree** — block min-excess summaries + sampled table;
   reuse `Cartesian.Microtable` for the micro endpoint repair. Prove the
   `ConcreteMacroBPCloseLCADirectory` fields against the real construction.
3. **C3 join** — assemble and prove `…two_n_plus_o_concrete_query_profile`,
   retaining the `logSlackLower` lower-bound conjunct. Retire any superseded
   abstract families in the *same* round.

A real witness with a loose constant beats another profile layer; the literature
guarantees the constants can be tightened later without changing the theorem
shape.

## References

- M. J. Jacobson. *Space-efficient static trees and graphs.* FOCS 1989.
- D. Clark. *Compact Pat Trees.* PhD thesis, Univ. of Waterloo, 1996.
- M. A. Bender and M. Farach-Colton. *The LCA Problem Revisited.* LATIN 2000.
  https://www.dcc.fc.up.pt/~pribeiro/aulas/taa1920/lca_rmq.pdf
- S. Vigna. *Broadword Implementation of Rank/Select Queries.* WEA 2008.
  https://vigna.di.unimi.it/ftp/papers/Broadword.pdf
- J. Fischer and V. Heun. *Space-Efficient Preprocessing Schemes for Range
  Minimum Queries on Static Arrays.* SIAM J. Comput. 40(2):465–492, 2011.
  https://www.semanticscholar.org/paper/d093047cb47f7f48ff633ac0ad61e3ca3564a9be
- G. Navarro and K. Sadakane. *Fully Functional Static and Dynamic Succinct
  Trees.* ACM Trans. Algorithms 10(3), 2014. https://arxiv.org/abs/0905.0768
  (the range min-max tree; 2n+o(n) bits, O(1) tree ops incl. RMQ/LCA).
- R. Affeldt, J. Garrigue, K. Tanaka. *Proving Tree Algorithms for Succinct Data
  Structures.* ITP 2019, LIPIcs 141. https://arxiv.org/abs/1904.02809 ;
  code: https://github.com/affeldt-aist/succinct
- G. Navarro. *Compact Data Structures: A Practical Approach.* Cambridge Univ.
  Press, 2016.
