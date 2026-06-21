# The o(n) Overhead Wall — Worktree Audit + Research-Backed Plan (2026-06-20)

A deep, worktree-aware audit of the succinct-RMQ effort, a precise diagnosis of
the wall, and a research-grounded plan to get past it. Companion to
`docs/AUDIT_AND_A_DESIGN.md` (round log), `docs/SUCCINCT_FINAL_PATH.md` (worker
spec), and `docs/SUCCINCT_RESEARCH_AND_PLAN.md` (prior research pass).

## 1. Where the work actually is (worktrees)

- **Coordinator** `codex/rmq-small-extraction` (main checkout): merged,
  gate-green floor. Owns names/merge/verification.
- **Worker A** `codex/rmq-c2-bp-close-answer` (9 ahead, dirty): the BP close/LCA
  core in `SuccinctCloseProposal.lean`.
- **Worker "B"** `codex/rmq-c1-descriptor-select-global` (8 ahead, **+4016 dirty
  lines**): *despite* the intended "rank/select parameter arithmetic" role, it is
  actually building a **dense descriptor select** (`twoWordDescriptorSample`,
  `denseTwoWordRoute*`, `payloadWordCountDescriptorTable`).
- 8 other worktrees are spent/merged blocker branches. The
  `codex/rmq-final-succinct-join` branch is not ahead of coord (no live join).

**The single most important organizational fact: neither active worker is
attacking the actual gap (the close-directory o(n) overhead).** A is on
exactness; "B" is on a select variant that is *already done* in the coordinator
(see §4).

## 2. The floor (merged, proven, trust-clean)

`2n`-bit BP encoding (lossless); two-level **rank** and **select** each concrete,
exact, O(1), and **o(n)** (`canonicalTwoLevelSelectOverhead_littleO`, etc.);
the `2n − O(log n)` Catalan lower bound; a useful catalog of negative theorems
pruning bad designs.

## 3. The wall, diagnosed precisely

Worker A has built an extensive close architecture: BP-excess machinery
(`bpBlockMinExcess`/`MaxExcess`/`bpBlockArgMinPrefixPos`), rmM-style summary
tables (`concreteBPRangeMinMaxSummaryTable`), several witness-macro variants
(range / block-pair / prefix-range / endpoint-fringe), candidate merging, and a
Four-Russians-style `BlockMicroCodebook`. Two halves are genuinely solved:

- **Exact**: layered `lcaCloseCosted_exact … = scanWindow …` across all geometric
  cases (the +700 dirty lines finish the cross-block/spanning/fringe cases),
  correctly respecting the `blockPairMacroDirectory_not_sufficient` blocker via
  fringe repair.
- **O(1)**: every read is a true constant (`…cost_le_one/_two/_three`, top
  `cost ≤ 6`), independent of block size.

**The o(n) overhead is the wall, and it is not merely "unproven" — the headline
construction is non-instantiable.** The one theorem that *looks* like a complete
succinct directory,

```
concreteGuardedBPEndpointFringeMacroMicroBPCloseLCADirectory_sampled_profile
  : LittleOLinear (microOverhead + sampledDirectoryOverhead slots)
    ∧ payload.length ≤ … ∧ cost ≤ 6 ∧ erase = some answerClose
```

is an **abstract conditional with mutually unsatisfiable premises**:

- `interiorBlockPairRanges blockCount = (List.range (blockCount*blockCount)).map …`
  — i.e. **blockCount² (dense, all block-pairs)**. So `hmacroBudget`
  (those ranges fit in the o(n) `sampledDirectoryOverhead`) forces
  `blockCount² · fieldWidth = o(n)` ⟹ blockSize = ω(√(n log n)) — **large blocks**.
- `hmicroLittle : LittleOLinear microOverhead` with the codebook
  `payload.length = codeCount · tableOverhead` forces codeCount = 2^blockSize to
  be polynomial ⟹ blockSize = O(log n) — **small blocks**.

No block size is both ω(√(n log n)) and O(log n). The theorem is therefore
**vacuous** (anti-pattern: *abstract-no-witness*, fidelity criterion 4 of
`CODEX_AUTONOMY.md`), and it is the same dense family the project already
disproved (`denseAllCloseBPCloseLCAOverhead_not_littleO`,
`blockPairMacroDirectory_not_sufficient`) — reincarnated inside the "sampled"
wrapper. The coordinator must **not** accept it as closing the target.

### The deeper structural cause

Every close summary stores a **`fieldWidth`-bit (Θ(log n)) absolute value per
block/range**. Even *one* absolute Θ(log n)-bit value per Θ(log n)-sized block is
already Θ(n) bits — never o(n) — *before* the dense all-pairs blowup. The effort
is in the wrong family entirely: **precompute-the-answers with absolute-width
entries**, rather than **navigate compact relative summaries + universal tables**.

## 4. The fix the project already knows: reuse the rank/select o(n) technique

The decisive observation: **rank and select already achieve o(n) in this very
repo**, and they do it with the exact technique the close directory is missing.
Two-level rank stores

- superblock cumulative ranks, *absolute* but sampled every Θ(log²n) bits
  ⟹ (n/log²n)·O(log n) = o(n); plus
- block ranks **relative** to the superblock, in O(log log n) bits, every
  Θ(log n) bits ⟹ (n/log n)·O(log log n) = o(n); plus
- in-word `popcount`/`select` primitive — O(1), **stores nothing**.

(`canonicalBlockRankEntries` already stores *relative* deltas — this machinery
exists.) The close/RMQ directory must mirror this:

1. **Universal table for small (≤ ½ log n) blocks** — the in-block min-excess /
   argmin answer for every possible block pattern. #patterns = 2^{½log n}=O(√n),
   table size O(√n·polylog)=o(n), lookup O(1). This is the role `BlockMicroCodebook`
   should play; size it at blockSize = ½ log n and **prove its o(n)**. RMQ needs
   this because, unlike rank, there is no free single-word "argmin" primitive
   (popcount has no min-analogue in a standard word-RAM).
2. **Relative + sampled excess summaries**, *not* per-range answers: block
   min-excess stored **relative** to a sampled superblock reference, in
   O(log log n) bits — exactly like the rank blocks — giving o(n). Reuse the
   two-level rank parameter machinery (`sampledDirectoryOverhead`, the relative
   block-entry codec).
3. **Navigate** (combine superblock + block + in-block via the universal table)
   to answer inter-block RMQ in O(1) — instead of storing an answer per block
   pair. This is the rmM forward/backward search specialized to the ±1 excess.

Net overhead: o(n) (universal table) + o(n) (relative summaries) = o(n), with
O(1) query. **Drop** the `interiorBlockPairRanges` (blockCount²) macro and the
range/prefix-range witness variants — they are the wrong family.

## 5. Research backing (what the literature does, with citations)

The wall is the classic *succinct* (bits, not words) RMQ problem; its resolution
is well established. Key facts that pin the design:

- **2n+o(n) bits, O(1) query is exactly the Fischer–Heun result** and the o(n)
  comes from block decomposition + **universal lookup tables** for small blocks,
  not stored answers [Fischer–Heun 2011; earlier Fischer–Heun 2007]. The 2n is
  asymptotically **optimal** in the encoding model [Fischer 2010, *Optimal
  Succinctness for RMQ*].
- **The range min-max tree** is the canonical O(1)-navigation structure: each
  node stores total/min/max excess; *small blocks are handled by direct table
  lookups, larger ranges by sampled representatives* — explicitly the
  universal-table + sampled-summary split, in 2n+o(n) bits [Navarro–Sadakane
  2014]. A deliberately **simplified** version, the best formalization target,
  is [Cordova–Navarro 2016, *Simple and Efficient Fully-Functional Succinct
  Trees*, arXiv:1601.06939].
- **±1-RMQ + the Four-Russians universal block table** is the in-block O(1)
  device [Bender–Farach-Colton 2000] — note BFC is O(n) *words*; Fischer–Heun is
  the succinct *bits* refinement. The project already has the precedent
  (`Cartesian.Microtable` over `signatureUniverse` in the FH layer).
- **Relative/compact encoding of directory entries** (O(log log n)-bit blocks
  over absolute superblocks) is the standard rank/select o(n) device
  [Jacobson 1989; Clark 1996; Vigna 2008; Navarro 2016, *Compact Data
  Structures*]. This is the exact technique the repo's two-level rank/select
  already use and the close directory does not.
- Pairing the construction with a formalized lower bound remains a genuine
  differentiator; the relevant succinct-RMQ lower bound is [Liu–Yu 2020, *Lower
  Bound for Succinct Range Minimum Query*, arXiv:2004.05738], complementary to
  the repo's own Catalan bound.

### On the "add a word-level min-excess primitive" alternative

A tempting shortcut is to declare an O(1) word-level argmin/min-excess RAM
primitive (mirroring `rankBoolWordPrefix`/`selectBoolWord`) so the in-block step
needs no table. It is *defensible* in an abstract word-RAM, but it **expands the
trusted cost-model base** (popcount is a real ISA op; packed-argmin is not
standard, only broadword-derivable [Vigna 2008]). **Prefer the universal table**:
it is literature-canonical, already precedented in-repo, and adds *no* new
trusted primitive. Reserve the word primitive as a fallback only if the table's
o(n) proof proves intractable, and then instantiate it explicitly.

## 6. Recommended plan & worker realignment

The gap is no longer "build components" — it is **the close-directory o(n)
overhead via the rank/select technique**, then the join. Concretely:

1. **Pin contracts first (coordinator).** Fix the close directory's
   `closeOverhead n` expression and parameter regime (blockSize = ½ log n;
   superblock sampling; relative block-excess width = O(log log n)) and the final
   close-profile signature, plus `sorry`-stubbed component lemmas. This is the
   parallelism unlock (CODEX_AUTONOMY proof-worker protocol step 1).
2. **Re-task the second worker to the *actual* Worker-B role.** Retire the dense
   descriptor-select work — select is already o(n)+exact in the coordinator
   (TwoLevel); the +4016-line descriptor path is redundant and fighting the same
   wall. Point it at the **o(n) overhead arithmetic for the close directory**:
   prove `BlockMicroCodebook` overhead is o(n) at blockSize = ½ log n, and the
   relative-summary overhead is o(n) (reusing `sampledDirectoryOverhead` +
   `LittleOLinear.add`), then the `sum of overheads is o(n)` join glue.
3. **Keep Worker A on the close core**, but pivot from *precompute-the-answers*
   (range/block-pair/prefix-range witnesses) to **navigate compact summaries**:
   relative block-excess + universal-table in-block, combined by an O(1)
   forward/backward search. Finish exactness against this structure.
4. **Activate the join** (coordinator-owned): assemble `bpCode` (2n) + rank +
   select + the new o(n) close into one concrete `def : …Family`, and prove the
   final bundled theorem retaining `logSlackLower n ≤ 2n + overhead`.
5. **Do not widen for throughput.** The bottleneck is the chain
   (universal-table/relative-summary → close o(n) → join), not a fan-out; extra
   parallel builders would reproduce the "not little-o" negatives. Carve out only
   the universal-table o(n) lemma as an independent leaf.

### First theorem to target (kills the mirage, proves the real thing)

A *concrete, instantiated* close-directory profile with **no budget
hypotheses** — block size fixed to ½ log n, summaries relative — of shape:

```lean
theorem concreteRelativeRmmBPCloseLCADirectory_profile (n : Nat) :
  LittleOLinear closeOverhead ∧
  (∀ shape (h : shape ∈ shapesOfSize n),
     (directory n shape h).payload.length = closeOverhead n) ∧
  (∀ …, (directory …).lcaCloseCosted l r |>.cost ≤ K) ∧
  (∀ …, (directory …).lcaCloseCosted … |>.erase = some answerClose)
```

If that typechecks `sorry`-free for a concrete `directory` and a concrete
`closeOverhead` with `LittleOLinear closeOverhead` *unconditionally*, the wall is
broken and only the join remains.

## References

- M. A. Bender, M. Farach-Colton. *The LCA Problem Revisited.* LATIN 2000.
- J. Fischer, V. Heun. *A New Succinct Representation of RMQ-Information and
  Improvements in the Enhanced Suffix Array.* ESCAPE 2007.
- J. Fischer. *Optimal Succinctness for Range Minimum Queries.* LATIN 2010.
  arXiv:0812.2775.
- J. Fischer, V. Heun. *Space-Efficient Preprocessing Schemes for Range Minimum
  Queries on Static Arrays.* SIAM J. Comput. 40(2):465–492, 2011.
- G. Navarro, K. Sadakane. *Fully Functional Static and Dynamic Succinct Trees.*
  ACM Trans. Algorithms 10(3), 2014. arXiv:0905.0768.
- J. Cordova, G. Navarro. *Simple and Efficient Fully-Functional Succinct Trees.*
  2016. arXiv:1601.06939.
- H. Liu, H. Yu. *Lower Bound for Succinct Range Minimum Query.* STOC/arXiv 2020.
  arXiv:2004.05738.
- G. Jacobson. *Space-efficient Static Trees and Graphs.* FOCS 1989.
- D. Clark. *Compact Pat Trees.* PhD thesis, Waterloo, 1996.
- S. Vigna. *Broadword Implementation of Rank/Select Queries.* WEA 2008.
- G. Navarro. *Compact Data Structures: A Practical Approach.* Cambridge, 2016.
- R. Affeldt, J. Garrigue, K. Tanaka. *Proving Tree Algorithms for Succinct Data
  Structures.* ITP 2019. arXiv:1904.02809.
