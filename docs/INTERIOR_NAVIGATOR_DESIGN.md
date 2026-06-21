# Interior O(1) Range-Min Navigator — Integrated Design Note (2026-06-21)

Worker-facing design for `concreteBPRelativeRmmInteriorDirectory_profile`: the
last open object on the close side. Integrates the coordinator's construction
with the audit's reuse/decoupling refinements; both converged on the same design.
Companion to `docs/SUCCINCT_OVERHEAD_WALL_AND_PLAN.md` and the round log.

## The key insight (agreed)

Do **not** build a full Navarro–Sadakane rmM tree (logarithmic query unless you
add heavy constant-time machinery) and do **not** build a navigator over the
block minima directly (its sparse table is Θ(n log n) bits — the wall). Instead:

**A tiny Fischer–Heun-style two-level sparse table over the already-shrunk
block-minimum sequence (m = n/log n), where the sparse table lives at a coarse
enough granularity that its unavoidable Θ(k log k) cost is o(n) — storing only
indices/offsets, with every value comparison routed through B's existing O(1)
relative-summary point-access.**

This is o(n) by counting, O(1) by reuse, and payload-live by the index/value
decoupling — which is exactly what defeats the `proof_only_oracle` obstruction
the loop just documented (the answer flows through real reads of two payloads, so
no constant-charging oracle can satisfy it).

## The construction

Interior problem: given `startBlock`, `count`, return the **leftmost** block
index whose block-minimum excess is minimal over `[startBlock, startBlock+count)`.
Each candidate's true `(minExcess, argMinPrefixPos)` is recovered by one charged
relative-summary read (`summaryCosted`, cost ≤ 2, already proven exact + o(n)).

1. Split the m = n/log n block-minima into **macroblocks of ≈ log²n blocks**
   (⇒ n/log³n macroblocks).
2. **Local sparse table per macroblock**, entries = **local offsets** (O(log log n)
   bits). Space: (n/log³n)·(log²n · log log n)·(log log n) = **n·(log log n)²/log n
   = o(n)**.
3. **Global sparse table over macroblock minima**, entries = global indices
   (O(log n) bits). Space: (n/log³n)·log n·log n = **n/log n = o(n)**.
4. **Query = ≤ 3 candidates**: left-macroblock suffix (local table), right-macroblock
   prefix (local table), middle full-macroblock range (global table).
5. **Merge** the ≤ 3 candidates by `(minExcess, leftmost block index)`, recovering
   each candidate's excess via one `summaryCosted` read.

Constant number of charged reads ⇒ O(1). Avoids both documented traps: no scan
over all interior blocks; no proof-only oracle.

## Integration refinements (from the audit)

### R1 — Reuse the verified sparse-table algebra; don't reinvent it

The project already has a **verified O(1), exact** sparse table:
`RMQ.SparseTable.Instrumented` (`query_refines_and_steps_le_seven`,
`memoBuild_and_query_refine_with_steps`). Crucially it is **already index/value
decoupled**: it stores argmin **indices** (`Option Nat`) and compares through an
external value accessor (`betterIndexArray (xs : Array Int)`). So:

- **Global macroblock table:** reuse it nearly verbatim — it stores global indices
  (O(log n) bits), which is o(n) at the coarse macroblock granularity.
- **Local macroblock tables:** reuse the same build/query/combine algebra and its
  correctness lemma, but **re-encode the stored payload as local offsets**
  (O(log log n) bits) — Instrumented's `Option Nat` (global, O(log n)-bit) storage
  is too wide at the fine granularity (n·log log n = ω(n)).
- **Comparator:** in both, the value accessor is B's relative-summary point-access
  (build-time may compute block-minima directly; the *stored* payload is only
  indices/offsets).

Net: the hard O(1)+exactness *algebra* is already proven; the genuinely new work
shrinks to the payload-live offset encoding (A) + the o(n) counting (B).

### R2 — The decoupling is the principle (o(n) AND payload-live)

Store offsets/indices; never store excess values in the tables; recover values via
point-access only at merge. This is simultaneously:
- **why it is o(n):** local entries are O(log log n)-bit offsets, not O(log n)-bit
  values (storing values in the local tables would be ω(n));
- **why it is payload-live and oracle-proof:** the answer is read from the sparse
  table's index/offset payload *and* the summary's value payload, so the
  `payloadLiveBPRelativeRmmInteriorDirectory_profile_allows_proof_only_oracle`
  obstruction cannot apply to this concrete construction.

### R3 — Leftmost tie-break at every level, not just the final merge

Each sparse table's stored argmin must be the **leftmost** minimizer of its span
(in `betterIndexArray`, tie → keep the smaller index), and the power-of-two
combine must preserve leftmost — otherwise the `(minExcess, leftmost index)` merge
in step 5 can return a non-leftmost answer and miss `scanWindow` semantics.

### R4 — Honest overhead terms

Add one new term `logLogSquaredSampledDirectoryOverhead` (the local tables;
≈ n·(log log n)²/log n) alongside the existing `logLogSampledDirectoryOverhead`
(relative summary) and `sampledDirectoryOverhead` (global table / super baselines).
Each is `LittleOLinear`; sum via `LittleOLinear.add`. The pattern already exists
in `SuccinctSpace`/`SuccinctCloseProposal` for the other two terms.

### R5 — Minor correction to the alternatives analysis

The Cartesian-shape RMQ over block minima is ruled out primarily by **table size**:
a universal table at log²n-blocks-per-macroblock has Catalan(log²n) ≈ 2^Θ(log²n)
shapes — super-polynomial, not o(n). (Shrinking to ½ log n blocks per macroblock
makes the shape table fit but pushes the *global* table back to Θ(n).) This is even
more decisive than the circularity worry; the conclusion — use local sparse tables,
not a shape table — is unchanged.

## Target signature and worker split

Pin `concreteBPRelativeRmmInteriorDirectory_profile` and prove it by
**composition**, not as a fresh structure:

```
(shape) :
  LittleOLinear interiorOverhead ∧
  payload.length ≤ interiorOverhead shape.size ∧            -- B: counting
  (∀ startBlock count, (queryCosted startBlock count).cost ≤ K) ∧   -- reuse Instrumented
  (∀ …, (queryCosted startBlock count).erase =
       some (bpRangeMinExcess …, bpRangeArgMinPrefixPos …))        -- algebra + summary + leftmost
```

- **Worker A:** the navigator construction — instantiate the global table on
  Instrumented; build the local tables with offset re-encoding; wire the
  comparator to `summaryCosted`; the ≤3-candidate query + leftmost merge.
- **Worker B:** `interiorOverhead` o(n) — define `logLogSquaredSampledDirectoryOverhead`,
  prove its `LittleOLinear`, and sum the three terms.
- **Coordinator:** retire the `blockCount²` mirage now — this navigator *replaces*
  `interiorBlockPairRanges`; delete it and its `axiom_check` entry in the same
  round the navigator lands (retire-don't-bless).

## References

- J. Fischer. *Optimal Succinctness for Range Minimum Queries.* LATIN 2010.
  arXiv:0812.2775. (2n+o(n) bits, O(1); optimality.)
- G. Navarro, K. Sadakane. *Fully Functional Static and Dynamic Succinct Trees.*
  ACM TALG 2014. arXiv:0905.0768. (rmM-tree; BP RMQ/LCA reduced to O(1) primitives
  over sampled/block summaries.)
- J. Cordova, G. Navarro. *Simple and Efficient Fully-Functional Succinct Trees.*
  2016. arXiv:1601.06939.
- D. Baumstark et al. *Faster Range Minimum Queries.* 2017. arXiv:1711.10385.
  (Sparse table over block minima: O((n/b)log(n/b)) words — the granularity/space
  accounting this design relies on.)
- M. Bender, M. Farach-Colton. *The LCA Problem Revisited.* LATIN 2000. (±1 RMQ +
  universal block table for the in-block micro layer.)
