# Interior O(1) Range-Min Navigator Design

Worker-facing design for `concreteBPRelativeRmmInteriorDirectory_profile`, the
current close-side bottleneck for the BP-native `2*n + o(n)`, `O(1)` succinct
RMQ theorem.

This note records the agreed construction target. It is a design guide, not a
completed proof claim.

## Key Insight

Do not build a full Navarro-Sadakane rmM tree yet, and do not store all
block-range answers. The remaining interior query is smaller:

- the BP string has length `2*n`;
- complete-block summaries reduce the live sequence to about `n / log n`
  block minima;
- B's relative summary table can recover a candidate block's true
  `(minExcess, argMinPrefixPos)` with charged point reads and cost `<= 4`.

So the navigator should store only indices or offsets into that shrunk
block-minimum sequence. Values are recovered only when comparing the constant
number of query candidates.

That index/value decoupling is the central trick: it gives `o(n)` payload and
prevents the proof-only-oracle failure mode, because a real query must read both
the navigator payload and the relative-summary payload.

## Construction

Let `m` be the number of complete-block minima, roughly `n / log n`.

1. Split the `m` block minima into macroblocks of about `(log n)^2` blocks.
2. For each macroblock, build local sparse tables over its block minima. Store
   local offsets, not global `Nat` values. Each offset needs `O(log log n)` bits.
3. Build a global sparse table over the macroblock minima. Its entries identify
   representative block indices for whole-macroblock ranges.
4. Answer an interval by merging at most three candidates:
   the left macroblock suffix, the right macroblock prefix, and the middle
   whole-macroblock range.
5. For each candidate block, use the relative summary table to read the true
   minimum excess and argmin prefix position. Merge by `(minExcess, leftmost
   block index)`.

The query cost is constant because it performs a fixed number of table reads and
candidate comparisons. The space is `o(n)` because the local tables cost roughly

`n * (log log n)^2 / log n`

bits, and the global macroblock table costs roughly

`n / log n`

bits.

## Sparse-Table Reuse Discipline

`RMQ.SparseTable.Instrumented` is useful because it already proves the sparse
table query algebra and leftmost tie policy for stored argmin indices. Reuse
that proof pattern and, where possible, theorem shapes.

Do not reuse its `betterIndexArray (xs : Array Int)` as an uncharged value
oracle for this succinct navigator. In the final construction, candidate
comparison must be tied to charged payload reads:

- read a candidate offset/index from the navigator payload;
- read its block minimum/argmin information through B's relative summary table;
- compare those decoded candidate values with the leftmost tie rule.

The local tables should store local offsets. A local table storing global
`Option Nat` entries would be too wide for the fine-grained layer.

## Tie Policy

Leftmostness must be enforced at every level:

- local sparse table cells store the leftmost minimum within their span;
- global sparse table cells store the leftmost minimum macro representative;
- the final three-candidate merge breaks ties by smaller block index.

Only enforcing leftmostness at the last merge is not enough if an intermediate
table has already discarded the leftmost minimizer.

## Overhead Target

The existing `concreteBPRelativeRmmInteriorOverhead` should be extended or
replaced so it pays for:

- the charged relative summary table;
- local offset sparse tables, with a new little-o envelope like
  `logLogSquaredSampledDirectoryOverhead`;
- the global macroblock sparse table or top routing;
- machine-word bounded reads for all payload words.

The new local-table envelope should model fixed-slot

`n / log n * (log log n)^2`

payload and prove `LittleOLinear` Mathlib-free, using the same style as
`logLogSampledDirectoryOverhead_littleO` and `sampledDirectoryOverhead_littleO`.

## Target Theorem

The construction should culminate in a concrete theorem shaped like:

```lean
theorem concreteBPRelativeRmmInteriorDirectory_profile
    (shape : Cartesian.CartesianShape)
    (hsize : 2 ^ 128 <= shape.size) :
    let directory := concreteBPRelativeRmmInteriorDirectory shape
    SuccinctSpace.LittleOLinear concreteBPRelativeRmmInteriorOverhead /\
      directory.payload.length <=
        concreteBPRelativeRmmInteriorOverhead shape.size /\
      (forall startBlock count,
        (directory.rangeMinCosted startBlock count).cost <=
          concreteBPRelativeRmmInteriorQueryCost) /\
      (forall {startBlock count : Nat},
        0 < count ->
          startBlock + count <= canonicalBPRelativeSummaryBlockCount shape ->
            (directory.rangeMinCosted startBlock count).erase =
              some
                (bpRangeMinExcess shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count,
                 bpRangeArgMinPrefixPos shape
                  (canonicalBPRelativeSummaryBlockSize shape)
                  startBlock count)) /\
      directory.read_words_length_le_machine
```

The exact names may evolve, but the obligations should not: concrete payload,
constant charged query, exact leftmost range-min witness, little-o overhead, and
machine-word bounded reads.

## Non-Targets

These do not close the milestone:

- a direct scan over all interior blocks;
- a dense all-pairs block-range table;
- a sparse table over every block minimum at global granularity;
- a Cartesian-shape universal table over `(log n)^2`-sized macroblocks;
- a proof-only oracle or abstract profile whose query reads no payload;
- an adapter with `payloadWordsRead := fun _ _ => []`;
- an uncharged external accessor standing in for candidate values.
- a selector-cell bridge whose exactness assumes the cell already contains the
  semantic winner, such as `selectorEntries[slot]? = some
  (bpRangeArgMinBlock ...)`, unless the same construction also builds the
  local/global/top selector entries, routes the query to that slot, and consumes
  the bridge in `concreteBPRelativeRmmInteriorDirectory_profile`.

## Worker Split

Worker A owns the concrete navigator and exactness:

- define the local/global table representations;
- implement the at-most-three-candidate query;
- prove the query exact by composing sparse-table leftmostness, relative summary
  exactness, and the final leftmost merge;
- consume `concreteBPRelativeRmmInteriorDirectory_parameter_profile_of_size_ge`.

Worker B owns the remaining space arithmetic:

- define the local sparse-table overhead envelope;
- prove it is `LittleOLinear`;
- package the final interior overhead budget and machine-word side conditions
  in a theorem A can consume directly.
- if the space arithmetic is already closed, the next B-owned target is not
  another answer-as-premise bridge. It is the concrete selector layer: built
  entries, slot arithmetic, payload budget, machine-word bounds, and an
  exactness theorem with no premise that a selector cell already stores the
  semantic winner.

The coordinator should retire the dense `interiorBlockPairRanges` path once the
concrete navigator profile lands.
