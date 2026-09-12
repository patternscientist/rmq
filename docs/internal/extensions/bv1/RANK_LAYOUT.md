# BV-1 actual Jacobson rank layout leaf

Status: INCOMPLETE (whole BV-1 composition). The assigned RankLayout leaf is
proved and checked, for coordinator reconstruction. Whole BV-1 acceptance rows
remain OPEN; this leaf supplies actual-array geometry for the final allocation.

Governance `0e6a00f654abc64f8b68988fa9675b9a839dca2f`, continuation checkpoint
`645a0502b9da9ad6444edbe44759e1c2c5661f25`. This is the same preflighted
proof-sprint worker and completion gate. Scope is only RankLayout.lean and this
file. No root Allocation/AllocationLayout edits, shared-module changes or commit.
No Lean command until the next explicit shared build grant.

## Frozen requirements

Coordinator: "Prove actual jacobsonRankData scalar equalities wordSize=M,
blocksPerSuper=M, regularity of sentinel raw and four sample arrays, each sample
count≤n+1, rawcount≤2*n+2, each sampleword width≤2*M+3, rawword≤M. Actual d arrays
with cast bridge, no canonical readiness hypothesis. Root consumes these for
final Allocation's rankSegments widths/regularity and rawalias geometry."

Here d=jacobsonRankData bits, n=bits.length, M=machineWordBits n. The exact
four-array list is, in final allocation order:

```lean
[d.superTables.falseTable.store.words, d.superTables.trueTable.store.words,
 d.blockTables.falseTable.store.words, d.blockTables.trueTable.store.words]
```

It is called jacobsonSampleArrays in this independent leaf and is definitionally
the root Allocation.rankSegments list. The raw array is the actual
d.bitWords.store.words, including its n+1 trailing empty sentinels. No easier
uncasted replacement record or readiness assumption is an accepted endpoint.

## Frozen local evidence rows

| ID | Requirement | Exact target |
|---|---|---|
| RL-SCALAR | Actual scalar equalities across overhead cast. | d.wordSize=M; d.blocksPerSuper=M; also d.superWidth=M and d.blockWidth=machineWordBits(M*M). |
| RL-RAW | Actual sentinel array regularity, count, width. | RegularWords d.bitWords.store.words; size≤2*n+2; every member word.length≤M. |
| RL-SAMPLE | All four actual sample arrays regular/count/width. | For every words in the list above: RegularWords words, size≤n+1, every member word.length≤2*M+3. |
| RL-JOIN | Same-record unconditional endpoint. | jacobsonRankLayout conjunction with only bits as input. |
| RL-CHECK | Expected-type consumption and trust. | Narrow build, explicit full-array consumer, cast/raw identity diagnostics, hygiene and whitespace. |

Proof chain: transport runtime projections across the two existing overhead
equalities used by jacobsonRankData; identify actual scalars/raw words/entry
lists with the existing constructor's values; use exact canonical entry counts
and FixedWidthNatTable.read_exact for word counts; use existing regularity for
fixed-width arrays and chunk stores with sentinels; use the existing logarithmic
block-width bound. The uncast constructor is only a proof intermediate feeding
equalities for the actual d. It never replaces the required object.

The planned trust challenge checks the exact actual-sample list in an explicit
typed consumer. The existing RegularLayout rejection of #[[],[true]] remains
the regularity obstruction; this leaf does not claim a new source mutation
campaign or whole BV-1 closure. A positive sample-count weakening or readiness
condition is forbidden by the expected type of the unconditional same-record
join.

No new design/process choice is made; this implements the assigned final
allocation consumer. Root owns public claims, ledgers, and broad integration
gates. Verification and proof digestion follow after checks.

## Checked propositions and object identity

RL-SCALAR is proved by the four scalar equality theorems. `jacobson_project`
transports any nondependent runtime projection across the existing two overhead
equalities used in `jacobsonRankData`. The generic cast lemma substitutes those
equalities and closes by reflexivity, including proof irrelevance for the cast
proof. Applying it to wordSize, blocksPerSuper, superWidth, and blockWidth gives
the exact four formulas in the frozen row. Applying it to `.bitWords.store.words`
gives `jacobson_raw_words_eq`, an equality of the actual casted array to
`(BoundedPayloadWordStore.ofChunksWithSentinel bits (machineWordBits_pos n)).store.words`.

RL-RAW follows on that same actual array. `jacobson_raw_regular` rewrites with
its checked raw-array identity and consumes the previous complete sentinel
regularity theorem. `jacobson_raw_count_le` counts real chunks plus exactly n+1
empty sentinel words and uses the existing chunk-count bound. Its literal
conclusion is `d.bitWords.store.words.size ≤ 2*n+2`. The raw member-width bound
uses the actual bounded bit-store field and the actual record's machine-word
bound to conclude `word.length ≤ M`.

RL-SAMPLE handles every member of the exact four-array list, including both
targets at both levels. Regularity uses each actual FixedWidthNatTable record.
Word count comes from its `read_exact` Option equality: mapping every stored
word through the decoder equals the reference entries, hence the array size
equals the entry count. Cast projection transport identifies those actual entry
lists with the existing canonical super/block entry lists, whose exact lengths
are n/M/M+1 and n/M+1, respectively. Both are at most n+1. Fixed-table successful
word lengths equal the actual table width. The super width is M; the block
width is machineWordBits(M*M), at most 2*M+3 by the existing logarithmic bounds.

RL-JOIN is exactly this unconditional checked proposition:

```lean
theorem jacobsonRankLayout (bits : List Bool) :
  let d := jacobsonRankData bits
  let n := bits.length
  let m := machineWordBits n
  d.wordSize = m ∧ d.blocksPerSuper = m ∧
    RegularWords d.bitWords.store.words ∧ d.bitWords.store.words.size ≤ 2*n+2 ∧
    (∀ word ∈ d.bitWords.store.words.toList, word.length ≤ m) ∧
    ∀ words ∈ jacobsonSampleArrays bits,
      RegularWords words ∧ words.size ≤ n+1 ∧
        ∀ word ∈ words.toList, word.length ≤ 2*m+3
```

The exact fresh-import consumer below expands jacobsonSampleArrays back to all
four actual table-array projections. It therefore checks the same record and
same array identities the allocation owner needs. Every regularity conclusion
has the original RegularWords definition: actual indexed words equal their
firstLength-stride slices of their own flattened bits. The min-length slice
corollaries remain available from RegularLayout. No whole-allocation safety,
capacity, or source/controller result is inferred from these component facts.

## Verification

| Stage | Result | Seconds | Diagnostic |
|---|---|---:|---|
| rank-layout-1 | PASS | 10.557 | All proofs passed; one deprecated Array.size_toArray alias warning. |
| rank-layout-2 | PASS | 8.065 | Replaced alias by List.size_toArray; clean source, no warnings. |
| rank-layout-consumer | PASS | 8.546 | Seven exact typed consumers and twelve axiom reports, no warnings. |

Checks used the explicitly granted c974 build slot, one job, the pinned direct
v4.22.0 Lake binary and owned runner with unique stages and 180-second deadlines.
The direct binary avoids the previously observed elan shim network attempt.
There was no timeout, output cap, or abandoned process. The slot was released
immediately after the consumer completed. Commands and results are recorded in
`commands/rank-layout-*.json`.

Final source: 9815 bytes, SHA256
`7A5756940175BD775A0F4F0928EBB01F222C7C8DB0461CB12C74770A6F8D629B`.
Required RMQ-wide trust-keyword/Mathlib and native-decision scans found no
matches. `git diff --check` and untracked-source whitespace checks passed
(only Git newline-conversion notices). Broad gates were skipped because this
is a bounded component lemma with a fresh exact-type consumer; integration and
public closure remain with the coordinator.

All twelve public theorem diagnostics report only existing standard
`propext`, `Classical.choice`, and `Quot.sound`. There is no new trusted
declaration or external dependency. The fresh import also checks the existing
exact regularity rejection `¬RegularWords #[[],[true]]`. This is an actual
rejection at the same regularity predicate, not a claim that count/width alone
implies regularity or that a full source mutation campaign has been run.

## Proof digestion

The work bridges an overhead-accounting cast to the actual runtime projections
used in rank. In plain English, the record's relabeling of proof indices does
not change its word size, block geometry, words, or samples. Its four sample
arrays and sentinel raw view are now proved to have the shape and small
logical dimensions required by the final allocation.

There are no live readiness or size assumptions: only the input list is a
parameter. A skeptical grad student should next ask whether the final physical
descriptors point to these very arrays, whether the raw sentinel view aliases
the single counted raw bit range correctly, and whether all numeric addresses
and intermediate values fit the physical word width. Those are the final
allocation/reader/safety composition obligations; these component facts feed
them without claiming to close them. Whole BV-1 remains incomplete.

## Exact fresh-import consumer

```lean
import RMQ.Core.WordRAM.Bitvector.RankLayout
open RMQ RMQ.PackedBitvector RMQ.SuccinctSpace RMQ.SuccinctRank
example (bits : List Bool) : (jacobsonRankData bits).wordSize = machineWordBits bits.length :=
  jacobson_wordSize_eq bits
example (bits : List Bool) : (jacobsonRankData bits).blocksPerSuper = machineWordBits bits.length :=
  jacobson_blocksPerSuper_eq bits
example (bits : List Bool) :
  (jacobsonRankData bits).bitWords.store.words =
    (BoundedPayloadWordStore.ofChunksWithSentinel bits (machineWordBits_pos bits.length)).store.words :=
  jacobson_raw_words_eq bits
example (bits : List Bool) :
  let d := jacobsonRankData bits
  let n := bits.length
  let m := machineWordBits n
  d.wordSize = m ∧ d.blocksPerSuper = m ∧
    RegularWords d.bitWords.store.words ∧ d.bitWords.store.words.size ≤ 2*n+2 ∧
    (∀ word ∈ d.bitWords.store.words.toList, word.length ≤ m) ∧
    ∀ words ∈ [d.superTables.falseTable.store.words, d.superTables.trueTable.store.words,
      d.blockTables.falseTable.store.words, d.blockTables.trueTable.store.words],
      RegularWords words ∧ words.size ≤ n+1 ∧
        ∀ word ∈ words.toList, word.length ≤ 2*m+3 := jacobsonRankLayout bits
example (bits : List Bool) :
  (jacobsonRankData bits).superWidth = machineWordBits bits.length := jacobson_superWidth_eq bits
example (bits : List Bool) :
  (jacobsonRankData bits).blockWidth =
    machineWordBits (machineWordBits bits.length * machineWordBits bits.length) := jacobson_blockWidth_eq bits
example : ¬RegularWords #[[], [true]] := irregular_empty_head_rejected
#print axioms jacobson_wordSize_eq
#print axioms jacobson_blocksPerSuper_eq
#print axioms jacobson_superWidth_eq
#print axioms jacobson_blockWidth_eq
#print axioms jacobson_raw_words_eq
#print axioms jacobson_raw_regular
#print axioms jacobson_samples_regular
#print axioms jacobson_samples_count_le
#print axioms jacobson_raw_count_le
#print axioms jacobson_sample_word_length_le
#print axioms jacobson_raw_word_length_le
#print axioms jacobsonRankLayout
```
