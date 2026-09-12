# BV-1 canonical supplied-store rank semantics leaf

Status: INCOMPLETE (whole BV-1 composition). The assigned RankSemantics leaf
is proved and checked, for coordinator reconstruction; full BV-1 rows remain
OPEN until the actual source/reader/allocation composition closes.

Governance `0e6a00f654abc64f8b68988fa9675b9a839dca2f`; continuation checkpoint
`645a0502b9da9ad6444edbe44759e1c2c5661f25`. Canonical proof-sprint preflight and
completion gate carry forward from the same active governed worker. Write scope
is only `RankSemantics.lean` and this file. No commit, no shared-module change,
and no Lean process without the next explicit shared build grant.

## Frozen target and consumer chain

For every `bits : List Bool`, `target : Bool`, `prefix : Nat`, and supplied
`store : WordRAM.ReadStore`, put `d := SuccinctRank.jacobsonRankData bits` and
`c := SuccinctClose.bpFringeChunkBits (2 * bits.length)`. Prove

```lean
(packedRankRead 17 18 19 21 c target store bits.length
  d.wordSize d.blocksPerSuper prefix).value =
  Succinct.rankPrefix target bits prefix
```

under exactly the actual read agreements: segment17 is
`(d.superSampleWords target)[i]?`; segment18 is
`(d.blockSampleWords target)[i]?`; segment19 is
`d.bitWords.store.words[i]?`; segment21 is
`(SuccinctClose.bpFringeChunkTable c).store.words[i]?`.
The canonical rank store below is merely that logical interface to the actual
Jacobson arrays. Its raw words remain unnormalized and include the original
sentinel. Final Allocation must establish these agreements from its selected
super/block descriptor bank and shared raw sentinel alias. The source itself
does not receive a semantic rank answer or a Jacobson proof field.

```lean
def RankStoreAgrees (bits : List Bool) (target : Bool)
    (store : WordRAM.ReadStore) : Prop :=
  ∀ segment index, segment = 17 ∨ segment = 18 ∨ segment = 19 ∨ segment = 21 →
    store.readWord? segment index =
      (canonicalRankReadStore bits target).readWord? segment index
```

The stronger intermediate target is exact `.toCosted` equality with
`d.bpChunkedRankCosted c target prefix`. The existing supplied-store rank trace
agreement proves that equality. The existing chunked rank exactness theorem
then consumes c positive and d.wordSize at most 8*c, both derived canonically.
Every prefix is quantified, including saturation beyond the input length and
the empty input. The original scalar geometry is preserved: no blocks-per-super
constant or smaller substitute input is used.

## Frozen local acceptance rows

| ID | Requirement | Exact planned evidence |
|---|---|---|
| RS-GEOM | Derive c positive and raw width at most8*c. | Conjunction from original d.wordSize_le_machine, machine-word monotonicity, fringe bound. |
| RS-READ | Preserve all four actual components and their charged computation. | Exact `.toCosted = d.bpChunkedRankCosted c target prefix`. |
| RS-SEMANTIC | Full arbitrary-store, all-size, both-target rank endpoint. | Explicit expression above equals canonical List rankPrefix. |
| RS-CANONICAL | Inhabited canonical store consumer. | Same expression with actual Jacobson logical store, no agreement or width assumptions. |
| RS-CHECK | Exact typed consumers and trust diagnostics. | Narrow build, fresh import, same-domain constant-zero rejection, hygiene and whitespace. |

Anti-vacuity predicate is exactly `∀ bits target prefix, (run bits target prefix).value
= Succinct.rankPrefix target bits prefix`; the planned mutation substitutes
constant-zero TraceResult.pure at the same quantifiers. `[true]`, true, prefix1
rejects it. This tests the semantic predicate and does not claim source/memory
composition by itself.

No new architectural or process choice is made; this is the coordinator's
assigned consumer of the final shared allocation. Broad gates, public claims,
and design/workflow ledgers remain coordinator-owned. Verification and proof
digestion will be appended after the leaf's required checks.

## Read-only Jacobson allocation-safety inventory

This inventory reports existing definitions/theorems and consequences to be
proved by the allocation owner. It does not add or claim checked Allocation
fields. Put n=bits.length and m=machineWordBits n.

| Surface | Existing source | Exact information |
|---|---|---|
| Canonical word size | SuccinctRank.lean:1489 | jacobsonRankWordSize n = m |
| Blocks per super | SuccinctRank.lean:1498 | jacobsonRankBlocksPerSuper n = m |
| Super sample width | SuccinctRank.lean:1502 | jacobsonRankSuperWidth n = m |
| Block sample width | SuccinctRank.lean:1506 | jacobsonRankBlockWidth n = machineWordBits(m*m) |
| Builder side conditions | SuccinctRank.lean:1518 | Positive word size and blocks/super; wordSize≤m; n<2^superWidth; blocksPerSuper*wordSize<2^blockWidth |
| Rank record fields | SuccinctRank.lean:763 | wordSize_pos, wordSize_le_machine, blocksPerSuper_pos; original sample entries/tables and raw store; exact paired payload lengths |
| Super entry count | SuccinctRank.lean:457 | canonicalSuperRankEntries target bits wordSize blocksPerSuper has n/wordSize/blocksPerSuper+1 entries |
| Block entry count | SuccinctRank.lean:464 | canonicalBlockRankEntries target bits wordSize blocksPerSuper has n/wordSize+1 entries |
| Sample builders | SuccinctRank.lean:279,315 | canonicalSuperRankSampleTables / canonicalBlockRankSampleTablesOfLocalSpan use FixedWidthRankSampleTables.ofEntries |
| Table builders | SuccinctSpace/Tables.lean:419,64,35 | One encoded word per entry, through rank ofEntries -> natural ofEntries -> ofEncodedWords |
| Fixed table length | SuccinctSpace/Tables.lean:111 | table.payload.length = entries.length*width |
| Every successful fixed word | SuccinctSpace/Tables.lean:27 | table.word_length_of_get? proves returned word.length = width |
| Paired Jacobson super length | SuccinctRank.lean:1553 | exactly jacobsonRankSuperOverhead n = 2*((n/m/m+1)*m), with the source written as two summands |
| Paired Jacobson block length | SuccinctRank.lean:1564 | exactly jacobsonRankBlockOverhead n = 2*((n/m+1)*machineWordBits(m*m)), with two summands |
| Whole Jacobson profile | SuccinctRank.lean:1791 | d.auxPayload.length = superOverhead n + blockOverhead n; raw flattened payload=bits; all raw words≤m |

Raw sentinel detail matters for descriptor count. The constructor
`BoundedPayloadWordStore.ofChunksWithSentinel` at
`SuccinctSpace/WordStore.lean:576` uses
`(chunkPayloadWords wordSize bits ++ List.replicate (n+1) []).toArray`.
It appends n+1 empty sentinel words, not just one. The raw array's exact count
therefore follows from `chunkPayloadWords_length_eq_div_add_indicator`
(WordStore.lean:390):

```text
n/m + (if n%m = 0 then 0 else 1) + n+1.
```

`chunkPayloadWords_length_le_div_add_one` (WordStore.lean:369) gives the coarse
bound n/m+n+2 ≤ 2*n+2. Both sample entry counts are at most n+1. The extra empty
words contribute zero payload bits; `ofChunksWithSentinel_erases` at632
preserves exactly bits. All-size short-first and empty-word regularity is
already in the separate checked RegularLayout leaf.

For bounding block-word width by the experiment's physical width, use
`machineWordBits_mul_self_log_bound` (SuccinctRank.lean:1656) and
`nestedMachineWordBits_le_succ` (1581) to obtain
`machineWordBits(m*m) ≤ 2*m+3 < 32+16*m`. The latter right side is exactly
`Experiment.width n` (SelectExperiment.lean:22). This is a proof route reported
to the allocation owner, not a new checked width theorem in this semantic leaf.

The canonical object chain is jacobsonRankData (SuccinctRank.lean:1775) ->
canonicalTwoLevelRankDataOfChunksExactLocalBlock (1331) ->
canonicalTwoLevelRankDataOfBridgeLocalBlock (1193) ->
canonicalRankWordBridgeOfChunksWithSentinel (1097) -> the raw store constructor
above. `jacobsonRankData` changes the overhead indices via a cast. No existing
direct lemma equating its scalar projections to the four canonical formulas
was found in the searched rank modules; the allocation proof may need to
transport projections across that cast before using the count formulas. The
semantic theorem avoids this issue by retaining the actual record scalars and
using its own existing word-size bound.

## Checked exact propositions and chain

The source calls the arbitrary prefix variable `limit`, an alpha-renaming of
the frozen target's `prefix` because Lean reserves the latter token. There is
no change in quantifiers, domain, bound, or result.

RS-GEOM is `canonical_rank_chunk_geometry bits`: with the original d and c,
`0<c ∧ d.wordSize≤8*c`. It follows from d.wordSize_le_machine and
`machineWordBits n ≤ machineWordBits (2*n) ≤ 8*c`, plus the existing positive
fringe chunk size theorem. No caller-supplied positivity/size hypothesis remains.

RS-READ is `rankRead_toCosted_of_agree bits target store hagree limit`, whose
literal proposition is:

```lean
let d := jacobsonRankData bits
let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
(packedRankRead 17 18 19 21 c target store bits.length
  d.wordSize d.blocksPerSuper limit).toCosted =
  d.bpChunkedRankCosted c target limit
```

`packedRankRead` is definitionally the existing
`d.bpChunkedRankTraceResultWithStore` on the same store, four segments, target,
c, and limit. Its supplied-store `.toCosted_of_agree` theorem consumes each
actual agreement. Nothing is looked up through a replacement proof-side value.

RS-SEMANTIC is `rankRead_value_of_agree`: the exact same expression's `.value`
equals `Succinct.rankPrefix target bits limit`. Taking Costed.value of RS-READ
gives the same existing chunked value. `d.bpChunkedRankCosted_exact` consumes
that d, target, limit, and the two derived hypotheses from RS-GEOM to conclude
the reference rank. RS-CANONICAL is `canonicalRankRead_value`, with the actual
canonical logical store and reflexive agreements. Every bits/target/limit is
quantified; rank saturation is inherited from the existing evaluator rather
than imposed as an input restriction.

RS-CHECK includes an in-source consumer that expands all four agreements to
the actual arrays, plus the fresh-import consumer preserved below. The latter
checks seven exact propositions: geometry, full Costed equality, arbitrary
store with explicit four agreements, canonical store value, empty input at an
arbitrary limit, saturated singleton limit10, and the same-domain mutation
refutation. `constant_zero_rank_rejected` rejects the exact semantic predicate
with a constant-zero run, using `[true]`, true, limit1. That refutation has no
axioms; it does not stand for a broader source-mutation campaign.

## Verification

| Stage | Result | Seconds | Diagnostic |
|---|---|---:|---|
| rank-semantics-1 | FAIL | 8.723 | Parser rejected reserved binder token prefix. |
| rank-semantics-2 | PASS | 7.574 | Alpha-renamed binder to limit; all source proofs pass without local warnings. |
| rank-semantics-consumer | FAIL | 5.161 | Empty-list control required the explicit rankPrefix_nil theorem at a variable limit. |
| rank-semantics-consumer-2 | PASS | 3.905 | Seven typed checks, five axiom reports; no local warnings. |

All checks ran with the granted shared build slot, one job, pinned direct
v4.22.0 Lake, unique owned stages, and a 180-second deadline. No timeout,
output cap, or abandoned process occurred. The slot was released immediately
after the successful consumer. Dependency warnings replayed from existing
SuccinctFinalRAM and ReviewerReachabilitySmall; this new module has none.
Command records are in `commands/rank-semantics-*.json`. Direct Lake avoids the
previously observed elan shim network attempt.

Final source is 6212 bytes, SHA256
`9AC0B86BC1630635EAA63A3DC3C3889206A0FDFB0205DD86C36ECF7F5516AB7C`.
Required RMQ-wide trust-keyword/Mathlib and native-decision scans had no matches.
`git diff --check` passed; explicit untracked-file checks also passed with only
newline-conversion notices. No full gate was run: this independent leaf and
its direct consumer were checked narrowly, and the coordinator owns broad
integration certification.

The four substantive diagnostics use only existing standard `propext`,
`Classical.choice`, and `Quot.sound`; constant_zero_rank_rejected has no axioms.
No new trusted declaration, external dependency, or executable oracle is added.

## Proof digestion

The work identifies the exact logical rank operation that the final shared
allocation must serve. In plain English, reading the two selected sample
tables, the original raw word (including its sentinel), and the shared chunk
table returns the correct count for either Boolean value and any requested
prefix. It also preserves the existing logical Costed computation exactly.

The arbitrary-store result has four live read-agreement assumptions and no
input-domain restrictions; the canonical logical store satisfies them without
additional assumptions. This is not a proof that the numeric source fetches
those words from the final packed memory. A skeptical grad student should ask
next whether the final Allocation's descriptors and reader establish the same
four agreements, and whether the source's rank block refines this exact scalar
expression. Those independent composition obligations remain with the
coordinator/controller/reader work. RankLayout will separately discharge the
actual Jacobson casted-array geometry and count/width bounds.

## Exact fresh-import consumer

```lean
import RMQ.Core.WordRAM.Bitvector.RankSemantics
open RMQ RMQ.PackedBitvector RMQ.SuccinctRank RMQ.SuccinctFinal.PackedCellProbe
example (bits : List Bool) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  0 < c ∧ d.wordSize ≤ 8*c := canonical_rank_chunk_geometry bits
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hagree : RankStoreAgrees bits target store) (limit : Nat) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).toCosted =
    d.bpChunkedRankCosted c target limit := rankRead_toCosted_of_agree bits target store hagree limit
example (bits : List Bool) (target : Bool) (store : WordRAM.ReadStore)
  (hsuper : ∀ i, store.readWord? 17 i = ((jacobsonRankData bits).superSampleWords target)[i]?)
  (hblock : ∀ i, store.readWord? 18 i = ((jacobsonRankData bits).blockSampleWords target)[i]?)
  (hword : ∀ i, store.readWord? 19 i = (jacobsonRankData bits).bitWords.store.words[i]?)
  (hchunk : ∀ i, store.readWord? 21 i = (SuccinctClose.bpFringeChunkTable
    (SuccinctClose.bpFringeChunkBits (2 * bits.length))).store.words[i]?) (limit : Nat) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedRankRead 17 18 19 21 c target store bits.length d.wordSize d.blocksPerSuper limit).value =
    Succinct.rankPrefix target bits limit := by
  apply rankRead_value_of_agree bits target store _ limit
  intro segment index hs
  rcases hs with rfl | rfl | rfl | rfl
  · exact hsuper index
  · exact hblock index
  · exact hword index
  · exact hchunk index
example (bits : List Bool) (target : Bool) (limit : Nat) :
  let d := jacobsonRankData bits
  let c := SuccinctClose.bpFringeChunkBits (2 * bits.length)
  (packedRankRead 17 18 19 21 c target (canonicalRankReadStore bits target)
    bits.length d.wordSize d.blocksPerSuper limit).value = Succinct.rankPrefix target bits limit :=
  canonicalRankRead_value bits target limit
example (target : Bool) (limit : Nat) :
  (packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits 0) target
    (canonicalRankReadStore [] target) 0 (jacobsonRankData []).wordSize
    (jacobsonRankData []).blocksPerSuper limit).value = 0 :=
  by simpa only [List.length_nil, Nat.mul_zero, Succinct.rankPrefix_nil] using canonicalRankRead_value [] target limit
example :
  (packedRankRead 17 18 19 21 (SuccinctClose.bpFringeChunkBits 2) true
    (canonicalRankReadStore [true] true) 1 (jacobsonRankData [true]).wordSize
    (jacobsonRankData [true]).blocksPerSuper 10).value = 1 :=
  canonicalRankRead_value [true] true 10
example : ¬ (∀ (bits : List Bool) (target : Bool) (limit : Nat),
  (WordRAM.TraceResult.pure 0).value = Succinct.rankPrefix target bits limit) :=
  constant_zero_rank_rejected
#print axioms canonical_rank_chunk_geometry
#print axioms rankRead_toCosted_of_agree
#print axioms rankRead_value_of_agree
#print axioms canonicalRankRead_value
#print axioms constant_zero_rank_rejected
```
