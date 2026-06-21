# Succinct Select Locator Architecture

This note pins down the final select-side architecture for the concrete
`2*n + o(n), O(1)` BP-native RMQ target.

The immediate purpose is to prevent more worker loops from satisfying a weak
interface while missing the word-RAM substance.  The final close-access witness
needs a concrete false-select locator for `shape.bpCode`, not another abstract
`selectCosted` field and not a dense occurrence-indexed local table.

## Research Anchor

The classical fact we are relying on is stable:

- Raman, Raman, and Rao's indexable dictionary supports `Rank` and `Select` in
  `O(1)` time on the RAM model with `B(n,m) + o(n) + O(log log m)` bits for an
  `n`-element subset of a universe of size `m`.
  Source: https://arxiv.org/abs/0705.0552
- Modern engineering surveys still state the uncompressed bitvector version:
  rank/select on a length-`n` bitvector can be answered in `O(1)` time with
  `o(n)` additional bits.
  Source: https://arxiv.org/abs/2206.01149
- The BP side is aligned with the standard succinct-tree target: static trees
  have `2n + o(n)`-bit representations with constant-time operations in the
  word-RAM model, and range min-max trees are the standard BP navigation
  technology.
  Source: https://arxiv.org/abs/0905.0768

For this repository, the proof-friendly route is not to formalize the full RRR
entropy-compressed dictionary first.  The right near-term target is a
Clark/RRR-style sampled select locator specialized to the false bits of
`shape.bpCode`, with explicit sparse exceptions and a bounded dense local
case.

## Binding Design Choice

Use a sparse/dense inventory for `select false shape.bpCode idx`.

Let

```lean
w n   := SuccinctRankProposal.machineWordBits n
ell n := Nat.log2 (w n) + 1
```

The concrete constants may move during implementation, but the asymptotic
shape should not:

```lean
superStride n      := (w n) * (w n)
localStride n      := max 1 ((w n) / ((ell n) * (ell n)))
superLongSpan n    := superStride n * w n * ell n
localSparseSpan n  := w n
```

The directory stores four kinds of payload-backed entries.

1. Super inventory, every `superStride n`-th false occurrence:
   base occurrence, base position, span class, and pointer.

2. Long-super explicit payload:
   if a super interval has span `> superLongSpan n`, store all selected
   positions in that super interval.  Long spans are disjoint, so the number of
   such intervals is at most `bits.length / superLongSpan n`.

3. Short-super local inventory, every `localStride n`-th false occurrence
   inside short super intervals:
   local base occurrence, local base position, span class, and pointer.

4. Sparse-local explicit payload:
   if a local interval has span `> localSparseSpan n`, store all selected
   positions in that local interval.  Sparse local spans are disjoint, so the
   number of such intervals is at most `bits.length / localSparseSpan n`.

If a local interval has span `<= localSparseSpan n`, the selected false bit is
within a window of length at most one machine word.  Because the window may
cross an alignment boundary, the query reads at most two aligned payload words,
uses counted word-rank to decide whether the answer is in the first word, and
then uses counted `RAM.selectBoolWord` in the chosen word.

This is the core anti-blocker: dense local cases are solved by a real charged
two-word query, not by a pure `blockIndex` oracle that already knows the
selected word.

## Query Shape

The final costed query should be definitionally close to this:

```text
selectCloseCosted idx:
  occ := min idx falseCount
  read super entry for occ / superStride
  if occ is outside the false count:
    return none
  if super entry is long:
    read explicit long position at pointer + local occurrence
  else:
    read local entry for local occurrence / localStride
    if local entry is sparse:
      read explicit sparse position at pointer + local occurrence
    else:
      read payload word at local base position / wordSize
      count usable false bits in that first word
      if local occurrence is in first word:
        select in first word
      else:
        read next payload word
        select remaining occurrence in second word
```

All table and payload reads must be charged.  All word reads must prove the
read word length is bounded by `machineWordBits bits.length`.

## Space Budget

The intended auxiliary overhead is a sum of these envelopes:

```lean
superDirectoryOverhead n       = O(n / w n)
longSuperExplicitOverhead n    = O(n / ell n)
localDirectoryOverhead n       = O(n * (ell n)^3 / w n)
sparseLocalExplicitOverhead n  = O(n / ell n)
```

The current repo already has `LittleOLinear` support for `n / log n`, for
`n * loglog n / log n`, and for `n * (loglog n)^2 / log n`.  This architecture
will likely require two small arithmetic extensions:

```lean
theorem littleOLinear_id_div_logLog_succ :
    SuccinctSpace.LittleOLinear
      (fun n => n / (Nat.log2 (Nat.log2 n + 1) + 1))

def logLogCubedSampledDirectoryOverhead (slots : Nat) (n : Nat) : Nat :=
  slots * ((n / (Nat.log2 n + 1)) *
    ((Nat.log2 (Nat.log2 n + 1) + 1) *
      ((Nat.log2 (Nat.log2 n + 1) + 1) *
        (Nat.log2 (Nat.log2 n + 1) + 1))))

theorem logLogCubedSampledDirectoryOverhead_littleO (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (logLogCubedSampledDirectoryOverhead slots)
```

Those lemmas are arithmetic support, not select closure.  A worker should prove
them only if immediately consumed by the concrete select locator budget.

## Interface Correction

The existing
`SuccinctSelectProposal.TwoLevelPayloadLiveStoredWordSelectData` is still useful
for rank/select scaffolding and for the current read-backed adapter, but it is
probably too narrow for the final false-select construction.  Its query shape
reads one local table sample and one aligned payload word.  The sparse/dense
locator needs branch-specific explicit reads and a dense two-word path.

Therefore the final implementation should introduce a concrete false-select
surface whose query is defined from its payload fields:

```lean
structure SparseDenseFalseSelectCloseData
    (shape : Cartesian.CartesianShape)
    (overhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine :
    wordSize <= SuccinctRankProposal.machineWordBits shape.bpCode.length

  -- Payload-backed tables for the four entry classes above.
  superPayload : List Bool
  longExplicitPayload : List Bool
  localPayload : List Bool
  sparseExplicitPayload : List Bool

  payload_length_le :
    (superPayload ++ longExplicitPayload ++
      localPayload ++ sparseExplicitPayload).length <= overhead

  -- Entry decoders and table-read exactness proofs go here.  They should be
  -- concrete fixed-width payload decoders, not arbitrary answer fields.
```

Then define, not store as a field:

```lean
def SparseDenseFalseSelectCloseData.selectCloseCosted
    (data : SparseDenseFalseSelectCloseData shape overhead queryCost)
    (idx : Nat) : Costed (Option Nat) := ...
```

Required profile:

```lean
theorem sparseDenseFalseSelectCloseData_profile
    (shape : Cartesian.CartesianShape) :
    let data := sparseDenseFalseSelectCloseData shape
    data.payload.length <= sparseDenseFalseSelectOverhead shape.size /\
      (forall idx,
        (data.selectCloseCosted idx).cost <= sparseDenseFalseSelectQueryCost) /\
      (forall idx,
        (data.selectCloseCosted idx).erase =
          SuccinctSpace.bpCloseOfInorder? shape idx) /\
      data.read_words_length_le_machine
```

The read-backed final close-access layer should then consume this concrete
false-select component plus the existing rank-false component.  If the current
`ReadBackedBPCloseAccessDirectory` remains tied to
`TwoLevelPayloadLiveStoredWordSelectData`, add a sibling final theorem for the
sparse/dense close-access directory rather than forcing this construction
through the old one-word select shape.

## Non-Goals And Invalid Stops

These are known traps, not milestones:

- A dense occurrence-indexed local table.  It gives exact select but its payload
  is linear or worse.
- A pure `blockIndex : Bool -> Nat -> Nat` that computes the selected payload
  word without charged reads.
- A local descriptor theorem whose hypotheses already contain the selected
  word, selected position, or exact run membership.
- A read-backed adapter from an abstract rank/select family with no concrete
  compact select family.
- Another impossibility theorem for the dense locator unless it also proves the
  sparse/dense target above is misspecified.

The named positive target is the concrete sparse/dense false-select profile and
its consumption by the final BP-native RMQ theorem.

