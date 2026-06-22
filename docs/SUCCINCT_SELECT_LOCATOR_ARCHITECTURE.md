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
   positions in that local interval as offsets from the interval's local base,
   not as absolute `0..n` BP positions, unless a separate theorem proves the
   absolute encoding still fits the named little-o budget. Sparse local spans
   are disjoint, so the number of such intervals is at most
   `bits.length / localSparseSpan n`.

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

Checked caveat for the current Lean surface: the implemented
`SparseDenseFalseSelectLocatorEntry` packs four equal-width fields into one
charged word. The theorem
`sparseDenseFalseSelectLocatorEntry_fullMachineField_not_word_bounded` proves
that four full machine-width fields cannot satisfy the machine-word read bound,
and the `SparseDenseFalseSelectCloseData.*_full_machine_field_impossible`
theorems lift this to present super/local locator entries. A concrete
dense-local builder should not try to store absolute BP base positions in that
one-word entry. It should use relative fields, split locator fields across a
bounded number of charged words, or prove that explicit exception payloads cover
the affected intervals within the named little-o budget.

The stronger invariant for the final C1 construction is:

- high-frequency local entries may not carry absolute `0..n` positions,
  absolute payload-word indices, or absolute table pointers;
- packed local fields must be tags, intra-window offsets, local rank deltas, or
  word-index deltas whose range is covered by the local span invariant;
- absolute full-width fields are allowed only in low-frequency super tables,
  long/sparse explicit exception payloads, or charged side tables whose total
  payload is separately proved `LittleOLinear`;
- when a low-frequency super table uses absolute full-width fields, it should
  store them in split charged fields or another word-bounded layout, not in the
  old one-word four-full-field locator codec;
- routing from an occurrence `q` to the local descriptor slot must be bounded
  arithmetic, not an uncharged predecessor/search function.

The preferred repaired layout is a rectangular local inventory. For a query
occurrence `q`, compute:

```text
superSlot        := q / superStride
localSlotInSuper := (q - super.baseOccurrence) / localStride
globalLocalSlot  := superSlot * localSlotsPerSuper + localSlotInSuper
```

With this layout, the super entry no longer needs to store an absolute base
pointer into the local table. A dense local descriptor should either live at
`globalLocalSlot` itself or be found through a charged dense-side locator whose
payload budget is proved separately. In particular, the final compact builder
should not use `loc.pointer` as an absolute index into a global
`denseLocalEntries` table.

For sparse-local exceptions, the same rule applies. A packed local descriptor
should not store an absolute pointer into the sparse explicit table. Use a
charged sparse-local flag/rank side structure, or another explicitly budgeted
side locator, to derive the exception base. The side locator may reuse the
rank/select primitives already present in the project, but its reads and
payload bits must be visible in the C1 profile.

The preferred exception-table layout is padded and relative, because it avoids a
second predecessor/prefix-sum problem. A long-super exception block reserves
`superStride` relative offsets; a sparse-local exception block reserves
`localStride` relative offsets. The query computes
`exceptionBlockRank * stride + localOccurrence` from a charged flag-rank
directory and reads a relative offset, then adds the stored base position. A
variable-length explicit table is acceptable only if it also supplies a charged
base-offset directory and proves that directory's payload budget.

Current positive repair surface:
`FixedWidthSparseDenseFalseSelectDenseLocalEntryTable` splits dense-local fields
across four independent fixed-width Nat tables and proves payload length,
unit-cost per-field reads, and machine-word bounds from only
`fieldWidth <= machineWordBits n`. `SparseDenseFalseSelectCloseData` now
consumes that table in its dense branch: after the packed local locator marks a
dense case, `selectCloseCosted` reads
`denseLocalTable.readCosted loc.pointer` and then runs the two-word BP payload
fallback from the split dense-local entry. The routing-helper theorem
`sparseDenseFalseSelectBranchObligations_of_built_entries` has been aligned to
the same split dense entry route, and
`sparseDenseFalseSelectBranchObligations_of_built_entries_and_dense_payload_facts`
replaces the dense answer-certificate premise with aligned-word and rank/local
occurrence routing facts over that split entry. The generated
`builtLongExplicitFalseSelectBranch` is useful as a sanity check for
long-explicit exactness, but it stores every false position and is not the
compact final construction.

Adversarial audit note: the split dense-local table is a useful representation
primitive, not by itself the final compact route. If it is populated with one
full-width row per high-frequency local interval, or addressed by an absolute
packed `loc.pointer`, it recreates the same space/routing failure in a more
polished form. The final C1 theorem must show both that the dense-entry address
is obtained by the rectangular arithmetic or charged side locator above, and
that the table's field widths and number of rows fit the named
`canonicalSparseDenseFalseSelectOverhead` budget.

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
- A full-width dense/local descriptor row for every high-frequency local
  interval unless its row count times field width is proved within the named
  little-o C1 budget. Splitting a bad global pointer into several charged words
  does not by itself make the construction succinct.
- Absolute `0..n` positions for sparse-local explicit entries at local-entry
  frequency. Sparse-local explicit payloads should store relative offsets, or
  the same theorem must prove the absolute payload remains little-o.
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
