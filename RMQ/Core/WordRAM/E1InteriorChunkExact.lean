import RMQ.Core.SuccinctSpace.MachineChunkedTable
import RMQ.Core.WordRAM.E1InteriorChunkFold

/-! # Non-final-chunk exactness for the machine-chunked table store

`interiorChunkFold_cOut_eq_routeDecode` (`E1InteriorChunkValue.lean:526`)
carries two width premises.  `hle` bounds EVERY chunk and discharges
verbatim from the store's own `word_length_le` field.  `hexact` demands
EQUALITY, but only of a chunk that has another chunk above it
(`j + 1 < n`); the final chunk's width is spurious because its tail
contributes `2 ^ w.length * 0`.

DD-20260719-009 recorded that cut, and it is correct.  What DD-009 got
wrong -- and M3d-15 caught by evaluation -- is the DISCHARGE: it declared
`hexact` VACUOUS at `canonicalRelativeRmmInteriorComponentStore` "because
the interior tables are single-chunk".  They are not.  Evaluating
`(size, wordSize, relativeWidth, chunkCount)` gives

    (1, 2, 5, 3)   (2, 3, 7, 3)   (4, 4, 7, 2)   (8, 5, 9, 2)
    (16, 6, 9, 2)  (64, 8, 9, 2)  (256, 10, 11, 2)
    (1024, 12, 11, 1)  (4096, 14, 11, 1)  (65536, 18, 13, 1)

so every `shape.size` below roughly `1024` is MULTI-chunk and `hexact` is
a LIVE obligation at exactly the small shapes an all-size claim must
cover.  This module discharges it SUBSTANTIVELY, from
`chunkPayloadWords`'s own structure, and cites no vacuity.

## The proof obligation, and why it is true

`fixedWidthNatTableMachineWords` (`MachineChunkedTable.lean:15`) is a bare
`flatMap (chunkPayloadWords wordSize)` over the table's cells, with NO
padding.  `chunkPayloadWords` emits chunks of length exactly `wordSize`
except possibly the last, which is why `hle` is unconditional and `hexact`
needs the `j + 1 < n` guard.

The per-index presentation that makes this provable is
`chunkPayloadWords_get?_eq_take_drop` (`WordStore.lean:274`): the chunk at
index `j` is `(payload.drop (j * wordSize)).take wordSize`.  Its length is
therefore `min wordSize (payload.length - j * wordSize)`, which equals
`wordSize` exactly when `(j + 1) * wordSize <= payload.length`.

RECORDED BECAUSE A RESUME NOTE CLAIMED OTHERWISE: that lemma DOES exist,
at exactly `WordStore.lean:274`, and four modules already cite it
(`GenericSelect/DenseWord.lean:38`,
`RankSelectCompressed/Base/ClassLengthEnvelope.lean:2679`,
`RankSelectCompressed/Base/LogChunks.lean:681`,
`RankSelectCompressedSubLogDenseWord.lean:222`).  Nothing needed to be
invented here; the arithmetic below is all that was missing.
-/

open RMQ.SuccinctSpace

namespace RMQ
namespace WordRAM
namespace E1InteriorChunkExact

open RMQ.SuccinctSpace
open RMQ.WordRAM.E1InteriorChunkFold

/-- A chunk index with a chunk above it is a FULL word's worth of payload.

This is the whole arithmetic content of non-final-chunk exactness.  Both
arms of the `width % wordSize` split give `j + 1 <= width / wordSize`,
after which `Nat.div_mul_le_self` finishes.  Stated separately because it
is the step a reviewer would otherwise re-derive. -/
theorem succ_mul_le_of_succ_lt_chunkCount
    {width wordSize j : Nat}
    (hj : j + 1 < fixedWidthNatTableMachineChunkCount width wordSize) :
    (j + 1) * wordSize ≤ width := by
  unfold fixedWidthNatTableMachineChunkCount at hj
  have hle : j + 1 ≤ width / wordSize := by
    by_cases h : width % wordSize = 0
    · simp [h] at hj
      omega
    · simp [h] at hj
      omega
  calc (j + 1) * wordSize ≤ (width / wordSize) * wordSize :=
        Nat.mul_le_mul_right _ hle
    _ ≤ width := Nat.div_mul_le_self width wordSize

/-- NON-FINAL-CHUNK EXACTNESS at the machine-chunked store.

The machine word at flat index `i * count + j`, for a cell index `i` that
the table actually holds and a chunk index `j` with another chunk above
it, has length exactly `wordSize`.

The `j + 1 < count` guard is load-bearing and cannot be dropped: at
`j + 1 = count` with `width % wordSize ≠ 0` the final chunk is strictly
shorter, so the unguarded statement is FALSE at most interior tables. -/
theorem machineWords_length_eq_of_succ_lt_chunkCount
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    {i j : Nat} {cell chunk : List Bool}
    (hcell : table.store.words.toList[i]? = some cell)
    (hj : j + 1 < fixedWidthNatTableMachineChunkCount width wordSize)
    (hchunk :
      (fixedWidthNatTableMachineWords table wordSize)[
        i * fixedWidthNatTableMachineChunkCount width wordSize + j]? =
        some chunk) :
    chunk.length = wordSize := by
  have hslice := table.machineWords_cell_slice hwordSize hcell
  simp only at hslice
  -- the chunk list of cell `i`, indexed at `j`
  have hget : (chunkPayloadWords wordSize cell)[j]? = some chunk := by
    rw [← hslice]
    rw [List.getElem?_take_of_lt (by omega), List.getElem?_drop]
    exact hchunk
  -- per-index exactness of `chunkPayloadWords`
  have heq := chunkPayloadWords_get?_eq_take_drop hget
  have hcellLen : cell.length = width :=
    table.word_length_of_get? (by simpa [Array.getElem?_toList] using hcell)
  have hmul : (j + 1) * wordSize ≤ width :=
    succ_mul_le_of_succ_lt_chunkCount hj
  have hdrop : (cell.drop (j * wordSize)).length = width - j * wordSize := by
    rw [List.length_drop, hcellLen]
  rw [heq, List.length_take, hdrop]
  have : (j + 1) * wordSize = j * wordSize + wordSize := by
    rw [Nat.succ_mul]
  omega

/-- Every stored cell chunks into exactly `chunkCount` machine words.

Extracted from `machineWords_cell_slice`'s own proof, which establishes it
inline; it is needed separately below to bound the flat chunk index. -/
theorem chunkPayloadWords_length_eq_chunkCount_of_mem
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    {logical : List Bool} (hmem : logical ∈ table.store.words.toList) :
    (chunkPayloadWords wordSize logical).length =
      fixedWidthNatTableMachineChunkCount width wordSize := by
  have hlen : logical.length = width := by
    rcases List.mem_iff_getElem?.mp hmem with ⟨j, hlogical⟩
    exact table.word_length_of_get? (by
      simpa [Array.getElem?_toList] using hlogical)
  simpa [fixedWidthNatTableMachineChunkCount, hlen] using
    chunkPayloadWords_length_eq_div_add_indicator hwordSize logical

/-- THE FLAT CHUNK INDEX IS IN RANGE.

For a cell index `i` the table holds and a chunk index `j` below the chunk
count, the flat index `i * count + j` is a genuine index into the table's
machine word list.

This is what lets the agreement premise below be stated in BOUNDED form.
It is not a convenience: the unbounded form is FALSE at the interior store
(see `E1InteriorChunkStore.lean`), so the bound is what makes the premise
dischargeable at all. -/
theorem machineWords_index_lt
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    {i j : Nat} {cell : List Bool}
    (hcell : table.store.words.toList[i]? = some cell)
    (hj : j < fixedWidthNatTableMachineChunkCount width wordSize) :
    i * fixedWidthNatTableMachineChunkCount width wordSize + j <
      (fixedWidthNatTableMachineWords table wordSize).length := by
  have h := List.mul_add_le_flatMap_length_of_constant_length
    table.store.words.toList (chunkPayloadWords wordSize)
    (fixedWidthNatTableMachineChunkCount width wordSize)
    (fun x hx => chunkPayloadWords_length_eq_chunkCount_of_mem table hwordSize hx)
    hcell
  unfold fixedWidthNatTableMachineWords
  omega

/-- A cell index the table's entry list allows is backed by a stored word.

DERIVED, not assumed.  `read_exact` maps the stored word through
`bitsToNatLE` onto `entries[i]?`; if the entry is `some`, the word cannot
be `none`.  Stated so the corollary below carries no unchecked existential
premise -- an unproved premise and an unsatisfiable one look identical at
the definition site. -/
theorem cell_exists_of_lt
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) {i : Nat}
    (hi : i < entries.length) :
    ∃ cell, table.store.words.toList[i]? = some cell := by
  have h := table.read_exact i
  cases hw : table.store.words[i]? with
  | none =>
      rw [hw] at h
      simp only [Option.map_none] at h
      have hentry : entries[i]? = none := h.symm
      rw [List.getElem?_eq_none_iff] at hentry
      omega
  | some cell =>
      exact ⟨cell, by simpa [Array.getElem?_toList] using hw⟩

/-- THE `hexact` PREMISE OF THE VALUE BRIDGE, in the form the bridge states
it, for a `ReadStore` segment that holds the table's machine words.

The agreement hypothesis `hagree` is the segment-to-table mapping and is
deliberately left as a parameter: it is fixed by the interior composition
(the summary group's segment assignment), not by this module.  It is
discharged AT `canonicalRelativeRmmInteriorComponentStore` in
`E1InteriorChunkStore.lean`.

`hagree` IS BOUNDED, AND THE BOUND IS LOAD-BEARING.  It agrees only at
addresses the table's own machine word list actually indexes.  The
unbounded form -- `∀ a`, which this corollary carried until M3d-17 -- is
FALSE at the interior store, and not marginally: that store is the
CONCATENATION of eight tables' word lists, so past the end of any one
table the store still answers `some` (the next table's word) while
`(machineWords table)[a]?` is `none`.  Evaluated at `chainShape 1` the
baseline table contributes `2` words to a `31`-word store, so the
unbounded form fails first at `a = 2`.  Only the bounded form is
derivable there, and it is all the proof below ever uses -- at the single
index `i * chunkCount + j`, which `machineWords_index_lt` places in
range.

Everything else discharges.  Note the guard travels correctly: the bridge
guards on `j + 1 < chunkIters`, and on the valid arm with the cap in hand
`chunkIters` IS the machine chunk count, so the bridge's guard is exactly
the guard `machineWords_length_eq_of_succ_lt_chunkCount` needs. -/
theorem hexact_of_segment_agrees
    {entries : List Nat} {width wordSize : Nat}
    (table : FixedWidthNatTable entries width) (hwordSize : 0 < wordSize)
    (store : ReadStore)
    {segment base deadAddress entriesLen chunkCount i : Nat}
    (hcount : chunkCount = fixedWidthNatTableMachineChunkCount width wordSize)
    (hvalid : i < entriesLen)
    (hentries : i < entries.length)
    (hagree : ∀ a, a < (fixedWidthNatTableMachineWords table wordSize).length →
      store.readWord? segment (base + a) =
        (fixedWidthNatTableMachineWords table wordSize)[a]?) :
    ∀ j, j + 1 < chunkIters entriesLen chunkCount i → ∀ w,
      store.readWord? segment
          (chunkStart base deadAddress entriesLen chunkCount i + j) =
          some w →
        w.length = wordSize := by
  intro j hj w hw
  rcases cell_exists_of_lt table hentries with ⟨cell, hcell⟩
  rw [chunkIters, if_pos hvalid] at hj
  rw [chunkStart, if_pos hvalid] at hw
  have hjlt : j + 1 < fixedWidthNatTableMachineChunkCount width wordSize := by
    have : j + 1 < chunkCount := Nat.lt_of_lt_of_le hj (Nat.min_le_left _ _)
    omega
  refine machineWords_length_eq_of_succ_lt_chunkCount table hwordSize
    hcell hjlt ?_
  have haddr : base + i * chunkCount + j = base + (i * chunkCount + j) := by
    omega
  rw [haddr] at hw
  have hrange :
      i * chunkCount + j <
        (fixedWidthNatTableMachineWords table wordSize).length := by
    rw [hcount]
    exact machineWords_index_lt table hwordSize hcell (by omega)
  rw [hagree (i * chunkCount + j) hrange] at hw
  rw [← hcount]
  exact hw

/-! ## Anti-vacuity: the guard is load-bearing, checked by execution

The campaign rule this module was written under: where a quantity is
computable, EVALUATE it rather than reason about it.  That is what caught
the false single-chunk claim, so it is applied here to this module's OWN
statement rather than only to its inputs.

The fixture is the `shape.size = 1` interior row from the evaluation
recorded in the header -- `wordSize = 2`, `relativeWidth = 5`,
`chunkCount = 3` -- i.e. a REACHABLE shape, and the most multi-chunk one.
-/

/-- The fixture's chunk count agrees with the evaluated interior row. -/
theorem exactFixture_chunkCount : fixedWidthNatTableMachineChunkCount 5 2 = 3 := by
  decide

/-- A five-bit cell, the width the `size = 1` shape's relative table uses. -/
def exactFixtureCell : List Bool := [true, false, true, true, false]

theorem exactFixture_chunks :
    chunkPayloadWords 2 exactFixtureCell =
      [[true, false], [true, true], [false]] := by
  decide

/-- THE NON-FINAL CHUNKS ARE EXACTLY `wordSize` WIDE -- the conclusion of
`machineWords_length_eq_of_succ_lt_chunkCount`, exhibited on a reachable
shape rather than only proved in the abstract. -/
theorem exactFixture_nonfinal_lengths :
    (chunkPayloadWords 2 exactFixtureCell)[0]?.map List.length = some 2 ∧
      (chunkPayloadWords 2 exactFixtureCell)[1]?.map List.length = some 2 := by
  decide

/-- THE GUARD IS LOAD-BEARING, NOT DECORATIVE.  The FINAL chunk is
strictly shorter than `wordSize`, so dropping `j + 1 < n` from the premise
does not weaken the statement -- it makes it FALSE at this shape.  This is
the check that distinguishes a real cut from a hypothesis carried for
appearance. -/
theorem exactFixture_final_length_lt :
    (chunkPayloadWords 2 exactFixtureCell)[2]?.map List.length = some 1 := by
  decide

/-- The `hagree` premise of `hexact_of_segment_agrees` is SATISFIABLE.

A premise stated as a visible debt owes a witness that it can be met at
the intended instantiation; unproved and unsatisfiable look identical at
the definition site.  The segment-restricted store below meets it at
`base = 0` for any table, so nothing composed on that corollary rests on
an unmeetable hypothesis. -/
def segmentStore
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (wordSize segment : Nat) :
    ReadStore where
  readWord? := fun s i =>
    if s = segment then (fixedWidthNatTableMachineWords table wordSize)[i]?
    else none

theorem segmentStore_agrees
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (wordSize segment : Nat) :
    ∀ a, (segmentStore table wordSize segment).readWord? segment (0 + a) =
      (fixedWidthNatTableMachineWords table wordSize)[a]? := by
  intro a
  simp [segmentStore]

end E1InteriorChunkExact
end WordRAM
end RMQ
