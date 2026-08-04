import RMQ.Core.SuccinctFinal.RAM.PackedCellProbe.Probe

/-!
# Per-source word geometry

`FG-08` asks that every logical read lower to physical cell probes. A logical
read of the flat payload store is `(segment, index)`, and the store answers it
with `(sourceWords shape source)[index]?` -- one entry of an `Array (List Bool)`.
To answer the same read by probing `packedMemory`, a controller must know two
things about that array from `n` and the decoded long count alone: how many words
it has, and where word `index` sits inside the source's payload.

This module supplies both. It first proves the two generic shapes the word arrays
come in:

* a fixed-width table, whose words all have the table's field width; and
* a chunked bit source, whose words are full strides except for a short last one.

Both are then expressed by the *same* function, `packedWordSlice`, so that the
per-source theorems below all have one statement shape and the store built on top
of them needs one arm per source rather than one arm per representation.

Nothing here mentions `CartesianShape` on the packed side: the counts and widths
are the size-only mirrors of `SourceFactorization`, and the theorems say the
shape-indexed word array agrees with them.
-/

namespace RMQ

namespace SuccinctFinal

namespace PackedCellProbe

open Cartesian
open SuccinctSpace

/-! ## The common word shape

Both representations answer index `i` the same way: `none` past the word count,
and otherwise the `width`-bit slice of the source payload starting at `i * width`.
`List.take` truncates, so a chunked source's short final word needs no separate
arm -- it is the slice that runs out of payload.
-/

/-- Word `i` of a source with `count` words of stride `width` over `payload`. -/
def packedWordSlice (payload : List Bool) (count width i : Nat) :
    Option (List Bool) :=
  if i < count then some ((payload.drop (i * width)).take width) else none

theorem packedWordSlice_of_lt
    {payload : List Bool} {count width i : Nat} (hi : i < count) :
    packedWordSlice payload count width i =
      some ((payload.drop (i * width)).take width) := by
  simp [packedWordSlice, hi]

theorem packedWordSlice_of_le
    {payload : List Bool} {count width i : Nat} (hi : count <= i) :
    packedWordSlice payload count width i = none := by
  simp [packedWordSlice, Nat.not_lt.mpr hi]

/-! ## Uniform words -/

/--
A list of equal-length words is indexed by slicing its own concatenation.

This is the fact that makes a fixed-width table probeable: the payload alone,
plus the width, determines every stored word.
-/
theorem packedUniformWords_getElem?
    {width : Nat} :
    forall {words : List (List Bool)},
      (forall {word : List Bool}, List.Mem word words -> word.length = width) ->
      forall i : Nat,
        words[i]? =
          packedWordSlice (flattenPayloadWords words) words.length width i := by
  intro words
  induction words with
  | nil =>
      intro _ i
      simp [packedWordSlice]
  | cons word rest ih =>
      intro hwidth i
      have hword : word.length = width := hwidth List.mem_cons_self
      have hrest :
          forall {w : List Bool}, List.Mem w rest -> w.length = width := by
        intro w hmem
        exact hwidth (List.mem_cons_of_mem word hmem)
      cases i with
      | zero =>
          simp [flattenPayloadWords, packedWordSlice, ← hword]
      | succ j =>
          have hsplit : (j + 1) * width = word.length + j * width := by
            rw [hword, Nat.succ_mul]
            exact Nat.add_comm _ _
          have hdrop :
              (word ++ flattenPayloadWords rest).drop ((j + 1) * width) =
                (flattenPayloadWords rest).drop (j * width) := by
            rw [hsplit, ← List.drop_drop]
            simp
          simp only [flattenPayloadWords, List.getElem?_cons_succ,
            List.length_cons, packedWordSlice, hdrop]
          rw [ih hrest j]
          by_cases hj : j < rest.length
          · simp [packedWordSlice, hj, Nat.succ_lt_succ_iff]
          · simp [packedWordSlice, hj, Nat.succ_lt_succ_iff]

/-! ## Fixed-width tables

`FixedWidthNatTable` carries three fields that between them pin the whole word
array: every stored word has the field width, the words concatenate to the
payload, and decoding word `i` gives `entries[i]?`. The last one is what fixes the
*count* without any positivity assumption on the width -- a zero-width table (the
inactive close summary is one) still has exactly `entries.length` empty words, and
`flattenPayloadWords` cannot see them.
-/

theorem packedFixedWidthTable_isSome
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    (table.store.words[i]?).isSome = (entries[i]?).isSome := by
  have hread := table.read_exact i
  rw [← hread]
  cases table.store.words[i]? with
  | none => rfl
  | some _ => rfl

theorem packedFixedWidthTable_words_length
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) :
    table.store.words.toList.length = entries.length := by
  have hkey :
      forall i : Nat,
        (i < table.store.words.toList.length) = (i < entries.length) := by
    intro i
    have h := packedFixedWidthTable_isSome table i
    have hleft :
        (table.store.words[i]?).isSome =
          decide (i < table.store.words.toList.length) := by
      rw [← Array.getElem?_toList]
      cases hlt : decide (i < table.store.words.toList.length) with
      | true =>
          have : i < table.store.words.toList.length := by
            simpa using hlt
          rw [List.getElem?_eq_getElem this]
          rfl
      | false =>
          have : table.store.words.toList.length <= i := by
            simpa using hlt
          rw [List.getElem?_eq_none this]
          rfl
    have hright :
        (entries[i]?).isSome = decide (i < entries.length) := by
      cases hlt : decide (i < entries.length) with
      | true =>
          have : i < entries.length := by simpa using hlt
          rw [List.getElem?_eq_getElem this]
          rfl
      | false =>
          have : entries.length <= i := by simpa using hlt
          rw [List.getElem?_eq_none this]
          rfl
    have := hleft.symm.trans (h.trans hright)
    simpa using congrArg (fun b => b = true) this
  have h1 := hkey table.store.words.toList.length
  have h2 := hkey entries.length
  simp only [Nat.lt_irrefl, eq_iff_iff, false_iff, iff_false, Nat.not_lt] at h1 h2
  omega

/--
**Every fixed-width table word is a payload slice.** No hypothesis: the count is
the entry count and the stride is the field width, for every such table.
-/
theorem packedFixedWidthTable_getElem?
    {entries : List Nat} {width : Nat}
    (table : FixedWidthNatTable entries width) (i : Nat) :
    table.store.words[i]? =
      packedWordSlice table.payload entries.length width i := by
  have huniform :
      forall {word : List Bool},
        List.Mem word table.store.words.toList -> word.length = width := by
    intro word hmem
    rcases List.getElem?_of_mem hmem with ⟨j, hj⟩
    exact table.word_length_of_get? (by simpa [Array.getElem?_toList] using hj)
  have hslice := packedUniformWords_getElem? huniform i
  rw [← Array.getElem?_toList, hslice, table.store.erases,
    packedFixedWidthTable_words_length table]

/-! ## Chunked bit sources

A chunked source's stride and its read width differ: `chunkPayloadWords` leaves a
short final word, and a probe issued at the full stride would decode foreign bits
from the next component rather than truncating. `packedWordSlice` takes that
truncation from `List.take`, so the same statement covers both kinds of word.
-/

/-- The number of words a chunked bit source stores. -/
def packedChunkCount (length width : Nat) : Nat :=
  length / width + (if length % width = 0 then 0 else 1)

theorem packedChunkedWords_getElem?
    {width : Nat} (hwidth : 0 < width) (payload : List Bool) (i : Nat) :
    (chunkPayloadWords width payload)[i]? =
      packedWordSlice payload (packedChunkCount payload.length width) width i := by
  have hcount :
      (chunkPayloadWords width payload).length =
        packedChunkCount payload.length width :=
    chunkPayloadWords_length_eq_div_add_indicator hwidth payload
  have hmono : forall a b : Nat, a <= b -> a * width <= b * width := by
    intro a b hab
    exact Nat.mul_le_mul_right width hab
  have hq :
      payload.length / width * width + payload.length % width =
        payload.length := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod payload.length width
  have hrlt : payload.length % width < width := Nat.mod_lt _ hwidth
  have hsuccq :
      (payload.length / width + 1) * width =
        payload.length / width * width + width :=
    Nat.succ_mul _ _
  have hiff : i < packedChunkCount payload.length width <->
      i * width < payload.length := by
    constructor
    · intro hi
      by_cases hr : payload.length % width = 0
      · have hcnt :
            packedChunkCount payload.length width = payload.length / width := by
          simp [packedChunkCount, hr]
        have hile : i + 1 <= payload.length / width := by
          rw [hcnt] at hi
          omega
        have hmul := hmono (i + 1) (payload.length / width) hile
        have hs : (i + 1) * width = i * width + width := Nat.succ_mul _ _
        omega
      · have hile : i <= payload.length / width := by
          simp only [packedChunkCount, if_neg hr] at hi
          omega
        have hmul := hmono i (payload.length / width) hile
        omega
    · intro hi
      by_cases hr : payload.length % width = 0
      · have hcnt :
            packedChunkCount payload.length width = payload.length / width := by
          simp [packedChunkCount, hr]
        rw [hcnt]
        by_cases hlt : i < payload.length / width
        · exact hlt
        · exfalso
          have hmul := hmono (payload.length / width) i (Nat.le_of_not_lt hlt)
          omega
      · simp only [packedChunkCount, if_neg hr]
        by_cases hlt : i < payload.length / width + 1
        · exact hlt
        · exfalso
          have hge : payload.length / width + 1 <= i := by omega
          have hmul := hmono (payload.length / width + 1) i hge
          omega
  by_cases hi : i < packedChunkCount payload.length width
  · have hmul : i * width < payload.length := hiff.mp hi
    rcases chunkPayloadWords_get?_some_of_mul_lt hwidth hmul with ⟨word, hword⟩
    rw [hword, packedWordSlice_of_lt hi,
      chunkPayloadWords_get?_eq_take_drop hword]
  · have hmul : payload.length <= i * width := by
      by_cases h : i * width < payload.length
      · exact absurd (hiff.mpr h) hi
      · omega
    rw [chunkPayloadWords_get?_none_of_length_le_mul hmul,
      packedWordSlice_of_le (by omega)]

/-- Past the last chunk, the stride has already covered the whole payload. -/
theorem packedChunkCount_mul_le
    {width : Nat} (hwidth : 0 < width) (len i : Nat)
    (hi : packedChunkCount len width <= i) : len <= i * width := by
  have hmono : forall a b : Nat, a <= b -> a * width <= b * width := by
    intro a b hab
    exact Nat.mul_le_mul_right width hab
  have hq : len / width * width + len % width = len := by
    rw [Nat.mul_comm]
    exact Nat.div_add_mod len width
  have hrlt : len % width < width := Nat.mod_lt _ hwidth
  by_cases hr : len % width = 0
  · have hcnt : packedChunkCount len width = len / width := by
      simp [packedChunkCount, hr]
    have hmul := hmono (len / width) i (by omega)
    omega
  · have hcnt : packedChunkCount len width = len / width + 1 := by
      simp only [packedChunkCount, if_neg hr]
    have hmul := hmono (len / width + 1) i (by omega)
    have hsucc : (len / width + 1) * width = len / width * width + width :=
      Nat.succ_mul _ _
    omega

/--
The sentinel padding a chunked rank store appends is already the right answer.

`ofChunksWithSentinel` follows the real chunks with `payload.length + 1` empty
words, and past the last chunk the payload slice is empty for exactly the reason
the sentinel is: the stride has run off the end. So one statement covers the
padded array too, with a larger count and the same slice.
-/
theorem packedChunkedSentinelWords_getElem?
    {width : Nat} (hwidth : 0 < width) (payload : List Bool) (i : Nat) :
    (chunkPayloadWords width payload ++
      List.replicate (payload.length + 1) [])[i]? =
      packedWordSlice payload
        (packedChunkCount payload.length width + (payload.length + 1)) width i := by
  have hchunks :
      (chunkPayloadWords width payload).length =
        packedChunkCount payload.length width :=
    chunkPayloadWords_length_eq_div_add_indicator hwidth payload
  by_cases hi : i < packedChunkCount payload.length width
  · rw [List.getElem?_append_left (by omega),
      packedChunkedWords_getElem? hwidth payload i,
      packedWordSlice_of_lt hi, packedWordSlice_of_lt (by omega)]
  · have hge : packedChunkCount payload.length width <= i := by omega
    have hcov : payload.length <= i * width :=
      packedChunkCount_mul_le hwidth payload.length i hge
    have hempty : (payload.drop (i * width)).take width = [] := by
      rw [List.drop_eq_nil_of_le hcov]
      simp
    rw [List.getElem?_append_right (by omega), List.getElem?_replicate]
    by_cases hsent : i - (chunkPayloadWords width payload).length <
        payload.length + 1
    · rw [if_pos hsent, packedWordSlice_of_lt (by omega), hempty]
    · rw [if_neg hsent, packedWordSlice_of_le (by omega)]

/-! ## The dense select entry tables

Eight sources, two tables, one statement each. The count is the slot count and the
stride is the field width, both already size-only in `SourceFactorization`.
-/

theorem packedSelectSuperBaseOccurrenceWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSuperBaseOccurrence)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSuperBaseOccurrence)
        (packedSuperSlots shape.size) (packedSuperWidth shape.size) i := by
  show
    (GenericSelect.superTable shape.bpCode
      false).baseOccurrenceTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    List.length_map, GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]
  rfl

theorem packedSelectSuperBaseWordIndexWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSuperBaseWordIndex)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSuperBaseWordIndex)
        (packedSuperSlots shape.size) (packedSuperWidth shape.size) i := by
  show
    (GenericSelect.superTable shape.bpCode
      false).baseWordIndexTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices,
    List.length_map, GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]
  rfl

theorem packedSelectSuperRankBeforeWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSuperRankBefore)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSuperRankBefore)
        (packedSuperSlots shape.size) (packedSuperWidth shape.size) i := by
  show
    (GenericSelect.superTable shape.bpCode
      false).rankBeforeTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore,
    List.length_map, GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]
  rfl

theorem packedSelectSuperFirstOffsetWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSuperFirstOffset)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSuperFirstOffset)
        (packedSuperSlots shape.size) (packedSuperWidth shape.size) i := by
  show
    (GenericSelect.superTable shape.bpCode
      false).firstOffsetTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    List.length_map, GenericSelect.superEntries_length, superSlotCount_eq_packed,
    superFieldWidth_eq_packed]
  rfl

theorem packedSelectLocalBaseOccurrenceWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLocalBaseOccurrence)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalBaseOccurrence)
        (packedLocalSlots shape.size) (packedLocalWidth shape.size) i := by
  show
    (GenericSelect.localTable shape.bpCode
      false).baseOccurrenceTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.baseOccurrences,
    List.length_map, GenericSelect.localEntries_length, localSlotCount_eq_packed,
    localFieldWidth_eq_packed]
  rfl

theorem packedSelectLocalBaseWordIndexWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLocalBaseWordIndex)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalBaseWordIndex)
        (packedLocalSlots shape.size) (packedLocalWidth shape.size) i := by
  show
    (GenericSelect.localTable shape.bpCode
      false).baseWordIndexTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.baseWordIndices,
    List.length_map, GenericSelect.localEntries_length, localSlotCount_eq_packed,
    localFieldWidth_eq_packed]
  rfl

theorem packedSelectLocalRankBeforeWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLocalRankBefore)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalRankBefore)
        (packedLocalSlots shape.size) (packedLocalWidth shape.size) i := by
  show
    (GenericSelect.localTable shape.bpCode
      false).rankBeforeTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.ranksBefore,
    List.length_map, GenericSelect.localEntries_length, localSlotCount_eq_packed,
    localFieldWidth_eq_packed]
  rfl

theorem packedSelectLocalFirstOffsetWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLocalFirstOffset)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLocalFirstOffset)
        (packedLocalSlots shape.size) (packedLocalWidth shape.size) i := by
  show
    (GenericSelect.localTable shape.bpCode
      false).firstOffsetTable.store.words[i]? = _
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.SparseDenseSelectDenseLocalEntry.firstOffsets,
    List.length_map, GenericSelect.localEntries_length, localSlotCount_eq_packed,
    localFieldWidth_eq_packed]
  rfl

/-! ## The chunked bit sources

Four sources store bits rather than fields. The BP code is chunked bare; the three
rank-directory bit stores are chunked with the sentinel padding their word-present
obligation needs. `finalRankBPCodeAlias` is the second kind over the same bits as
the first, which is exactly why it is a separate source.
-/

theorem packedBpCodeWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape .bpCode)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape .bpCode)
        (packedChunkCount (2 * shape.size) (packedBpCodeWordWidth shape.size))
        (packedBpCodeWordWidth shape.size) i := by
  have hlen := CartesianShape.bpCode_length shape
  have hwidth := packedBpCodeWordWidth_pos shape.size
  have hw :
      SuccinctRank.machineWordBits shape.bpCode.length =
        packedBpCodeWordWidth shape.size := by
    rw [hlen]
    rfl
  show
    ((chunkPayloadWords (SuccinctRank.machineWordBits shape.bpCode.length)
      shape.bpCode).toArray)[i]? = _
  rw [List.getElem?_toArray, hw,
    packedChunkedWords_getElem? hwidth shape.bpCode i, hlen]
  rfl

theorem packedFinalRankBPCodeAliasWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .finalRankBPCodeAlias)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .finalRankBPCodeAlias)
        (packedChunkCount (2 * shape.size) (packedRankWordSize shape.size) +
          (2 * shape.size + 1))
        (packedRankWordSize shape.size) i := by
  have hlen := CartesianShape.bpCode_length shape
  have hwidth :
      0 < builtRelativeSplitBPCloseRankWordSize shape :=
    builtRelativeSplitBPCloseRankWordSize_pos shape
  have hw :
      builtRelativeSplitBPCloseRankWordSize shape =
        packedRankWordSize shape.size :=
    rankWordSize_eq_packed shape
  show
    ((chunkPayloadWords (builtRelativeSplitBPCloseRankWordSize shape)
        shape.bpCode ++
      List.replicate (shape.bpCode.length + 1) []).toArray)[i]? = _
  rw [List.getElem?_toArray,
    packedChunkedSentinelWords_getElem? hwidth shape.bpCode i, hw, hlen]
  rfl

theorem packedSelectLongFlagBitsWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLongFlagBits)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongFlagBits)
        (packedChunkCount (packedSuperSlots shape.size)
            (packedLongFlagWordSize shape.size) +
          (packedSuperSlots shape.size + 1))
        (packedLongFlagWordSize shape.size) i := by
  have hlen := longFlagBits_length_eq_packed shape
  have hwidth :
      0 < GenericSelect.longFlagRankWordSize shape.bpCode false :=
    GenericSelect.longFlagRankWordSize_pos shape.bpCode false
  have hw :
      GenericSelect.longFlagRankWordSize shape.bpCode false =
        packedLongFlagWordSize shape.size :=
    longFlagRankWordSize_eq_packed shape
  show
    ((chunkPayloadWords (GenericSelect.longFlagRankWordSize shape.bpCode false)
        (GenericSelect.longSuperFlagBits shape.bpCode false) ++
      List.replicate
        ((GenericSelect.longSuperFlagBits shape.bpCode false).length + 1)
        []).toArray)[i]? = _
  rw [List.getElem?_toArray,
    packedChunkedSentinelWords_getElem? hwidth
      (GenericSelect.longSuperFlagBits shape.bpCode false) i,
    hw, hlen]
  rfl

theorem packedSelectSparseFlagBitsWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSparseFlagBits)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseFlagBits)
        (packedChunkCount (packedSparseSlots shape.size)
            (packedSparseWordSize shape.size) +
          (packedSparseSlots shape.size + 1))
        (packedSparseWordSize shape.size) i := by
  have hlen := sparseFlagBits_length_eq_packed shape
  have hwidth :
      0 < GenericSelect.sparseExceptionEffectiveFlagRankWordSize
        shape.bpCode false :=
    GenericSelect.sparseExceptionEffectiveFlagRankWordSize_pos shape.bpCode false
  have hw :
      GenericSelect.sparseExceptionEffectiveFlagRankWordSize shape.bpCode false =
        packedSparseWordSize shape.size :=
    sparseFlagRankWordSize_eq_packed shape
  show
    ((chunkPayloadWords
        (GenericSelect.sparseExceptionEffectiveFlagRankWordSize
          shape.bpCode false)
        (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false) ++
      List.replicate
        ((GenericSelect.sparseExceptionEffectiveFlagBits
          shape.bpCode false).length + 1)
        []).toArray)[i]? = _
  rw [List.getElem?_toArray,
    packedChunkedSentinelWords_getElem? hwidth
      (GenericSelect.sparseExceptionEffectiveFlagBits shape.bpCode false) i,
    hw, hlen]
  rfl

/-! ## Rank-sample columns

Four two-level rank directories contribute one sampled column each to the flat
payload. Their slot counts are the canonical entry counts, which the existing
overhead mirrors already carry in factored form.
-/

/-- Slots in one polarity of the final rank superblock samples. -/
def packedRankSuperSlots (n : Nat) : Nat :=
  2 * n / packedRankWordSize n / packedRankWordSize n + 1

/-- Slots in one polarity of the final rank block samples. -/
def packedRankBlockSlots (n : Nat) : Nat :=
  2 * n / packedRankWordSize n + 1

/-- Slots in one polarity of the long-flag rank samples, at either level. -/
def packedLongFlagRankSlots (n : Nat) : Nat :=
  packedSuperSlots n / packedLongFlagWordSize n + 1

/-- Slots in one polarity of the sparse-flag rank samples, at either level. -/
def packedSparseRankSlots (n : Nat) : Nat :=
  packedSparseSlots n / packedSparseWordSize n + 1

theorem packedFinalRankSuperFalseWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .finalRankSuperFalse)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .finalRankSuperFalse)
        (packedRankSuperSlots shape.size) (packedRankWordSize shape.size) i := by
  show
    (builtRelativeSplitBPCloseRankData shape).superTables.falseTable.store.words[i]?
      =
      packedWordSlice
        (builtRelativeSplitBPCloseRankData shape).superTables.falseTable.payload
        (packedRankSuperSlots shape.size) (packedRankWordSize shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [builtRelativeSplitBPCloseRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    packedRankSuperSlots, CartesianShape.bpCode_length, rankWordSize_eq_packed,
    builtRelativeSplitBPCloseRankBlocksPerSuper]

theorem packedFinalRankBlockFalseWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .finalRankBlockFalse)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .finalRankBlockFalse)
        (packedRankBlockSlots shape.size) (packedRankBlockWidth shape.size) i := by
  show
    (builtRelativeSplitBPCloseRankData shape).blockTables.falseTable.store.words[i]?
      =
      packedWordSlice
        (builtRelativeSplitBPCloseRankData shape).blockTables.falseTable.payload
        (packedRankBlockSlots shape.size) (packedRankBlockWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [builtRelativeSplitBPCloseRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    packedRankBlockSlots, CartesianShape.bpCode_length, rankWordSize_eq_packed,
    rankBlockWidth_eq_packed]

theorem packedSelectLongFlagRankSuperTrueWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLongFlagRankSuperTrue)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongFlagRankSuperTrue)
        (packedLongFlagRankSlots shape.size)
        (packedLongFlagWordSize shape.size) i := by
  show
    (GenericSelect.longFlagRankData shape.bpCode
      false).superTables.trueTable.store.words[i]? =
      packedWordSlice
        (GenericSelect.longFlagRankData shape.bpCode
          false).superTables.trueTable.payload
        (packedLongFlagRankSlots shape.size)
        (packedLongFlagWordSize shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.longFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    GenericSelect.longFlagRankBlocksPerSuper, Nat.div_one,
    packedLongFlagRankSlots, longFlagBits_length_eq_packed,
    longFlagRankWordSize_eq_packed]

theorem packedSelectLongFlagRankBlockTrueWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLongFlagRankBlockTrue)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongFlagRankBlockTrue)
        (packedLongFlagRankSlots shape.size)
        (packedLongFlagWordSize shape.size) i := by
  show
    (GenericSelect.longFlagRankData shape.bpCode
      false).blockTables.trueTable.store.words[i]? =
      packedWordSlice
        (GenericSelect.longFlagRankData shape.bpCode
          false).blockTables.trueTable.payload
        (packedLongFlagRankSlots shape.size)
        (packedLongFlagWordSize shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.longFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    GenericSelect.longFlagRankBlockWidth, packedLongFlagRankSlots,
    longFlagBits_length_eq_packed, longFlagRankWordSize_eq_packed]

theorem packedSelectSparseRankSuperTrueWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSparseRankSuperTrue)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseRankSuperTrue)
        (packedSparseRankSlots shape.size)
        (packedSparseWordSize shape.size) i := by
  show
    (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
      false).superTables.trueTable.store.words[i]? =
      packedWordSlice
        (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
          false).superTables.trueTable.payload
        (packedSparseRankSlots shape.size)
        (packedSparseWordSize shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalSuperRankSampleTables,
    SuccinctRank.canonicalSuperRankEntries_length,
    GenericSelect.sparseExceptionEffectiveFlagRankBlocksPerSuper, Nat.div_one,
    packedSparseRankSlots, sparseFlagBits_length_eq_packed,
    sparseFlagRankWordSize_eq_packed]

theorem packedSelectSparseRankBlockTrueWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSparseRankBlockTrue)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseRankBlockTrue)
        (packedSparseRankSlots shape.size)
        (packedSparseWordSize shape.size) i := by
  show
    (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
      false).blockTables.trueTable.store.words[i]? =
      packedWordSlice
        (GenericSelect.sparseExceptionEffectiveFlagRankData shape.bpCode
          false).blockTables.trueTable.payload
        (packedSparseRankSlots shape.size)
        (packedSparseWordSize shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.sparseExceptionEffectiveFlagRankData,
    SuccinctRank.canonicalTwoLevelRankDataOfChunksExactLocalBlock,
    SuccinctRank.canonicalTwoLevelRankDataOfBridgeLocalBlock,
    SuccinctRank.canonicalBlockRankSampleTablesOfLocalSpan,
    SuccinctRank.canonicalBlockRankEntries_length,
    GenericSelect.sparseExceptionEffectiveFlagRankBlockWidth,
    packedSparseRankSlots, sparseFlagBits_length_eq_packed,
    sparseFlagRankWordSize_eq_packed]

/-! ## The long relative table

The one source whose word count depends on the decoded header rather than on the
input size alone -- which is what the header cell is for.
-/

/-- Slots in the long-super relative table, from the decoded long count. -/
def packedLongRelativeSlots (n longCount : Nat) : Nat :=
  longCount * GenericSelect.superStride (2 * n)

theorem packedSelectLongRelativeWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectLongRelative)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectLongRelative)
        (packedLongRelativeSlots shape.size (longCount shape))
        (packedSuperWidth shape.size) i := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  show
    (GenericSelect.longSuperRelativeTable shape.bpCode false).store.words[i]? =
      packedWordSlice
        (GenericSelect.longSuperRelativeTable shape.bpCode false).payload
        (packedLongRelativeSlots shape.size (longCount shape))
        (packedSuperWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [GenericSelect.longSuperRelativeEntries_length, longCount,
    packedLongRelativeSlots, GenericSelect.longSuperRelativeWidth,
    packedSuperWidth, GenericSelect.wordBits, hlen]

/-! ## The close summary and interior tables -/

theorem packedCloseSummaryBaselineWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryBaseline)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeSummaryBaseline)
        (packedSummarySuperCount shape.size)
        (packedSummarySuperWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).baselineTable.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).baselineTable.payload
        (packedSummarySuperCount shape.size)
        (packedSummarySuperWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [SuccinctClose.bpSuperblockBaselineEntries_length,
    summarySuperCount_eq_packed, summarySuperWidth_eq_packed]

theorem packedCloseSummaryMinRelWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryMinRel)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeSummaryMinRel)
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).minRelTable.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).minRelTable.payload
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [SuccinctClose.bpBlockRelativeMinExcessEntries_length,
    summaryBlockCount_eq_packed, summaryRelativeWidth_eq_packed]

theorem packedCloseSummaryMaxRelWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryMaxRel)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeSummaryMaxRel)
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).maxRelTable.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).maxRelTable.payload
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [SuccinctClose.bpBlockRelativeMaxExcessEntries_length,
    summaryBlockCount_eq_packed, summaryRelativeWidth_eq_packed]

theorem packedCloseSummaryArgOffsetWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeSummaryArgOffset)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeSummaryArgOffset)
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
      shape).argOffsetTable.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeMinMaxArgSummaryTable_canonical
          shape).argOffsetTable.payload
        (packedSummaryBlockCount shape.size)
        (packedSummaryRelativeWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  simp only [SuccinctClose.bpBlockArgMinLocalOffsetEntries_length,
    summaryBlockCount_eq_packed, summaryRelativeWidth_eq_packed]

/-- Slots in the interior local offset table. -/
def packedInteriorLocalSlots (n : Nat) : Nat :=
  packedInteriorMacroCount n *
    (packedInteriorOffsetWidth n * packedInteriorMacroSize n)

/-- Size-only mirror of the interior global level count. -/
def packedInteriorGlobalLevelCount (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedInteriorMacroCount n)

/-- Size-only mirror of the interior global block width. -/
def packedInteriorBlockWidth (n : Nat) : Nat :=
  SuccinctRank.machineWordBits (packedSummaryBlockCount n)

/-- Slots in the interior global block table. -/
def packedInteriorGlobalSlots (n : Nat) : Nat :=
  packedInteriorGlobalLevelCount n * packedInteriorMacroCount n

theorem packedCloseInteriorLocalWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeInteriorLocal)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeInteriorLocal)
        (packedInteriorLocalSlots shape.size)
        (packedInteriorOffsetWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
      shape).table.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeRmmInteriorLocalTable
          shape).table.payload
        (packedInteriorLocalSlots shape.size)
        (packedInteriorOffsetWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  unfold packedInteriorLocalSlots
  simp only [SuccinctClose.bpLocalSparseOffsetEntries_length,
    SuccinctClose.concreteBPRelativeRmmInteriorLevelCount,
    interiorMacroCount_eq_packed, interiorOffsetWidth_eq_packed]
  simp only [SuccinctClose.concreteBPRelativeRmmInteriorMacroSize,
    SuccinctClose.canonicalBPRelativeSummaryBase,
    packedInteriorMacroSize, packedSummaryBase]

theorem packedCloseInteriorGlobalWords (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeInteriorGlobal)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeInteriorGlobal)
        (packedInteriorGlobalSlots shape.size)
        (packedInteriorBlockWidth shape.size) i := by
  show
    (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
      shape).table.store.words[i]? =
      packedWordSlice
        (SuccinctClose.concreteBPRelativeRmmInteriorGlobalTable
          shape).table.payload
        (packedInteriorGlobalSlots shape.size)
        (packedInteriorBlockWidth shape.size) i
  rw [packedFixedWidthTable_getElem?]
  unfold packedInteriorGlobalSlots packedInteriorGlobalLevelCount
    packedInteriorBlockWidth
  simp only [SuccinctClose.bpGlobalSparseBlockEntries_length,
    SuccinctClose.concreteBPRelativeRmmInteriorGlobalLevelCount,
    SuccinctClose.concreteBPRelativeRmmInteriorBlockWidth,
    interiorMacroCount_eq_packed, summaryBlockCount_eq_packed]

/-! ## The sparse relative table: the one count the header does not carry

Twenty-eight of the twenty-nine sources have a word count that is a function of
the input size and the decoded long count. This one does not.

`sparseExceptionRelativeEntries_length` gives the count as

```
rankPrefix true (sparseExceptionFlagBits bits target) (localSlotCount bits target)
  * localStride bits.length
```

and the leading factor is the number of local slots whose span forced a sparse
exception. That is a property of the bit pattern, not of its length: two shapes of
the same size share `n`, `longCount` does not record it, and no other stored
scalar does either. `K1` puts exactly one count in the header, and the
architecture spends it on `longCount`.

What is still true, and what this section proves, is the direction the lowering
needs. The exception count is bounded by the local slot count, which *is*
size-only, so a controller can use that bound as the table's capacity and every
**successful** logical read still lowers to the right slice. The residual is
one-directional: at an index between the real count and the capacity the packed
read answers where the store would have failed. Closing that gap is `FG-09`'s
totality clause -- every attempted probe of an actual run is successful -- not a
second header field.
-/

/-- The size-only capacity of the sparse relative table: every local slot an
exception. -/
def packedSparseRelativeCapacity (n : Nat) : Nat :=
  packedLocalSlots n * GenericSelect.localStride (2 * n)

theorem packedSparseRelativeEntries_le_capacity (shape : CartesianShape) :
    (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length <=
      packedSparseRelativeCapacity shape.size := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hrank :=
    RMQ.Succinct.rankPrefix_le_limit true
      (GenericSelect.sparseExceptionFlagBits shape.bpCode false)
      (GenericSelect.localSlotCount shape.bpCode false)
  rw [GenericSelect.sparseExceptionRelativeEntries_length]
  unfold packedSparseRelativeCapacity
  rw [hlen, ← localSlotCount_eq_packed shape]
  exact Nat.mul_le_mul_right _ hrank

/--
**Every successful sparse relative read lowers.** Stated as an implication rather
than an equation, because the packed side uses the size-only capacity and the
store uses the actual exception count.
-/
theorem packedSelectSparseRelativeWords_of_some
    (shape : CartesianShape) {i : Nat} {word : List Bool}
    (hget :
      (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .selectSparseRelative)[i]? = some word) :
    packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .selectSparseRelative)
        (packedSparseRelativeCapacity shape.size)
        (packedLocalWidth shape.size) i =
      some word := by
  have hlen : shape.bpCode.length = 2 * shape.size :=
    CartesianShape.bpCode_length shape
  have hw :
      GenericSelect.sparseExceptionRelativeWidth shape.bpCode =
        packedLocalWidth shape.size := by
    unfold GenericSelect.sparseExceptionRelativeWidth packedLocalWidth
    rw [hlen]
  have hbound := packedSparseRelativeEntries_le_capacity shape
  have hget' :
      (GenericSelect.sparseExceptionRelativeTable shape.bpCode
        false).store.words[i]? = some word := hget
  rw [packedFixedWidthTable_getElem?] at hget'
  show
    packedWordSlice
        (GenericSelect.sparseExceptionRelativeTable shape.bpCode false).payload
        (packedSparseRelativeCapacity shape.size)
        (packedLocalWidth shape.size) i =
      some word
  by_cases hi :
      i < (GenericSelect.sparseExceptionRelativeEntries shape.bpCode false).length
  · rw [packedWordSlice_of_lt hi] at hget'
    rw [packedWordSlice_of_lt (by omega), ← hw]
    exact hget'
  · rw [packedWordSlice_of_le (by omega)] at hget'
    exact absurd hget' (by simp)

/-! ## The retired finite-small slots

Three sources with no words and no payload. They are present as their own arms
rather than folded into a default, so a later change that gave them content would
break these proofs rather than pass silently.
-/

theorem packedCloseFiniteSmallInteriorMinWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeFiniteSmallInteriorMin)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeFiniteSmallInteriorMin) 0 0 i := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSourceWords, packedWordSlice]

theorem packedCloseFiniteSmallInteriorArgWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeFiniteSmallInteriorArg)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeFiniteSmallInteriorArg) 0 0 i := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSourceWords, packedWordSlice]

theorem packedCloseFiniteSmallSameBlockWords
    (shape : CartesianShape) (i : Nat) :
    (concreteBPNativeSuccinctRMQFlatPayloadSourceWords shape
        .closeFiniteSmallSameBlock)[i]? =
      packedWordSlice
        (concreteBPNativeSuccinctRMQFlatPayloadSourcePayload shape
          .closeFiniteSmallSameBlock) 0 0 i := by
  simp [concreteBPNativeSuccinctRMQFlatPayloadSourceWords, packedWordSlice]

end PackedCellProbe

end SuccinctFinal

end RMQ
