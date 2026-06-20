import RMQ.Core.SuccinctSpace

/-!
# Rank-side sampled-directory proposal

This module isolates the rank-side theorem surface matching
`SuccinctSelectProposal`.

The hard construction still has to build the sampled prefix tables and chunked
payload-word store.  The definitions below say what that construction should
return: payload-live rank data whose sample payload fits in the canonical
sampled-directory envelope, while queries use the existing counted path

1. read one rank sample,
2. read one payload word,
3. run the word-rank primitive.
-/

namespace RMQ
namespace SuccinctRankProposal

open SuccinctSpace

private theorem list_getElem?_append_left_some
    {α : Type} {xs ys : List α} {i : Nat} {value : α}
    (hget : xs[i]? = some value) :
    (xs ++ ys)[i]? = some value := by
  induction xs generalizing i with
  | nil =>
      simp at hget
  | cons head tail ih =>
      cases i with
      | zero =>
          simpa using hget
      | succ i =>
          exact ih hget

/-- Machine-word budget used by the word-RAM-facing rank/select targets. -/
def machineWordBits (n : Nat) : Nat :=
  Nat.log2 n + 1

theorem machineWordBits_pos (n : Nat) : 0 < machineWordBits n := by
  unfold machineWordBits
  omega

/-- Rank samples at word boundaries. -/
def rankSampleEntries
    (target : Bool) (bits : List Bool) (wordSize : Nat) : List Nat :=
  (List.range (bits.length / wordSize + 1)).map
    (fun i => RMQ.Succinct.rankPrefix target bits (i * wordSize))

theorem rankSampleEntries_getOpt_exact
    {target : Bool} {bits : List Bool} {wordSize i sample : Nat}
    (hget :
      (rankSampleEntries target bits wordSize)[i]? = some sample) :
    sample = RMQ.Succinct.rankPrefix target bits (i * wordSize) := by
  unfold rankSampleEntries at hget
  by_cases hlt : i < bits.length / wordSize + 1
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem rankPrefix_mono_limit
    (target : Bool) (bits : List Bool) {lo hi : Nat}
    (h : lo <= hi) :
    RMQ.Succinct.rankPrefix target bits lo <=
      RMQ.Succinct.rankPrefix target bits hi := by
  induction bits generalizing lo hi with
  | nil =>
      simp [RMQ.Succinct.rankPrefix_nil]
  | cons bit rest ih =>
      cases lo with
      | zero =>
          have hle :=
            RMQ.Succinct.rankPrefix_le_limit target (bit :: rest) hi
          simp [RMQ.Succinct.rankPrefix]
      | succ lo =>
          cases hi with
          | zero =>
              omega
          | succ hi =>
              have htail : lo <= hi := by omega
              have hrec := ih htail
              by_cases hbit : bit = target
              · simp [RMQ.Succinct.rankPrefix, hbit]
                omega
              · simp [RMQ.Succinct.rankPrefix, hbit]
                exact hrec

def canonicalSuperRankEntries
    (target : Bool) (bits : List Bool)
    (wordSize blocksPerSuper : Nat) : List Nat :=
  (List.range (bits.length / wordSize / blocksPerSuper + 1)).map
    (fun superIndex =>
      RMQ.Succinct.rankPrefix target bits
        ((superIndex * blocksPerSuper) * wordSize))

def canonicalBlockRankEntries
    (target : Bool) (bits : List Bool)
    (wordSize blocksPerSuper : Nat) : List Nat :=
  (List.range (bits.length / wordSize + 1)).map
    (fun wordIndex =>
      RMQ.Succinct.rankPrefix target bits (wordIndex * wordSize) -
        RMQ.Succinct.rankPrefix target bits
          (((wordIndex / blocksPerSuper) * blocksPerSuper) * wordSize))

theorem canonicalSuperRankEntries_getOpt_exact
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper i sample : Nat}
    (hget :
      (canonicalSuperRankEntries target bits wordSize blocksPerSuper)[i]? =
        some sample) :
    sample =
      RMQ.Succinct.rankPrefix target bits
        ((i * blocksPerSuper) * wordSize) := by
  unfold canonicalSuperRankEntries at hget
  by_cases hlt : i < bits.length / wordSize / blocksPerSuper + 1
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem canonicalBlockRankEntries_getOpt_exact
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper i sample : Nat}
    (hget :
      (canonicalBlockRankEntries target bits wordSize blocksPerSuper)[i]? =
        some sample) :
    sample =
      RMQ.Succinct.rankPrefix target bits (i * wordSize) -
        RMQ.Succinct.rankPrefix target bits
          (((i / blocksPerSuper) * blocksPerSuper) * wordSize) := by
  unfold canonicalBlockRankEntries at hget
  by_cases hlt : i < bits.length / wordSize + 1
  · simp [List.getElem?_map, List.getElem?_range hlt] at hget
    exact hget.symm
  · simp [hlt] at hget

theorem canonicalSuperRankEntries_present
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper pos : Nat}
    (hpos : pos <= bits.length) :
    exists sample,
      (canonicalSuperRankEntries target bits wordSize blocksPerSuper)[
        (pos / wordSize) / blocksPerSuper]? = some sample := by
  let i := (pos / wordSize) / blocksPerSuper
  have hwordIndex :
      pos / wordSize <= bits.length / wordSize := by
    exact Nat.div_le_div_right hpos
  have hsuperIndex :
      i <= bits.length / wordSize / blocksPerSuper := by
    exact Nat.div_le_div_right hwordIndex
  have hi :
      i < bits.length / wordSize / blocksPerSuper + 1 := by
    omega
  refine ⟨RMQ.Succinct.rankPrefix target bits
      ((i * blocksPerSuper) * wordSize), ?_⟩
  unfold canonicalSuperRankEntries
  simp [i, List.getElem?_map, List.getElem?_range hi]

theorem canonicalBlockRankEntries_present
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper pos : Nat}
    (hpos : pos <= bits.length) :
    exists delta,
      (canonicalBlockRankEntries target bits wordSize blocksPerSuper)[
        pos / wordSize]? = some delta := by
  let i := pos / wordSize
  have hwordIndex :
      i <= bits.length / wordSize := by
    exact Nat.div_le_div_right hpos
  have hi : i < bits.length / wordSize + 1 := by
    omega
  refine
    ⟨RMQ.Succinct.rankPrefix target bits (i * wordSize) -
        RMQ.Succinct.rankPrefix target bits
          (((i / blocksPerSuper) * blocksPerSuper) * wordSize), ?_⟩
  unfold canonicalBlockRankEntries
  simp [i, List.getElem?_map, List.getElem?_range hi]

theorem canonicalSuperRankEntries_mem_bound
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper width entry : Nat}
    (hmem :
      List.Mem entry
        (canonicalSuperRankEntries target bits wordSize blocksPerSuper))
    (hwidth : bits.length < 2 ^ width) :
    entry < 2 ^ width := by
  unfold canonicalSuperRankEntries at hmem
  rcases List.mem_map.mp hmem with ⟨i, _hi, rfl⟩
  exact Nat.lt_of_le_of_lt
    (RMQ.Succinct.rankPrefix_le_length target bits
      ((i * blocksPerSuper) * wordSize))
    hwidth

theorem canonicalBlockRankEntries_mem_bound
    {target : Bool} {bits : List Bool}
    {wordSize blocksPerSuper width entry : Nat}
    (hmem :
      List.Mem entry
        (canonicalBlockRankEntries target bits wordSize blocksPerSuper))
    (hwidth : bits.length < 2 ^ width) :
    entry < 2 ^ width := by
  unfold canonicalBlockRankEntries at hmem
  rcases List.mem_map.mp hmem with ⟨i, _hi, rfl⟩
  exact Nat.lt_of_le_of_lt
    (Nat.sub_le
      (RMQ.Succinct.rankPrefix target bits (i * wordSize))
      (RMQ.Succinct.rankPrefix target bits
        (((i / blocksPerSuper) * blocksPerSuper) * wordSize)))
    (Nat.lt_of_le_of_lt
      (RMQ.Succinct.rankPrefix_le_length target bits (i * wordSize))
      hwidth)

def canonicalSuperRankSampleTables
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hwidth : bits.length < 2 ^ width) :
    SuccinctSpace.FixedWidthRankSampleTables
      (canonicalSuperRankEntries true bits wordSize blocksPerSuper)
      (canonicalSuperRankEntries false bits wordSize blocksPerSuper)
      width :=
  SuccinctSpace.FixedWidthRankSampleTables.ofEntries
    (canonicalSuperRankEntries true bits wordSize blocksPerSuper)
    (canonicalSuperRankEntries false bits wordSize blocksPerSuper)
    width
    (fun hmem =>
      canonicalSuperRankEntries_mem_bound
        (target := true) hmem hwidth)
    (fun hmem =>
      canonicalSuperRankEntries_mem_bound
        (target := false) hmem hwidth)

def canonicalBlockRankSampleTables
    (bits : List Bool) (wordSize blocksPerSuper width : Nat)
    (hwidth : bits.length < 2 ^ width) :
    SuccinctSpace.FixedWidthRankSampleTables
      (canonicalBlockRankEntries true bits wordSize blocksPerSuper)
      (canonicalBlockRankEntries false bits wordSize blocksPerSuper)
      width :=
  SuccinctSpace.FixedWidthRankSampleTables.ofEntries
    (canonicalBlockRankEntries true bits wordSize blocksPerSuper)
    (canonicalBlockRankEntries false bits wordSize blocksPerSuper)
    width
    (fun hmem =>
      canonicalBlockRankEntries_mem_bound
        (target := true) hmem hwidth)
    (fun hmem =>
      canonicalBlockRankEntries_mem_bound
        (target := false) hmem hwidth)

@[simp] theorem canonicalSuperRankSampleTables_entries
    {bits : List Bool} {wordSize blocksPerSuper width : Nat}
    (hwidth : bits.length < 2 ^ width) (target : Bool) :
    (canonicalSuperRankSampleTables
        bits wordSize blocksPerSuper width hwidth).entries target =
      canonicalSuperRankEntries target bits wordSize blocksPerSuper := by
  cases target <;> rfl

@[simp] theorem canonicalBlockRankSampleTables_entries
    {bits : List Bool} {wordSize blocksPerSuper width : Nat}
    (hwidth : bits.length < 2 ^ width) (target : Bool) :
    (canonicalBlockRankSampleTables
        bits wordSize blocksPerSuper width hwidth).entries target =
      canonicalBlockRankEntries target bits wordSize blocksPerSuper := by
  cases target <;> rfl

theorem canonicalSuperRankSampleTables_present
    {bits : List Bool} {wordSize blocksPerSuper width pos : Nat}
    (hwidth : bits.length < 2 ^ width)
    (target : Bool) (hpos : pos <= bits.length) :
    exists sample,
      ((canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper width hwidth).entries target)[
        (pos / wordSize) / blocksPerSuper]? = some sample := by
  simpa using
    (canonicalSuperRankEntries_present
      (target := target) (bits := bits)
      (wordSize := wordSize) (blocksPerSuper := blocksPerSuper)
      (pos := pos) hpos)

theorem canonicalBlockRankSampleTables_present
    {bits : List Bool} {wordSize blocksPerSuper width pos : Nat}
    (hwidth : bits.length < 2 ^ width)
    (target : Bool) (hpos : pos <= bits.length) :
    exists delta,
      ((canonicalBlockRankSampleTables
          bits wordSize blocksPerSuper width hwidth).entries target)[
        pos / wordSize]? = some delta := by
  simpa using
    (canonicalBlockRankEntries_present
      (target := target) (bits := bits)
      (wordSize := wordSize) (blocksPerSuper := blocksPerSuper)
      (pos := pos) hpos)

theorem canonicalSuperRankSampleTables_payload_length
    {bits : List Bool} {wordSize blocksPerSuper width : Nat}
    (hwidth : bits.length < 2 ^ width) :
    (canonicalSuperRankSampleTables
        bits wordSize blocksPerSuper width hwidth).payload.length =
      (canonicalSuperRankEntries true bits wordSize blocksPerSuper).length *
          width +
        (canonicalSuperRankEntries false bits wordSize blocksPerSuper).length *
          width := by
  exact SuccinctSpace.FixedWidthRankSampleTables.payload_length
    (canonicalSuperRankSampleTables
      bits wordSize blocksPerSuper width hwidth)

theorem canonicalBlockRankSampleTables_payload_length
    {bits : List Bool} {wordSize blocksPerSuper width : Nat}
    (hwidth : bits.length < 2 ^ width) :
    (canonicalBlockRankSampleTables
        bits wordSize blocksPerSuper width hwidth).payload.length =
      (canonicalBlockRankEntries true bits wordSize blocksPerSuper).length *
          width +
        (canonicalBlockRankEntries false bits wordSize blocksPerSuper).length *
          width := by
  exact SuccinctSpace.FixedWidthRankSampleTables.payload_length
    (canonicalBlockRankSampleTables
      bits wordSize blocksPerSuper width hwidth)

theorem canonicalRankParts_exact_of_word_local
    {target : Bool} {bits word : List Bool}
    {wordSize blocksPerSuper pos super delta : Nat}
    (hsuper :
      (canonicalSuperRankEntries target bits wordSize blocksPerSuper)[
        (pos / wordSize) / blocksPerSuper]? = some super)
    (hdelta :
      (canonicalBlockRankEntries target bits wordSize blocksPerSuper)[
        pos / wordSize]? = some delta)
    (hlocal :
      RMQ.RAM.boolRankPrefix target word
          (pos - (pos / wordSize) * wordSize) =
        RMQ.Succinct.rankPrefix target bits pos -
          RMQ.Succinct.rankPrefix target bits
            ((pos / wordSize) * wordSize)) :
    super + delta +
        RMQ.RAM.boolRankPrefix target word
          (pos - (pos / wordSize) * wordSize) =
      RMQ.Succinct.rankPrefix target bits pos := by
  let wordIndex := pos / wordSize
  let superIndex := wordIndex / blocksPerSuper
  let superStart := (superIndex * blocksPerSuper) * wordSize
  let wordStart := wordIndex * wordSize
  have hsuperExact :
      super =
        RMQ.Succinct.rankPrefix target bits superStart := by
    simpa [wordIndex, superIndex, superStart] using
      canonicalSuperRankEntries_getOpt_exact hsuper
  have hdeltaExact :
      delta =
        RMQ.Succinct.rankPrefix target bits wordStart -
          RMQ.Succinct.rankPrefix target bits superStart := by
    simpa [wordIndex, superIndex, superStart, wordStart] using
      canonicalBlockRankEntries_getOpt_exact hdelta
  have hsuperStart_le_wordStart : superStart <= wordStart := by
    have hdiv : superIndex * blocksPerSuper <= wordIndex := by
      simpa [superIndex] using
        (Nat.div_mul_le_self wordIndex blocksPerSuper)
    unfold superStart wordStart
    exact Nat.mul_le_mul_right wordSize hdiv
  have hwordStart_le_pos : wordStart <= pos := by
    simpa [wordIndex, wordStart] using
      (Nat.div_mul_le_self pos wordSize)
  have hprefixSuper_le_word :
      RMQ.Succinct.rankPrefix target bits superStart <=
        RMQ.Succinct.rankPrefix target bits wordStart :=
    rankPrefix_mono_limit target bits hsuperStart_le_wordStart
  have hprefixWord_le_pos :
      RMQ.Succinct.rankPrefix target bits wordStart <=
        RMQ.Succinct.rankPrefix target bits pos :=
    rankPrefix_mono_limit target bits hwordStart_le_pos
  have hlocal' :
      RMQ.RAM.boolRankPrefix target word
          (pos - (pos / wordSize) * wordSize) =
        RMQ.Succinct.rankPrefix target bits pos -
          RMQ.Succinct.rankPrefix target bits wordStart := by
    simpa [wordIndex, wordStart] using hlocal
  rw [hsuperExact, hdeltaExact, hlocal']
  omega

theorem chunkPayloadWords_rankPrefix_exact
    {target : Bool} {bits word : List Bool} {wordSize pos : Nat}
    (hwordSize : 0 < wordSize)
    (hpos : pos <= bits.length)
    (hget :
      (SuccinctSpace.chunkPayloadWords wordSize bits)[pos / wordSize]? =
        some word) :
    RMQ.RAM.boolRankPrefix target word
        (pos - (pos / wordSize) * wordSize) =
      RMQ.Succinct.rankPrefix target bits pos -
        RMQ.Succinct.rankPrefix target bits
          ((pos / wordSize) * wordSize) := by
  let start := (pos / wordSize) * wordSize
  let offset := pos - start
  have hwordEq :
      word = (bits.drop start).take wordSize := by
    simpa [start] using
      (SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hget)
  have hstart_le_pos : start <= pos := by
    simpa [start] using Nat.div_mul_le_self pos wordSize
  have hoffset_lt_wordSize : offset < wordSize := by
    have hlt := Nat.lt_div_mul_add hwordSize (a := pos)
    simp [offset, start]
    omega
  have hoffset_le_drop_length :
      offset <= (bits.drop start).length := by
    rw [List.length_drop]
    omega
  have hoffset_le_take_length :
      offset <= ((bits.drop start).take wordSize).length := by
    rw [List.length_take]
    exact Nat.le_min.mpr
      ⟨Nat.le_of_lt hoffset_lt_wordSize, hoffset_le_drop_length⟩
  have htake :
      RMQ.Succinct.rankPrefix target ((bits.drop start).take wordSize)
          offset =
        RMQ.Succinct.rankPrefix target (bits.drop start) offset :=
    RMQ.Succinct.rankPrefix_take_eq_of_le
      target (bits.drop start) (n := wordSize)
      (limit := offset) hoffset_le_take_length
  have hdrop :
      RMQ.Succinct.rankPrefix target (bits.drop start) offset =
        RMQ.Succinct.rankPrefix target bits pos -
          RMQ.Succinct.rankPrefix target bits start := by
    simpa [offset] using
      RMQ.Succinct.rankPrefix_drop_eq_sub_of_le
        target bits hstart_le_pos hpos
  calc
    RMQ.RAM.boolRankPrefix target word
        (pos - (pos / wordSize) * wordSize) =
        RMQ.Succinct.rankPrefix target word offset := by
          simp [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix,
            offset, start]
    _ = RMQ.Succinct.rankPrefix target ((bits.drop start).take wordSize)
        offset := by
          rw [hwordEq]
    _ = RMQ.Succinct.rankPrefix target (bits.drop start) offset := htake
    _ = RMQ.Succinct.rankPrefix target bits pos -
        RMQ.Succinct.rankPrefix target bits start := hdrop
    _ = RMQ.Succinct.rankPrefix target bits pos -
        RMQ.Succinct.rankPrefix target bits
          ((pos / wordSize) * wordSize) := by
          rfl

theorem ofChunks_rankPrefix_exact
    {target : Bool} {bits word : List Bool} {wordSize pos : Nat}
    (hwordSize : 0 < wordSize)
    (hpos : pos <= bits.length)
    (hget :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        bits hwordSize).store.words[pos / wordSize]? = some word) :
    RMQ.RAM.boolRankPrefix target word
        (pos - (pos / wordSize) * wordSize) =
      RMQ.Succinct.rankPrefix target bits pos -
        RMQ.Succinct.rankPrefix target bits
          ((pos / wordSize) * wordSize) := by
  have hlist :
      (SuccinctSpace.chunkPayloadWords wordSize bits)[pos / wordSize]? =
        some word := by
    simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
        Array.getElem?_toList] using hget
  exact chunkPayloadWords_rankPrefix_exact hwordSize hpos hlist

theorem ofChunks_word_present_of_lt
    {bits : List Bool} {wordSize pos : Nat}
    (hwordSize : 0 < wordSize)
    (hpos : pos < bits.length) :
    exists word,
      (SuccinctSpace.BoundedPayloadWordStore.ofChunks
        bits hwordSize).store.words[pos / wordSize]? = some word := by
  have hstart_lt :
      (pos / wordSize) * wordSize < bits.length := by
    have hstart_le : (pos / wordSize) * wordSize <= pos :=
      Nat.div_mul_le_self pos wordSize
    omega
  rcases
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        hwordSize hstart_lt with
    ⟨word, hget⟩
  refine ⟨word, ?_⟩
  simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunks,
    Array.getElem?_toList] using hget

theorem ofChunksWithSentinel_word_present
    {bits : List Bool} {wordSize pos : Nat}
    (hwordSize : 0 < wordSize)
    (hpos : pos <= bits.length) :
    exists word,
      (SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel
        bits hwordSize).store.words[pos / wordSize]? = some word := by
  let words :=
    SuccinctSpace.chunkPayloadWords wordSize bits ++
      List.replicate (bits.length + 1) []
  have hi : pos / wordSize < words.length := by
    have hdiv : pos / wordSize <= pos := Nat.div_le_self pos wordSize
    simp [words]
    omega
  refine ⟨words.get ⟨pos / wordSize, hi⟩, ?_⟩
  simp [SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel,
    words]

theorem ofChunksWithSentinel_rankPrefix_exact
    {target : Bool} {bits word : List Bool} {wordSize pos : Nat}
    (hwordSize : 0 < wordSize)
    (hpos : pos <= bits.length)
    (hget :
      (SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel
        bits hwordSize).store.words[pos / wordSize]? = some word) :
    RMQ.RAM.boolRankPrefix target word
        (pos - (pos / wordSize) * wordSize) =
      RMQ.Succinct.rankPrefix target bits pos -
        RMQ.Succinct.rankPrefix target bits
          ((pos / wordSize) * wordSize) := by
  let start := (pos / wordSize) * wordSize
  by_cases hstart_lt : start < bits.length
  · rcases
      SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
        hwordSize hstart_lt with
      ⟨chunkWord, hchunk⟩
    have hlist :
        (SuccinctSpace.chunkPayloadWords wordSize bits ++
          List.replicate (bits.length + 1) [])[pos / wordSize]? =
            some word := by
      simpa [SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel,
        Array.getElem?_toList] using hget
    have happend :
        (SuccinctSpace.chunkPayloadWords wordSize bits ++
          List.replicate (bits.length + 1) [])[pos / wordSize]? =
            some chunkWord := by
      exact list_getElem?_append_left_some hchunk
    rw [happend] at hlist
    injection hlist with hwordEq
    subst word
    exact chunkPayloadWords_rankPrefix_exact hwordSize hpos hchunk
  · have hstart_le_pos : start <= pos := by
      simpa [start] using Nat.div_mul_le_self pos wordSize
    have hstart_eq_pos : start = pos := by
      omega
    have hoffset : pos - (pos / wordSize) * wordSize = 0 := by
      omega
    rw [hoffset]
    simp [RMQ.Succinct.ram_boolRankPrefix_eq_rankPrefix,
      RMQ.Succinct.rankPrefix, start, hstart_eq_pos]

/-!
## Two-level rank target

The single-level wrappers below are useful migration targets, but by themselves
they do not fix the classical word-RAM tension: if each rank sample is a
full-width `log n` counter, then `o(n)` single-level sample overhead pushes the
payload word size beyond a machine word.  The next target is therefore a
two-level directory: superblock payload plus block payload plus a bounded word
store, with query exactness supplied by the eventual concrete builder.
-/

def twoLevelRankOverhead
    (super block : Nat -> Nat) (n : Nat) : Nat :=
  super n + block n

theorem twoLevelRankOverhead_littleO
    {super block : Nat -> Nat}
    (hsuper : SuccinctSpace.LittleOLinear super)
    (hblock : SuccinctSpace.LittleOLinear block) :
    SuccinctSpace.LittleOLinear
      (twoLevelRankOverhead super block) := by
  unfold twoLevelRankOverhead
  exact hsuper.add hblock

/-- Canonical rank-superblock budget: `O(n / log n)` bits. -/
def canonicalTwoLevelRankSuperOverhead (slots : Nat) : Nat -> Nat :=
  SuccinctSpace.sampledDirectoryOverhead slots

/-- Canonical rank-block budget: `O(n log log n / log n)` bits. -/
def canonicalTwoLevelRankBlockOverhead (slots : Nat) : Nat -> Nat :=
  SuccinctSpace.logLogSampledDirectoryOverhead slots

/-- Combined canonical two-level rank auxiliary budget. -/
def canonicalTwoLevelRankOverhead
    (superSlots blockSlots : Nat) : Nat -> Nat :=
  twoLevelRankOverhead
    (canonicalTwoLevelRankSuperOverhead superSlots)
    (canonicalTwoLevelRankBlockOverhead blockSlots)

theorem canonicalTwoLevelRankSuperOverhead_littleO (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelRankSuperOverhead slots) := by
  exact SuccinctSpace.sampledDirectoryOverhead_littleO slots

theorem canonicalTwoLevelRankBlockOverhead_littleO (slots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelRankBlockOverhead slots) := by
  exact SuccinctSpace.logLogSampledDirectoryOverhead_littleO slots

theorem canonicalTwoLevelRankOverhead_littleO
    (superSlots blockSlots : Nat) :
    SuccinctSpace.LittleOLinear
      (canonicalTwoLevelRankOverhead superSlots blockSlots) := by
  exact
    twoLevelRankOverhead_littleO
      (canonicalTwoLevelRankSuperOverhead_littleO superSlots)
      (canonicalTwoLevelRankBlockOverhead_littleO blockSlots)

/--
Payload-live two-level rank component target.

The structure is intentionally an interface, not a construction.  It fixes the
word-RAM obligations a concrete builder must discharge: payload words are
bounded by `wordSize`, `wordSize` fits the modeled machine-word budget, and the
auxiliary payload is split into superblock and block directories.
-/
structure TwoLevelPayloadLiveStoredWordRankData
    (bits : List Bool)
    (superOverhead blockOverhead queryCost : Nat) where
  wordSize : Nat
  wordSize_pos : 0 < wordSize
  wordSize_le_machine : wordSize <= machineWordBits bits.length
  blocksPerSuper : Nat
  blocksPerSuper_pos : 0 < blocksPerSuper
  superWidth : Nat
  blockWidth : Nat
  superTrueEntries : List Nat
  superFalseEntries : List Nat
  blockTrueEntries : List Nat
  blockFalseEntries : List Nat
  superTables :
    SuccinctSpace.FixedWidthRankSampleTables
      superTrueEntries superFalseEntries superWidth
  blockTables :
    SuccinctSpace.FixedWidthRankSampleTables
      blockTrueEntries blockFalseEntries blockWidth
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  superPayload_length : superTables.payload.length = superOverhead
  blockPayload_length : blockTables.payload.length = blockOverhead
  queryCost_ge_four : 4 <= queryCost
  super_present :
    forall target pos,
      pos <= bits.length ->
        exists sample,
          (superTables.entries target)[
            (pos / wordSize) / blocksPerSuper]? = some sample
  block_present :
    forall target pos,
      pos <= bits.length ->
        exists delta,
          (blockTables.entries target)[pos / wordSize]? = some delta
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, bitWords.store.words[pos / wordSize]? = some word
  rank_parts_exact :
    forall target pos super delta word,
      pos <= bits.length ->
        (superTables.entries target)[
            (pos / wordSize) / blocksPerSuper]? = some super ->
        (blockTables.entries target)[pos / wordSize]? = some delta ->
        bitWords.store.words[pos / wordSize]? = some word ->
          super + delta +
              RMQ.RAM.boolRankPrefix target word
                (pos - (pos / wordSize) * wordSize) =
            RMQ.Succinct.rankPrefix target bits pos

namespace TwoLevelPayloadLiveStoredWordRankData

def queryPos
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (_data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : Nat) : Nat :=
  Nat.min pos bits.length

def wordIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : Nat) : Nat :=
  data.queryPos pos / data.wordSize

def superIndex
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : Nat) : Nat :=
  data.wordIndex pos / data.blocksPerSuper

def wordOffset
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (pos : Nat) : Nat :=
  data.queryPos pos - data.wordIndex pos * data.wordSize

def superPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superTables.payload

def blockPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.blockTables.payload

def auxPayload
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    List Bool :=
  data.superPayload ++ data.blockPayload

def rankCosted
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) : RMQ.Costed Nat :=
  RMQ.Costed.bind
    (data.superTables.sampleCosted target (data.superIndex pos))
    fun super? =>
      RMQ.Costed.bind
        (data.blockTables.sampleCosted target (data.wordIndex pos))
        fun delta? =>
          RMQ.Costed.bind
            (data.bitWords.store.readWordCosted (data.wordIndex pos))
            fun word? =>
              match super?, delta?, word? with
              | some super, some delta, some word =>
                  RMQ.Costed.map
                    (fun localRank => super + delta + localRank)
                    (RMQ.RAM.rankBoolWordPrefix target word
                      (data.wordOffset pos)).toCosted
              | _, _, _ => RMQ.Costed.pure 0

theorem auxPayload_length
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead := by
  simp [auxPayload, superPayload, blockPayload,
    data.superPayload_length, data.blockPayload_length]

theorem payload_words_erase
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits := by
  exact data.bitWords.erases

theorem rankCosted_cost_le_four
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= 4 := by
  unfold rankCosted
  cases hsuper :
      (data.superTables.sampleCosted target (data.superIndex pos)).value <;>
    cases hblock :
      (data.blockTables.sampleCosted target (data.wordIndex pos)).value <;>
    cases hword :
      (data.bitWords.store.readWordCosted (data.wordIndex pos)).value <;>
    simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
      hsuper, hblock, hword]

theorem rankCosted_cost_le
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).cost <= queryCost := by
  exact Nat.le_trans
    (data.rankCosted_cost_le_four target pos)
    data.queryCost_ge_four

theorem rankCosted_exact
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    (target : Bool) (pos : Nat) :
    (data.rankCosted target pos).erase =
      RMQ.Succinct.rankPrefix target bits pos := by
  have hq : data.queryPos pos <= bits.length := by
    exact Nat.min_le_right pos bits.length
  rcases data.super_present target (data.queryPos pos) hq with
    ⟨super, hsuper⟩
  rcases data.block_present target (data.queryPos pos) hq with
    ⟨delta, hdelta⟩
  rcases data.word_present (data.queryPos pos) hq with
    ⟨word, hword⟩
  have hsuperValue :
      (data.superTables.sampleCosted target (data.superIndex pos)).value =
        some super := by
    have h :=
      data.superTables.sampleCosted_erase target (data.superIndex pos)
    change
      (data.superTables.sampleCosted target (data.superIndex pos)).value =
        (data.superTables.entries target)[data.superIndex pos]? at h
    rw [show data.superIndex pos =
        data.queryPos pos / data.wordSize / data.blocksPerSuper by rfl] at h
    rw [hsuper] at h
    exact h
  have hdeltaValue :
      (data.blockTables.sampleCosted target (data.wordIndex pos)).value =
        some delta := by
    have h :=
      data.blockTables.sampleCosted_erase target (data.wordIndex pos)
    change
      (data.blockTables.sampleCosted target (data.wordIndex pos)).value =
        (data.blockTables.entries target)[data.wordIndex pos]? at h
    rw [show data.wordIndex pos =
        data.queryPos pos / data.wordSize by rfl] at h
    rw [hdelta] at h
    exact h
  have hwordValue :
      (data.bitWords.store.readWordCosted (data.wordIndex pos)).value =
        some word := by
    have h := data.bitWords.store.readWordCosted_erase (data.wordIndex pos)
    change
      (data.bitWords.store.readWordCosted (data.wordIndex pos)).value =
        data.bitWords.store.words[data.wordIndex pos]? at h
    rw [show data.wordIndex pos =
        data.queryPos pos / data.wordSize by rfl] at h
    rw [hword] at h
    exact h
  have hsum :
      super + delta +
          RMQ.RAM.boolRankPrefix target word (data.wordOffset pos) =
        RMQ.Succinct.rankPrefix target bits (data.queryPos pos) := by
    simpa [wordOffset, wordIndex, queryPos] using
      data.rank_parts_exact target (data.queryPos pos) super delta word
        hq hsuper hdelta hword
  have hclamp :
      RMQ.Succinct.rankPrefix target bits (data.queryPos pos) =
        RMQ.Succinct.rankPrefix target bits pos := by
    unfold queryPos
    exact RMQ.Succinct.rankPrefix_min_length_eq target bits pos
  unfold rankCosted
  simp [RMQ.Costed.bind, RMQ.Costed.map, RMQ.Costed.pure,
    RMQ.Costed.erase, hsuperValue, hdeltaValue, hwordValue, hsum,
    hclamp]

theorem payload_word_length_le_machine
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost)
    {word : List Bool}
    (hmem : List.Mem word data.bitWords.store.words.toList) :
    word.length <= machineWordBits bits.length := by
  exact Nat.le_trans
    (data.bitWords.word_length_le hmem)
    data.wordSize_le_machine

theorem profile
    {bits : List Bool} {superOverhead blockOverhead queryCost : Nat}
    (data :
      TwoLevelPayloadLiveStoredWordRankData
        bits superOverhead blockOverhead queryCost) :
    data.auxPayload.length = superOverhead + blockOverhead /\
      data.wordSize <= machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= machineWordBits bits.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= queryCost /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos := by
  constructor
  · exact data.auxPayload_length
  · constructor
    · exact data.wordSize_le_machine
    · constructor
      · exact data.payload_words_erase
      · constructor
        · intro word hmem
          exact data.payload_word_length_le_machine hmem
        · intro target pos
          exact ⟨data.rankCosted_cost_le target pos,
            data.rankCosted_exact target pos⟩

end TwoLevelPayloadLiveStoredWordRankData

/--
The one remaining word-store fact needed by the canonical two-level rank
tables.

`CanonicalRankWordBridge` deliberately isolates the chunk-local obligation:
the sampled-table construction below does not care how payload words are
materialized, only that the chosen bounded store has the queried word and that
word-rank agrees with the corresponding slice of `rankPrefix`.
-/
structure CanonicalRankWordBridge
    (bits : List Bool) (wordSize : Nat) where
  bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize
  word_present :
    forall pos,
      pos <= bits.length ->
        exists word, bitWords.store.words[pos / wordSize]? = some word
  word_rank_exact :
    forall target pos word,
      pos <= bits.length ->
        bitWords.store.words[pos / wordSize]? = some word ->
          RMQ.RAM.boolRankPrefix target word
              (pos - (pos / wordSize) * wordSize) =
            RMQ.Succinct.rankPrefix target bits pos -
              RMQ.Succinct.rankPrefix target bits
                ((pos / wordSize) * wordSize)

/--
The ordinary chunked payload store supplies the local-rank equation directly;
the only extra premise is endpoint presence for the current indexing
convention.
-/
def canonicalRankWordBridgeOfChunks
    (bits : List Bool) {wordSize : Nat}
    (hwordSize : 0 < wordSize)
    (hpresent :
      forall pos,
        pos <= bits.length ->
          exists word,
            (SuccinctSpace.BoundedPayloadWordStore.ofChunks
              bits hwordSize).store.words[pos / wordSize]? = some word) :
    CanonicalRankWordBridge bits wordSize where
  bitWords := SuccinctSpace.BoundedPayloadWordStore.ofChunks bits hwordSize
  word_present := hpresent
  word_rank_exact := by
    intro target pos word hpos hget
    exact ofChunks_rankPrefix_exact hwordSize hpos hget

def canonicalRankWordBridgeOfChunksWithSentinel
    (bits : List Bool) {wordSize : Nat}
    (hwordSize : 0 < wordSize) :
    CanonicalRankWordBridge bits wordSize where
  bitWords :=
    SuccinctSpace.BoundedPayloadWordStore.ofChunksWithSentinel
      bits hwordSize
  word_present := by
    intro pos hpos
    exact ofChunksWithSentinel_word_present hwordSize hpos
  word_rank_exact := by
    intro target pos word hpos hget
    exact ofChunksWithSentinel_rankPrefix_exact hwordSize hpos hget

/--
Package the canonical superblock/block rank sample tables into the full
two-level rank interface, assuming only the chunk-local word bridge.

This is the conservative construction boundary for the next proof: all table
presence, fixed-width payload accounting, cost, and sample arithmetic fields
are discharged here; the remaining work is exactly to build a
`CanonicalRankWordBridge` from the intended payload-word chunker.
-/
def canonicalTwoLevelRankDataOfBridge
    (bits : List Bool)
    {wordSize blocksPerSuper superWidth blockWidth queryCost : Nat}
    (hword : 0 < wordSize)
    (hwordMachine : wordSize <= machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hsuperWidth : bits.length < 2 ^ superWidth)
    (hblockWidth : bits.length < 2 ^ blockWidth)
    (hquery : 4 <= queryCost)
    (bridge : CanonicalRankWordBridge bits wordSize) :
    TwoLevelPayloadLiveStoredWordRankData bits
      (canonicalSuperRankSampleTables
        bits wordSize blocksPerSuper superWidth hsuperWidth).payload.length
      (canonicalBlockRankSampleTables
        bits wordSize blocksPerSuper blockWidth hblockWidth).payload.length
      queryCost where
  wordSize := wordSize
  wordSize_pos := hword
  wordSize_le_machine := hwordMachine
  blocksPerSuper := blocksPerSuper
  blocksPerSuper_pos := hblocks
  superWidth := superWidth
  blockWidth := blockWidth
  superTrueEntries :=
    canonicalSuperRankEntries true bits wordSize blocksPerSuper
  superFalseEntries :=
    canonicalSuperRankEntries false bits wordSize blocksPerSuper
  blockTrueEntries :=
    canonicalBlockRankEntries true bits wordSize blocksPerSuper
  blockFalseEntries :=
    canonicalBlockRankEntries false bits wordSize blocksPerSuper
  superTables :=
    canonicalSuperRankSampleTables
      bits wordSize blocksPerSuper superWidth hsuperWidth
  blockTables :=
    canonicalBlockRankSampleTables
      bits wordSize blocksPerSuper blockWidth hblockWidth
  bitWords := bridge.bitWords
  superPayload_length := rfl
  blockPayload_length := rfl
  queryCost_ge_four := hquery
  super_present := by
    intro target pos hpos
    simpa using
      (canonicalSuperRankSampleTables_present
        (bits := bits) (wordSize := wordSize)
        (blocksPerSuper := blocksPerSuper)
        (width := superWidth) hsuperWidth target hpos)
  block_present := by
    intro target pos hpos
    simpa using
      (canonicalBlockRankSampleTables_present
        (bits := bits) (wordSize := wordSize)
        (blocksPerSuper := blocksPerSuper)
        (width := blockWidth) hblockWidth target hpos)
  word_present := by
    intro pos hpos
    exact bridge.word_present pos hpos
  rank_parts_exact := by
    intro target pos super delta word hpos hsuper hdelta hwordGet
    apply canonicalRankParts_exact_of_word_local
    · simpa using hsuper
    · simpa using hdelta
    · exact bridge.word_rank_exact target pos word hpos hwordGet

/--
Canonical two-level rank data from ordinary chunks, once the chunk store is
known to contain a word at every queried `pos / wordSize`.
-/
def canonicalTwoLevelRankDataOfChunksPresent
    (bits : List Bool)
    {wordSize blocksPerSuper superWidth blockWidth queryCost : Nat}
    (hword : 0 < wordSize)
    (hwordMachine : wordSize <= machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hsuperWidth : bits.length < 2 ^ superWidth)
    (hblockWidth : bits.length < 2 ^ blockWidth)
    (hquery : 4 <= queryCost)
    (hpresent :
      forall pos,
        pos <= bits.length ->
          exists word,
            (SuccinctSpace.BoundedPayloadWordStore.ofChunks
              bits hword).store.words[pos / wordSize]? = some word) :
    TwoLevelPayloadLiveStoredWordRankData bits
      (canonicalSuperRankSampleTables
        bits wordSize blocksPerSuper superWidth hsuperWidth).payload.length
      (canonicalBlockRankSampleTables
        bits wordSize blocksPerSuper blockWidth hblockWidth).payload.length
      queryCost :=
  canonicalTwoLevelRankDataOfBridge
    bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
      (canonicalRankWordBridgeOfChunks bits hword hpresent)

def canonicalTwoLevelRankDataOfChunksExact
    (bits : List Bool)
    {wordSize blocksPerSuper superWidth blockWidth queryCost : Nat}
    (hword : 0 < wordSize)
    (hwordMachine : wordSize <= machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hsuperWidth : bits.length < 2 ^ superWidth)
    (hblockWidth : bits.length < 2 ^ blockWidth)
    (hquery : 4 <= queryCost) :
    TwoLevelPayloadLiveStoredWordRankData bits
      (canonicalSuperRankSampleTables
        bits wordSize blocksPerSuper superWidth hsuperWidth).payload.length
      (canonicalBlockRankSampleTables
        bits wordSize blocksPerSuper blockWidth hblockWidth).payload.length
      queryCost :=
  canonicalTwoLevelRankDataOfBridge
    bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
      (canonicalRankWordBridgeOfChunksWithSentinel bits hword)

/--
The canonical constructor inherits the full two-level profile theorem once the
chunk-local bridge is supplied.
-/
theorem canonicalTwoLevelRankDataOfBridge_profile
    (bits : List Bool)
    {wordSize blocksPerSuper superWidth blockWidth queryCost : Nat}
    (hword : 0 < wordSize)
    (hwordMachine : wordSize <= machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hsuperWidth : bits.length < 2 ^ superWidth)
    (hblockWidth : bits.length < 2 ^ blockWidth)
    (hquery : 4 <= queryCost)
    (bridge : CanonicalRankWordBridge bits wordSize) :
    let data :=
      canonicalTwoLevelRankDataOfBridge
        bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
          bridge
    data.auxPayload.length =
        (canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper superWidth hsuperWidth).payload.length +
          (canonicalBlockRankSampleTables
            bits wordSize blocksPerSuper blockWidth hblockWidth).payload.length /\
      data.wordSize <= machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= machineWordBits bits.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= queryCost /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos := by
  exact
    (canonicalTwoLevelRankDataOfBridge
      bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
        bridge).profile

theorem canonicalTwoLevelRankDataOfChunksExact_profile
    (bits : List Bool)
    {wordSize blocksPerSuper superWidth blockWidth queryCost : Nat}
    (hword : 0 < wordSize)
    (hwordMachine : wordSize <= machineWordBits bits.length)
    (hblocks : 0 < blocksPerSuper)
    (hsuperWidth : bits.length < 2 ^ superWidth)
    (hblockWidth : bits.length < 2 ^ blockWidth)
    (hquery : 4 <= queryCost) :
    let data :=
      canonicalTwoLevelRankDataOfChunksExact
        bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
    data.auxPayload.length =
        (canonicalSuperRankSampleTables
          bits wordSize blocksPerSuper superWidth hsuperWidth).payload.length +
          (canonicalBlockRankSampleTables
            bits wordSize blocksPerSuper blockWidth hblockWidth).payload.length /\
      data.wordSize <= machineWordBits bits.length /\
      SuccinctSpace.flattenPayloadWords data.bitWords.store.words.toList =
        bits /\
      (forall {word : List Bool},
        List.Mem word data.bitWords.store.words.toList ->
          word.length <= machineWordBits bits.length) /\
      forall target pos,
        (data.rankCosted target pos).cost <= queryCost /\
          (data.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos := by
  exact
    canonicalTwoLevelRankDataOfBridge_profile
      bits hword hwordMachine hblocks hsuperWidth hblockWidth hquery
      (canonicalRankWordBridgeOfChunksWithSentinel bits hword)

structure TwoLevelPayloadLiveStoredWordRankFamily
    (super block : Nat -> Nat) (queryCost : Nat) where
  component :
    forall bits : List Bool,
      TwoLevelPayloadLiveStoredWordRankData
        bits (super bits.length) (block bits.length) queryCost
  super_littleO : SuccinctSpace.LittleOLinear super
  block_littleO : SuccinctSpace.LittleOLinear block

namespace TwoLevelPayloadLiveStoredWordRankFamily

def overhead
    {super block : Nat -> Nat} {queryCost : Nat}
    (_family :
      TwoLevelPayloadLiveStoredWordRankFamily
        super block queryCost) : Nat -> Nat :=
  twoLevelRankOverhead super block

theorem overhead_littleO
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead := by
  exact
    twoLevelRankOverhead_littleO
      family.super_littleO family.block_littleO

theorem constant_query_profile
    {super block : Nat -> Nat} {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankFamily
        super block queryCost) :
    SuccinctSpace.LittleOLinear family.overhead /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length =
          family.overhead bits.length) /\
        ((family.component bits).wordSize <=
          machineWordBits bits.length) /\
        SuccinctSpace.flattenPayloadWords
            (family.component bits).bitWords.store.words.toList = bits /\
        (forall {word : List Bool},
          List.Mem word
              (family.component bits).bitWords.store.words.toList ->
            word.length <= machineWordBits bits.length) /\
        forall target pos,
          ((family.component bits).rankCosted target pos).cost <=
              queryCost /\
            ((family.component bits).rankCosted target pos).erase =
              RMQ.Succinct.rankPrefix target bits pos := by
  constructor
  · exact family.overhead_littleO
  · intro bits
    exact (family.component bits).profile

end TwoLevelPayloadLiveStoredWordRankFamily

/-- Bit budget occupied by the true/false fixed-width rank sample tables. -/
def rankSamplePayloadBudget
    (trueEntries falseEntries : List Nat) (width : Nat) : Nat :=
  trueEntries.length * width + falseEntries.length * width

theorem fixedWidthRankSampleTables_payload_length_eq_budget
    {trueEntries falseEntries : List Nat} {width : Nat}
    (tables :
      SuccinctSpace.FixedWidthRankSampleTables
        trueEntries falseEntries width) :
    tables.payload.length =
      rankSamplePayloadBudget trueEntries falseEntries width := by
  simp [rankSamplePayloadBudget,
    SuccinctSpace.FixedWidthRankSampleTables.payload_length]

theorem fixedWidthRankSampleTables_payload_length_le_sampled
    {trueEntries falseEntries : List Nat} {width slots n : Nat}
    (tables :
      SuccinctSpace.FixedWidthRankSampleTables
        trueEntries falseEntries width)
    (hbudget :
      rankSamplePayloadBudget trueEntries falseEntries width <=
        SuccinctSpace.sampledDirectoryOverhead slots n) :
    tables.payload.length <=
      SuccinctSpace.sampledDirectoryOverhead slots n := by
  rw [fixedWidthRankSampleTables_payload_length_eq_budget tables]
  exact hbudget

/--
A payload-live rank component whose sample payload fits in a sampled directory
envelope.

The existing `PayloadLiveStoredWordRankData` contract already contains the
semantic chunk decomposition (`rank_parts_exact`).  This wrapper only fixes the
budget and family-level theorem target for a later concrete sampled-rank
builder.
-/
structure SampledPayloadLiveStoredWordRankData
    (bits : List Bool) (slots : Nat) where
  overhead : Nat
  data :
    SuccinctSpace.PayloadLiveStoredWordRankData bits overhead
  overhead_le :
    overhead <= SuccinctSpace.sampledDirectoryOverhead slots bits.length

namespace SampledPayloadLiveStoredWordRankData

def auxPayload
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots) :
    List Bool :=
  component.data.auxPayload

def rankCosted
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots)
    (target : Bool) (pos : Nat) :
    RMQ.Costed Nat :=
  component.data.rankCostedClamped target pos

theorem auxPayload_length_le_sampled
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots) :
    component.auxPayload.length <=
      SuccinctSpace.sampledDirectoryOverhead slots bits.length := by
  have hlen := component.data.auxPayload_length
  unfold auxPayload
  rw [hlen]
  exact component.overhead_le

theorem rankCosted_cost_le_three
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots)
    (target : Bool) (pos : Nat) :
    (component.rankCosted target pos).cost <= 3 := by
  exact component.data.rankCostedClamped_cost_le_three target pos

theorem rankCosted_exact
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots)
    (target : Bool) (pos : Nat) :
    (component.rankCosted target pos).erase =
      RMQ.Succinct.rankPrefix target bits pos := by
  exact component.data.rankCostedClamped_exact target pos

theorem profile
    {bits : List Bool} {slots : Nat}
    (component : SampledPayloadLiveStoredWordRankData bits slots) :
    component.auxPayload.length <=
        SuccinctSpace.sampledDirectoryOverhead slots bits.length /\
      SuccinctSpace.flattenPayloadWords
          component.data.bitWords.words.toList = bits /\
      forall target pos,
        (component.rankCosted target pos).cost <= 3 /\
          (component.rankCosted target pos).erase =
            RMQ.Succinct.rankPrefix target bits pos := by
  constructor
  · exact component.auxPayload_length_le_sampled
  · constructor
    · exact component.data.bitWords.payload_eq_words_join
    · intro target pos
      exact ⟨component.rankCosted_cost_le_three target pos,
        component.rankCosted_exact target pos⟩

end SampledPayloadLiveStoredWordRankData

/-- Bounded-envelope sampled rank family. -/
structure SampledPayloadLiveStoredWordRankFamily
    (slots : Nat) where
  component :
    forall bits : List Bool,
      SampledPayloadLiveStoredWordRankData bits slots

namespace SampledPayloadLiveStoredWordRankFamily

theorem bounded_constant_query_profile
    {slots : Nat}
    (family : SampledPayloadLiveStoredWordRankFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length <=
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.component bits).data.bitWords.words.toList = bits /\
          forall target pos,
            ((family.component bits).rankCosted
                target pos).cost <= 3 /\
              ((family.component bits).rankCosted
                  target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos := by
  constructor
  · exact SuccinctSpace.sampledDirectoryOverhead_littleO slots
  · intro bits
    exact (family.component bits).profile

end SampledPayloadLiveStoredWordRankFamily

/--
Exact-envelope version: this can plug directly into exact-length family
interfaces once a concrete sampled-rank builder is available.
-/
structure ExactSampledPayloadLiveStoredWordRankFamily
    (slots : Nat) where
  component :
    forall bits : List Bool,
      SuccinctSpace.PayloadLiveStoredWordRankData bits
        (SuccinctSpace.sampledDirectoryOverhead slots bits.length)

namespace ExactSampledPayloadLiveStoredWordRankFamily

def toSampledFamily
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordRankFamily slots) :
    SampledPayloadLiveStoredWordRankFamily slots where
  component bits :=
    { overhead := SuccinctSpace.sampledDirectoryOverhead slots bits.length
      data := family.component bits
      overhead_le := Nat.le_refl _ }

theorem constant_query_profile
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordRankFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.component bits).auxPayload.length =
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.component bits).bitWords.words.toList = bits /\
          forall target pos,
            ((family.component bits).rankCostedClamped
                target pos).cost <= 3 /\
              ((family.component bits).rankCostedClamped
                  target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos := by
  constructor
  · exact SuccinctSpace.sampledDirectoryOverhead_littleO slots
  · intro bits
    exact (family.component bits).profile

theorem bounded_constant_query_profile
    {slots : Nat}
    (family : ExactSampledPayloadLiveStoredWordRankFamily slots) :
    SuccinctSpace.LittleOLinear
        (SuccinctSpace.sampledDirectoryOverhead slots) /\
      forall bits : List Bool,
        ((family.toSampledFamily.component bits).auxPayload.length <=
            SuccinctSpace.sampledDirectoryOverhead slots bits.length) /\
          SuccinctSpace.flattenPayloadWords
              (family.toSampledFamily.component bits).data.bitWords.words.toList =
            bits /\
          forall target pos,
            ((family.toSampledFamily.component bits).rankCosted
                target pos).cost <= 3 /\
              ((family.toSampledFamily.component bits).rankCosted
                  target pos).erase =
                RMQ.Succinct.rankPrefix target bits pos := by
  exact family.toSampledFamily.bounded_constant_query_profile

end ExactSampledPayloadLiveStoredWordRankFamily

end SuccinctRankProposal
end RMQ
