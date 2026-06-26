import RMQ.Core.SuccinctClose.RelativeRmmMacro.CompactEndpoint

/-!
# Seeded local BP decoder and query helpers

Split implementation layer for the relative-rmM BP close/LCA macro. Public
declarations live in the canonical `RMQ.SuccinctClose` namespace.
-/

namespace RMQ
namespace SuccinctClose

open SuccinctSpace

/-- Auxiliary overhead reserved for the compact BP close/LCA directory.

The local endpoint and same-block work below is charged as bounded BP-word
primitive work over the base BP payload, so the auxiliary close overhead is the
compact two-level interior navigator payload.
-/
def compactBPCloseOverhead (n : Nat) : Nat :=
  if n < 2 ^ 128 then
    natListMax
      ((Cartesian.shapesOfSize n).map fun shape =>
        concreteBPRelativeRmmInteriorDirectoryPayloadLength shape)
  else
    concreteBPRelativeRmmInteriorOverhead n

theorem compactBPCloseOverhead_littleO :
    LittleOLinear compactBPCloseOverhead := by
  exact
    LittleOLinear.of_eventually_le
      concreteBPRelativeRmmInteriorOverhead_littleO
      ⟨2 ^ 128, by
        intro n hn
        have hnot : ¬ n < 2 ^ 128 := by omega
        simp [compactBPCloseOverhead, hnot]⟩

def concreteCompactBPCloseQueryCost : Nat :=
  10 + concreteBPRelativeRmmInteriorQueryCost

def concreteCompactBPCloseQueryCostWithRankSeed
    (rankCost : Nat) : Nat :=
  8 + 2 * rankCost + concreteBPRelativeRmmInteriorQueryCost

def bpCodeWordReadsAt
    (shape : Cartesian.CartesianShape) (index : Nat) : List (List Bool) :=
  payloadWordReadOfGet?
    (SuccinctSpace.chunkPayloadWords
      (SuccinctRank.machineWordBits shape.bpCode.length)
      shape.bpCode).toArray
    index

theorem bpCodeWordReadsAt_length_le_machine
    (shape : Cartesian.CartesianShape) (index : Nat)
    {word : List Bool}
    (hmem : word ∈ bpCodeWordReadsAt shape index) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold bpCodeWordReadsAt at hmem
  exact payloadWordReadOfGet?_length_le
    (by
      intro stored hget
      have hmemWords :
          stored ∈
            SuccinctSpace.chunkPayloadWords
              (SuccinctRank.machineWordBits shape.bpCode.length)
              shape.bpCode := by
        have hlist :
            (SuccinctSpace.chunkPayloadWords
              (SuccinctRank.machineWordBits shape.bpCode.length)
              shape.bpCode)[index]? = some stored := by
          simpa [Array.getElem?_toList] using hget
        exact List.mem_of_getElem? hlist
      exact SuccinctSpace.chunkPayloadWords_word_length_le
        (SuccinctRank.machineWordBits shape.bpCode.length)
        hmemWords)
    hmem

theorem list_take_add_eq_take_append_drop_take
    {α : Type} (xs : List α) (a b : Nat) :
    xs.take (a + b) = xs.take a ++ (xs.drop a).take b := by
  induction a generalizing xs with
  | zero =>
      simp
  | succ a ih =>
      cases xs with
      | nil =>
          simp
      | cons x xs =>
          simp [Nat.succ_add, ih]

theorem flatten_bpCodeWordReadsAt_eq_take_drop
    (shape : Cartesian.CartesianShape) (index : Nat) :
    SuccinctSpace.flattenPayloadWords (bpCodeWordReadsAt shape index) =
      (shape.bpCode.drop
        (index * SuccinctRank.machineWordBits shape.bpCode.length)).take
          (SuccinctRank.machineWordBits shape.bpCode.length) := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let words := SuccinctSpace.chunkPayloadWords wordSize shape.bpCode
  have hword : 0 < wordSize := by
    simpa [wordSize] using
      SuccinctRank.machineWordBits_pos shape.bpCode.length
  unfold bpCodeWordReadsAt payloadWordReadOfGet?
  cases hget : words.toArray[index]? with
  | some word =>
      have hlist : words[index]? = some word := by
        simpa [words, Array.getElem?_toList] using hget
      have hwordEq :=
        SuccinctSpace.chunkPayloadWords_get?_eq_take_drop hlist
      simp [SuccinctSpace.flattenPayloadWords, wordSize, hwordEq]
  | none =>
      by_cases hlt : index * wordSize < shape.bpCode.length
      · rcases
          SuccinctSpace.chunkPayloadWords_get?_some_of_mul_lt
            (wordSize := wordSize) hword
            (payload := shape.bpCode) (i := index) hlt with
          ⟨word, hlist⟩
        have harray : words.toArray[index]? = some word := by
          simpa [words, Array.getElem?_toList] using hlist
        rw [hget] at harray
        cases harray
      · have hdropLen :
            (shape.bpCode.drop (index * wordSize)).length = 0 := by
          rw [List.length_drop]
          omega
        cases hdrop : shape.bpCode.drop (index * wordSize) with
        | nil =>
            simp [SuccinctSpace.flattenPayloadWords]
        | cons bit rest =>
            simp [hdrop] at hdropLen

/--
The fixed local BP-word budget used by same-block and endpoint-fringe
primitives.  Canonical blocks have logarithmic width, so four consecutive
machine chunks are a conservative constant-width local window for the current
model surface; exactness is stated by the local primitive theorems below.
-/
def localBPBlockWordsRead
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : List (List Bool) :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  bpCodeWordReadsAt shape firstWord ++
    bpCodeWordReadsAt shape (firstWord + 1) ++
      bpCodeWordReadsAt shape (firstWord + 2) ++
        bpCodeWordReadsAt shape (firstWord + 3)

/-- First global BP bit position covered by the local four-word window. -/
def localBPWindowBase
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  firstWord * wordSize

/--
Contiguous bit view of the local BP window.

The query still charges the four payload words listed by `localBPBlockWordsRead`;
this proof-facing view exposes the covered slice so the seeded decoder can be
stated without calling the semantic local helpers.
-/
def localBPWindowBits
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : List Bool :=
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let base := localBPWindowBase shape blockSize close
  (shape.bpCode.drop base).take (4 * wordSize)

/-- The proof-facing local BP window is exactly the flattened charged words. -/
theorem localBPWindowBits_eq_flatten_localBPBlockWordsRead
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    localBPWindowBits shape blockSize close =
      SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close) := by
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let firstWord :=
    blockStartOf blockSize (blockOfClose blockSize close) / wordSize
  have h0 := flatten_bpCodeWordReadsAt_eq_take_drop shape firstWord
  have h1 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 1)
  have h2 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 2)
  have h3 := flatten_bpCodeWordReadsAt_eq_take_drop shape (firstWord + 3)
  have hsplit1 :
      (shape.bpCode.drop (firstWord * wordSize)).take (4 * wordSize) =
        (shape.bpCode.drop (firstWord * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 1) * wordSize)).take
            (3 * wordSize) := by
    have hfour : 4 * wordSize = wordSize + 3 * wordSize := by omega
    rw [hfour]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show firstWord * wordSize + wordSize =
      (firstWord + 1) * wordSize by
        rw [Nat.add_mul]
        simp]
  have hsplit2 :
      (shape.bpCode.drop ((firstWord + 1) * wordSize)).take
          (3 * wordSize) =
        (shape.bpCode.drop ((firstWord + 1) * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 2) * wordSize)).take
            (2 * wordSize) := by
    have hthree : 3 * wordSize = wordSize + 2 * wordSize := by omega
    rw [hthree]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show (firstWord + 1) * wordSize + wordSize =
      (firstWord + 2) * wordSize by
        rw [show firstWord + 2 = (firstWord + 1) + 1 by omega]
        simp [Nat.add_mul, Nat.add_comm]]
  have hsplit3 :
      (shape.bpCode.drop ((firstWord + 2) * wordSize)).take
          (2 * wordSize) =
        (shape.bpCode.drop ((firstWord + 2) * wordSize)).take wordSize ++
          (shape.bpCode.drop ((firstWord + 3) * wordSize)).take wordSize := by
    have htwo : 2 * wordSize = wordSize + wordSize := by omega
    rw [htwo]
    rw [list_take_add_eq_take_append_drop_take]
    simp only [List.drop_drop]
    rw [show (firstWord + 2) * wordSize + wordSize =
      (firstWord + 3) * wordSize by
        rw [show firstWord + 3 = (firstWord + 2) + 1 by omega]
        simp [Nat.add_mul, Nat.add_comm]]
  have hwindow :
      localBPWindowBits shape blockSize close =
        (shape.bpCode.drop (firstWord * wordSize)).take
          (4 * wordSize) := by
    simp [localBPWindowBits, localBPWindowBase, wordSize, firstWord]
  have h0w :
      SuccinctSpace.flattenPayloadWords (bpCodeWordReadsAt shape firstWord) =
        (shape.bpCode.drop (firstWord * wordSize)).take wordSize := by
    simpa [wordSize] using h0
  have h1w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (1 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 1) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h1
  have h2w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (2 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 2) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h2
  have h3w :
      SuccinctSpace.flattenPayloadWords
          (bpCodeWordReadsAt shape (3 + firstWord)) =
        (shape.bpCode.drop ((firstWord + 3) * wordSize)).take wordSize := by
    simpa [wordSize, Nat.add_comm] using h3
  rw [hwindow, hsplit1, hsplit2, hsplit3]
  simp [localBPBlockWordsRead, SuccinctSpace.flattenPayloadWords_append,
    h0w, h1w, h2w, h3w, wordSize, firstWord, Nat.add_comm]

/-- Read a global BP bit through the local window when it falls in range. -/
def localBPWindowGet?
    (shape : Cartesian.CartesianShape)
    (blockSize close globalPos : Nat) : Option Bool :=
  let base := localBPWindowBase shape blockSize close
  if base <= globalPos then
    (localBPWindowBits shape blockSize close)[globalPos - base]?
  else
    none

theorem localBPWindowBits_length_le
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPWindowBits shape blockSize close).length <=
      4 * SuccinctRank.machineWordBits shape.bpCode.length := by
  simp [localBPWindowBits, List.length_take]
  exact Nat.min_le_left _ _

/--
When the block size is zero, all closes have the same `blockOfClose`, so the
same-block test alone gives no endpoint coverage guarantee for a four-word
local BP window.
-/
theorem zeroBlockSameBlock_does_not_imply_localBPWindowCoverage
    (shape : Cartesian.CartesianShape)
    {rightClose : Nat}
    (hwide :
      4 * SuccinctRank.machineWordBits shape.bpCode.length <
        rightClose + 1) :
    blockOfClose 0 0 = blockOfClose 0 rightClose /\
      ¬ rightClose + 1 <=
        localBPWindowBase shape 0 0 +
          (localBPWindowBits shape 0 0).length := by
  constructor
  · simp [blockOfClose]
  · intro hcovered
    have hlen := localBPWindowBits_length_le shape 0 0
    have hbase : localBPWindowBase shape 0 0 = 0 := by
      simp [localBPWindowBase, blockStartOf]
    omega

theorem localBPWindowGet?_eq_bpCode_get?
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hcovered :
      localBPWindowBase shape blockSize close <= globalPos /\
        globalPos <
          localBPWindowBase shape blockSize close +
            4 * SuccinctRank.machineWordBits shape.bpCode.length) :
    localBPWindowGet? shape blockSize close globalPos =
      shape.bpCode[globalPos]? := by
  unfold localBPWindowGet? localBPWindowBits
  simp only [hcovered.1, ↓reduceIte]
  have hoff :
      globalPos - localBPWindowBase shape blockSize close <
        4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    omega
  rw [List.getElem?_take]
  simp [hoff]
  have hpos :
      localBPWindowBase shape blockSize close +
          (globalPos - localBPWindowBase shape blockSize close) =
        globalPos := by
    omega
  rw [hpos]

/--
Reading a bit from the flattened charged local BP words agrees with the global
BP code whenever the requested position lies in the four-word local window.
-/
theorem localBPBlockWordsRead_get?_eq_bpCode_get?
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hcovered :
      localBPWindowBase shape blockSize close <= globalPos /\
        globalPos <
          localBPWindowBase shape blockSize close +
            4 * SuccinctRank.machineWordBits shape.bpCode.length) :
    (SuccinctSpace.flattenPayloadWords
        (localBPBlockWordsRead shape blockSize close))[
          globalPos - localBPWindowBase shape blockSize close]? =
      shape.bpCode[globalPos]? := by
  have hget :=
    localBPWindowGet?_eq_bpCode_get?
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := globalPos) hcovered
  simpa [localBPWindowGet?, hcovered.1,
    localBPWindowBits_eq_flatten_localBPBlockWordsRead shape blockSize close]
    using hget

theorem localBPWindowBits_end_le_bpCode_length
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    localBPWindowBase shape blockSize close +
        (localBPWindowBits shape blockSize close).length <=
      shape.bpCode.length := by
  simp [localBPWindowBits, List.length_take, List.length_drop]
  omega

theorem localBPWindowBase_le_blockStart
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    localBPWindowBase shape blockSize close <=
      blockStartOf blockSize (blockOfClose blockSize close) := by
  unfold localBPWindowBase
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let start := blockStartOf blockSize (blockOfClose blockSize close)
  have hdiv := Nat.div_add_mod start wordSize
  have hcomm : start / wordSize * wordSize =
      wordSize * (start / wordSize) := by
    exact Nat.mul_comm (start / wordSize) wordSize
  change start / wordSize * wordSize <= start
  omega

theorem localBPWindow_block_end_le_four_words
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hblockSize :
      blockSize <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length) :
    blockStartOf blockSize (blockOfClose blockSize close) + blockSize <=
      localBPWindowBase shape blockSize close +
        4 * SuccinctRank.machineWordBits shape.bpCode.length := by
  unfold localBPWindowBase
  let wordSize := SuccinctRank.machineWordBits shape.bpCode.length
  let start := blockStartOf blockSize (blockOfClose blockSize close)
  have hword : 0 < wordSize := by
    simpa [wordSize] using
      SuccinctRank.machineWordBits_pos shape.bpCode.length
  have hdiv := Nat.div_add_mod start wordSize
  have hmod := Nat.mod_lt start hword
  have hcomm : start / wordSize * wordSize =
      wordSize * (start / wordSize) := by
    exact Nat.mul_comm (start / wordSize) wordSize
  change start + blockSize <= start / wordSize * wordSize + 4 * wordSize
  omega

theorem localBPWindowBits_covers_of_le_width
    {shape : Cartesian.CartesianShape}
    {blockSize close pos : Nat}
    (hbasePos :
      localBPWindowBase shape blockSize close <= pos)
    (hposLen : pos <= shape.bpCode.length)
    (hposWidth :
      pos <=
        localBPWindowBase shape blockSize close +
          4 * SuccinctRank.machineWordBits shape.bpCode.length) :
    pos <=
      localBPWindowBase shape blockSize close +
        (localBPWindowBits shape blockSize close).length := by
  let base := localBPWindowBase shape blockSize close
  let width := 4 * SuccinctRank.machineWordBits shape.bpCode.length
  have hbaseLen : base <= shape.bpCode.length := by omega
  have hoffLen : pos - base <= shape.bpCode.length - base := by omega
  have hoffWidth : pos - base <= width := by omega
  have hoff :
      pos - base <= Nat.min width (shape.bpCode.length - base) :=
    Nat.le_min.mpr ⟨hoffWidth, hoffLen⟩
  have hposEq : base + (pos - base) = pos := by omega
  simp [localBPWindowBits, List.length_take, List.length_drop]
  omega

/-- Absolute BP excess at the base of the local window. -/
def localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Nat :=
  bpExcessAt shape (localBPWindowBase shape blockSize close)

/--
Recover the base excess from a stored close-rank seed at the same prefix
position.  When the base is in range and the seed is the false-rank at the
base, this is equal to `localBPSeedExcess`.
-/
def localBPSeedFromRankFalse
    (base falseRankAtBase : Nat) : Nat :=
  base - 2 * falseRankAtBase

theorem rankPrefix_true_add_false_eq_of_le_length
    {bits : List Bool} {limit : Nat}
    (hlimit : limit <= bits.length) :
    Succinct.rankPrefix true bits limit +
        Succinct.rankPrefix false bits limit =
      limit := by
  induction bits generalizing limit with
  | nil =>
      have hzero : limit = 0 := by
        simpa using hlimit
      subst limit
      simp [Succinct.rankPrefix]
  | cons bit rest ih =>
      cases limit with
      | zero =>
          simp [Succinct.rankPrefix]
      | succ limit =>
          have htail : limit <= rest.length := by
            simp at hlimit
            omega
          have hrec := ih htail
          cases bit <;> simp [Succinct.rankPrefix] <;> omega

theorem localBPSeedFromRankFalse_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    localBPSeedFromRankFalse
        (localBPWindowBase shape blockSize close)
        (Succinct.rankPrefix false shape.bpCode
          (localBPWindowBase shape blockSize close)) =
      localBPSeedExcess shape blockSize close := by
  unfold localBPSeedFromRankFalse localBPSeedExcess bpExcessAt
  have hsum :=
    rankPrefix_true_add_false_eq_of_le_length
      (bits := shape.bpCode)
      (limit := localBPWindowBase shape blockSize close) hbase
  have hnonneg := bpExcessAt_prefix_nonnegative shape hbase
  omega

/-- Explicit modeled read of the false-rank seed at the local BP window base. -/
def localBPSeedFromRankFalseCosted
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) : Costed Nat :=
  let base := localBPWindowBase shape blockSize close
  { value :=
      localBPSeedFromRankFalse base
        (Succinct.rankPrefix false shape.bpCode base)
    cost := 1 }

theorem localBPSeedFromRankFalseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat) :
    (localBPSeedFromRankFalseCosted shape blockSize close).cost <= 1 := by
  simp [localBPSeedFromRankFalseCosted]

theorem localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    (localBPSeedFromRankFalseCosted shape blockSize close).erase =
      localBPSeedExcess shape blockSize close := by
  simpa [localBPSeedFromRankFalseCosted, Costed.erase] using
    localBPSeedFromRankFalse_eq_localBPSeedExcess
      shape blockSize close hbase

/-- Seed read routed through a supplied rank-close callback. -/
def localBPSeedFromRankCloseCosted
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat) : Costed Nat :=
  let base := localBPWindowBase shape blockSize close
  Costed.map (fun rankFalse => localBPSeedFromRankFalse base rankFalse)
    (rankCloseCosted base)

theorem localBPSeedFromRankCloseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize close).cost <=
      rankCost := by
  unfold localBPSeedFromRankCloseCosted
  simp [Costed.map, Costed.bind, Costed.pure]
  exact hrankCost (localBPWindowBase shape blockSize close)

theorem localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize close : Nat)
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length) :
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize close).erase =
      localBPSeedExcess shape blockSize close := by
  let base := localBPWindowBase shape blockSize close
  have hrank :
      (rankCloseCosted base).value =
        Succinct.rankPrefix false shape.bpCode base := by
    simpa [Costed.erase] using hrankExact base
  have hseed :=
    localBPSeedFromRankFalse_eq_localBPSeedExcess
      shape blockSize close hbase
  simpa [localBPSeedFromRankCloseCosted, Costed.map, Costed.bind,
    Costed.pure, Costed.erase, base, hrank] using hseed

/--
The local BP bits alone do not determine the absolute BP-excess seed at the
window base.

The fringe helpers return absolute `(excess, prefixPos)` candidates so that
they can be merged with the interior candidate. Two identical local windows can
have different prefix excess before the window, hence a decoder that is given
only `localBPWindowBits` still needs a charged/stored seed such as base excess
or equivalent rank metadata.
-/
theorem localBPWindowBits_alone_does_not_determine_base_excess :
    exists prefixA prefixB window : List Bool,
      List.take window.length
          (List.drop prefixA.length (prefixA ++ window)) =
        List.take window.length
          (List.drop prefixB.length (prefixB ++ window)) /\
      (Succinct.rankPrefix true (prefixA ++ window) prefixA.length -
          Succinct.rankPrefix false (prefixA ++ window) prefixA.length) ≠
        (Succinct.rankPrefix true (prefixB ++ window) prefixB.length -
          Succinct.rankPrefix false (prefixB ++ window) prefixB.length) := by
  refine ⟨[], [true], [false], ?_, ?_⟩
  · decide
  · decide

def localBPSeededExcessAt
    (window : List Bool) (seed base globalPos : Nat) : Nat :=
  let sample := Nat.min globalPos (base + window.length)
  seed +
      Succinct.rankPrefix true window (sample - base) -
    Succinct.rankPrefix false window (sample - base)

theorem localBPSeededExcessAt_eq_bpExcessAt
    {shape : Cartesian.CartesianShape}
    {blockSize close globalPos : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hpos :
      localBPWindowBase shape blockSize close <= globalPos)
    (hcovered :
      globalPos <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededExcessAt
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        globalPos =
      bpExcessAt shape globalPos := by
  let base := localBPWindowBase shape blockSize close
  let width := 4 * SuccinctRank.machineWordBits shape.bpCode.length
  have hend :
      base + (localBPWindowBits shape blockSize close).length <=
        shape.bpCode.length := by
    simpa [base] using
      localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
  have hposLen : globalPos <= shape.bpCode.length := by
    omega
  have hsample :
      Nat.min globalPos
          (base + (localBPWindowBits shape blockSize close).length) =
        globalPos := by
    exact Nat.min_eq_left (by simpa [base] using hcovered)
  have hsample' :
      Nat.min globalPos
          (localBPWindowBase shape blockSize close +
            (localBPWindowBits shape blockSize close).length) =
        globalPos := by
    simpa [base] using hsample
  have hoffWindow :
      globalPos - base <=
        (localBPWindowBits shape blockSize close).length := by
    omega
  have htrueLocal :
      Succinct.rankPrefix true
          (localBPWindowBits shape blockSize close)
          (globalPos - base) =
        Succinct.rankPrefix true shape.bpCode globalPos -
          Succinct.rankPrefix true shape.bpCode base := by
    have htake :
        Succinct.rankPrefix true
            ((shape.bpCode.drop base).take width)
            (globalPos - base) =
          Succinct.rankPrefix true (shape.bpCode.drop base)
            (globalPos - base) := by
      apply Succinct.rankPrefix_take_eq_of_le
      simpa [localBPWindowBits, base, width] using hoffWindow
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le
        true shape.bpCode hpos hposLen
    simpa [localBPWindowBits, base, width] using htake.trans hdrop
  have hfalseLocal :
      Succinct.rankPrefix false
          (localBPWindowBits shape blockSize close)
          (globalPos - base) =
        Succinct.rankPrefix false shape.bpCode globalPos -
          Succinct.rankPrefix false shape.bpCode base := by
    have htake :
        Succinct.rankPrefix false
            ((shape.bpCode.drop base).take width)
            (globalPos - base) =
          Succinct.rankPrefix false (shape.bpCode.drop base)
            (globalPos - base) := by
      apply Succinct.rankPrefix_take_eq_of_le
      simpa [localBPWindowBits, base, width] using hoffWindow
    have hdrop :=
      Succinct.rankPrefix_drop_eq_sub_of_le
        false shape.bpCode hpos hposLen
    simpa [localBPWindowBits, base, width] using htake.trans hdrop
  have hbaseNonneg := bpExcessAt_prefix_nonnegative shape hbase
  have hposNonneg := bpExcessAt_prefix_nonnegative shape hposLen
  have htrueMono :
      Succinct.rankPrefix true shape.bpCode base <=
        Succinct.rankPrefix true shape.bpCode globalPos :=
    Succinct.rankPrefix_mono_limit true shape.bpCode hpos
  have hfalseMono :
      Succinct.rankPrefix false shape.bpCode base <=
        Succinct.rankPrefix false shape.bpCode globalPos :=
    Succinct.rankPrefix_mono_limit false shape.bpCode hpos
  have hbaseNonneg' :
      Succinct.rankPrefix false shape.bpCode base <=
        Succinct.rankPrefix true shape.bpCode base := by
    simpa [base] using hbaseNonneg
  have hseed :
      localBPSeedExcess shape blockSize close =
        Succinct.rankPrefix true shape.bpCode base -
          Succinct.rankPrefix false shape.bpCode base := by
    simp [localBPSeedExcess, bpExcessAt, base]
  unfold localBPSeededExcessAt bpExcessAt
  simp [hsample', base, hseed, htrueLocal, hfalseLocal]
  change
    (Succinct.rankPrefix true shape.bpCode base -
          Succinct.rankPrefix false shape.bpCode base) +
        (Succinct.rankPrefix true shape.bpCode globalPos -
          Succinct.rankPrefix true shape.bpCode base) -
      (Succinct.rankPrefix false shape.bpCode globalPos -
        Succinct.rankPrefix false shape.bpCode base) =
    Succinct.rankPrefix true shape.bpCode globalPos -
      Succinct.rankPrefix false shape.bpCode globalPos
  omega

def localBPSeededBetterPrefixPos
    (window : List Bool) (seed base left right : Nat) : Nat :=
  if localBPSeededExcessAt window seed base right <
      localBPSeededExcessAt window seed base left then
    right
  else
    left

theorem localBPSeededBetterPrefixPos_bounds
    {window : List Bool} {seed base left right : Nat}
    (hleftBase : base <= left)
    (hleftCovered : left <= base + window.length)
    (hrightBase : base <= right)
    (hrightCovered : right <= base + window.length) :
    base <= localBPSeededBetterPrefixPos window seed base left right /\
      localBPSeededBetterPrefixPos window seed base left right <=
        base + window.length := by
  unfold localBPSeededBetterPrefixPos
  by_cases hlt :
      localBPSeededExcessAt window seed base right <
        localBPSeededExcessAt window seed base left
  · simp [hlt, hrightBase, hrightCovered]
  · simp [hlt, hleftBase, hleftCovered]

theorem localBPSeededBetterPrefixPos_eq_bpBetterArgMinPrefixPos
    {shape : Cartesian.CartesianShape}
    {blockSize close left right : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hleftBase :
      localBPWindowBase shape blockSize close <= left)
    (hleftCovered :
      left <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length)
    (hrightBase :
      localBPWindowBase shape blockSize close <= right)
    (hrightCovered :
      right <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededBetterPrefixPos
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        left right =
      bpBetterArgMinPrefixPos shape left right := by
  have hleft :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := left) hbase hleftBase hleftCovered
  have hright :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos := right) hbase hrightBase hrightCovered
  unfold localBPSeededBetterPrefixPos bpBetterArgMinPrefixPos
  rw [hleft, hright]

def localBPSeededPrefixRangeArgMinPrefixPosFrom
    (window : List Bool) (seed base : Nat) :
    Nat -> Nat -> Nat -> Nat
  | _pos, 0, best => best
  | pos, steps + 1, best =>
      let sample := Nat.min pos (base + window.length)
      let best' := localBPSeededBetterPrefixPos window seed base best sample
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
        (pos + 1) steps best'

theorem localBPSeededPrefixRangeArgMinPrefixPosFrom_bounds
    {window : List Bool} {seed base pos steps best : Nat}
    (hposBase : base <= pos)
    (hcovered : pos + steps <= base + window.length + 1)
    (hbestBase : base <= best)
    (hbestCovered : best <= base + window.length) :
    base <=
        localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
          pos steps best /\
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
          pos steps best <=
        base + window.length := by
  induction steps generalizing pos best with
  | zero =>
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        hbestBase, hbestCovered]
  | succ steps ih =>
      have hposCovered : pos <= base + window.length := by
        omega
      have hsample :
          Nat.min pos (base + window.length) = pos := by
        exact Nat.min_eq_left hposCovered
      have hbetterBounds :=
        localBPSeededBetterPrefixPos_bounds
          (window := window) (seed := seed) (base := base)
          (left := best) (right := pos)
          hbestBase hbestCovered hposBase hposCovered
      have htail :
          pos + 1 + steps <= base + window.length + 1 := by
        omega
      simpa [localBPSeededPrefixRangeArgMinPrefixPosFrom, hsample] using
        ih (pos := pos + 1)
          (best := localBPSeededBetterPrefixPos window seed base best pos)
          (by omega) htail hbetterBounds.1 hbetterBounds.2

theorem localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_bpPrefixRangeArgMinPrefixPosFrom
    {shape : Cartesian.CartesianShape}
    {blockSize close pos steps best : Nat}
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hposBase :
      localBPWindowBase shape blockSize close <= pos)
    (hcovered :
      pos + steps <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1)
    (hbestBase :
      localBPWindowBase shape blockSize close <= best)
    (hbestCovered :
      best <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length) :
    localBPSeededPrefixRangeArgMinPrefixPosFrom
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        pos steps best =
      bpPrefixRangeArgMinPrefixPosFrom shape pos steps best := by
  induction steps generalizing pos best with
  | zero =>
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom]
  | succ steps ih =>
      let base := localBPWindowBase shape blockSize close
      let window := localBPWindowBits shape blockSize close
      have hend :
          base + window.length <= shape.bpCode.length := by
        simpa [base, window] using
          localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
      have hcoveredLocal :
          pos + (steps + 1) <= base + window.length + 1 := by
        simpa [base, window, Nat.add_assoc] using hcovered
      have hbestBaseLocal : base <= best := by
        simpa [base] using hbestBase
      have hbestCoveredLocal : best <= base + window.length := by
        simpa [base, window] using hbestCovered
      have hposCovered : pos <= base + window.length := by
        omega
      have hposLen : pos <= shape.bpCode.length := by
        omega
      have hsampleLocal :
          Nat.min pos (base + window.length) = pos :=
        Nat.min_eq_left hposCovered
      have hsampleSemantic :
          Nat.min pos shape.bpCode.length = pos :=
        Nat.min_eq_left hposLen
      have hbetter :=
        localBPSeededBetterPrefixPos_eq_bpBetterArgMinPrefixPos
          (shape := shape) (blockSize := blockSize) (close := close)
          (left := best) (right := pos)
          hbase hbestBase hbestCovered
          (by simpa [base] using hposBase)
          (by simpa [base, window] using hposCovered)
      have hbest'Base :
          base <= bpBetterArgMinPrefixPos shape best pos := by
        unfold bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt]
          exact hposBase
        · simp [hlt]
          exact hbestBaseLocal
      have hbest'Covered :
          bpBetterArgMinPrefixPos shape best pos <= base + window.length := by
        unfold bpBetterArgMinPrefixPos
        by_cases hlt : bpExcessAt shape pos < bpExcessAt shape best
        · simp [hlt, hposCovered]
        · simp [hlt]
          exact hbestCoveredLocal
      have htail :
          pos + 1 + steps <= base + window.length + 1 := by
        omega
      have hrec :=
        ih (pos := pos + 1)
          (best := bpBetterArgMinPrefixPos shape best pos)
          (by simpa [base] using (show base <= pos + 1 by omega))
          (by simpa [base, window] using htail)
          (by simpa [base] using hbest'Base)
          (by simpa [base, window] using hbest'Covered)
      simp [localBPSeededPrefixRangeArgMinPrefixPosFrom,
        bpPrefixRangeArgMinPrefixPosFrom, base, window, hsampleLocal,
        hsampleSemantic, hbetter, hrec]

def localBPSeededPrefixRangeArgMinPrefixPos
    (window : List Bool) (seed base start count : Nat) : Nat :=
  match count with
  | 0 => Nat.min start (base + window.length)
  | steps + 1 =>
      localBPSeededPrefixRangeArgMinPrefixPosFrom window seed base
        (start + 1) steps (Nat.min start (base + window.length))

def localBPSeededPrefixRangeMinExcess
    (window : List Bool) (seed base start count : Nat) : Nat :=
  localBPSeededExcessAt window seed base
    (localBPSeededPrefixRangeArgMinPrefixPos window seed base start count)

theorem localBPSeededPrefixRangeArgMinPrefixPos_bounds_of_pos
    {window : List Bool} {seed base start count : Nat}
    (hcount : 0 < count)
    (hstartBase : base <= start)
    (hcovered : start + count <= base + window.length + 1) :
    base <=
        localBPSeededPrefixRangeArgMinPrefixPos window seed base
          start count /\
      localBPSeededPrefixRangeArgMinPrefixPos window seed base
          start count <=
        base + window.length := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      have hstartCovered : start <= base + window.length := by
        omega
      have hsampleLocal :
          Nat.min start (base + window.length) = start :=
        Nat.min_eq_left hstartCovered
      have htail :
          start + 1 + steps <= base + window.length + 1 := by
        omega
      simpa [localBPSeededPrefixRangeArgMinPrefixPos, hsampleLocal] using
        localBPSeededPrefixRangeArgMinPrefixPosFrom_bounds
          (window := window) (seed := seed) (base := base)
          (pos := start + 1) (steps := steps) (best := start)
          (by omega) htail hstartBase hstartCovered

theorem localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
    {shape : Cartesian.CartesianShape}
    {blockSize close start count : Nat}
    (hcount : 0 < count)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize close <= start)
    (hcovered :
      start + count <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1) :
    localBPSeededPrefixRangeArgMinPrefixPos
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        start count =
      bpPrefixRangeArgMinPrefixPos shape start count := by
  cases count with
  | zero =>
      omega
  | succ steps =>
      let base := localBPWindowBase shape blockSize close
      let window := localBPWindowBits shape blockSize close
      have hend :
          base + window.length <= shape.bpCode.length := by
        simpa [base, window] using
          localBPWindowBits_end_le_bpCode_length shape blockSize close hbase
      have hcoveredLocal :
          start + (steps + 1) <= base + window.length + 1 := by
        simpa [base, window, Nat.add_assoc] using hcovered
      have hstartCovered : start <= base + window.length := by
        omega
      have hstartLen : start <= shape.bpCode.length := by
        omega
      have hsampleLocal :
          Nat.min start (base + window.length) = start :=
        Nat.min_eq_left hstartCovered
      have hsampleSemantic :
          Nat.min start shape.bpCode.length = start :=
        Nat.min_eq_left hstartLen
      have htail :
          start + 1 + steps <= base + window.length + 1 := by
        omega
      have hfrom :=
        localBPSeededPrefixRangeArgMinPrefixPosFrom_eq_bpPrefixRangeArgMinPrefixPosFrom
          (shape := shape) (blockSize := blockSize) (close := close)
          (pos := start + 1) (steps := steps) (best := start)
          hbase
          (by simpa [base] using (show base <= start + 1 by omega))
          (by simpa [base, window] using htail)
          hstartBase
          (by simpa [base, window] using hstartCovered)
      simp [localBPSeededPrefixRangeArgMinPrefixPos,
        bpPrefixRangeArgMinPrefixPos, base, window, hsampleLocal,
        hsampleSemantic, hfrom]

theorem localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
    {shape : Cartesian.CartesianShape}
    {blockSize close start count : Nat}
    (hcount : 0 < count)
    (hbase :
      localBPWindowBase shape blockSize close <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize close <= start)
    (hcovered :
      start + count <=
        localBPWindowBase shape blockSize close +
          (localBPWindowBits shape blockSize close).length + 1) :
    localBPSeededPrefixRangeMinExcess
        (localBPWindowBits shape blockSize close)
        (localBPSeedExcess shape blockSize close)
        (localBPWindowBase shape blockSize close)
        start count =
      bpPrefixRangeMinExcess shape start count := by
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := close)
      (start := start) (count := count)
      hcount hbase hstartBase hcovered
  have hbounds :=
    localBPSeededPrefixRangeArgMinPrefixPos_bounds_of_pos
      (window := localBPWindowBits shape blockSize close)
      (seed := localBPSeedExcess shape blockSize close)
      (base := localBPWindowBase shape blockSize close)
      (start := start) (count := count)
      hcount hstartBase hcovered
  have hexcess :=
    localBPSeededExcessAt_eq_bpExcessAt
      (shape := shape) (blockSize := blockSize) (close := close)
      (globalPos :=
        localBPSeededPrefixRangeArgMinPrefixPos
          (localBPWindowBits shape blockSize close)
          (localBPSeedExcess shape blockSize close)
          (localBPWindowBase shape blockSize close)
          start count)
      hbase hbounds.1 hbounds.2
  simpa [localBPSeededPrefixRangeMinExcess, bpPrefixRangeMinExcess,
    harg] using hexcess

def localBPLeftFringeCandidateSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) : Costed (Option (Nat × Nat)) :=
  let window := localBPWindowBits shape blockSize leftClose
  let base := localBPWindowBase shape blockSize leftClose
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  { value :=
      some
        (localBPSeededPrefixRangeMinExcess window seed base
          (leftClose + 1) count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base
            (leftClose + 1) count)
    cost := 4 }

def localBPRightFringeCandidateSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) : Costed (Option (Nat × Nat)) :=
  let window := localBPWindowBits shape blockSize rightClose
  let base := localBPWindowBase shape blockSize rightClose
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  { value :=
      some
        (localBPSeededPrefixRangeMinExcess window seed base start count,
          localBPSeededPrefixRangeArgMinPrefixPos window seed base start count)
    cost := 4 }

theorem localBPBlockWordsRead_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize close : Nat)
    {word : List Bool}
    (hmem : word ∈ localBPBlockWordsRead shape blockSize close) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  simp [localBPBlockWordsRead, List.mem_append] at hmem
  rcases hmem with hmem | hmem | hmem | hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem
  · exact bpCodeWordReadsAt_length_le_machine shape _ hmem

theorem localBPLeftFringeCandidateSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose seed : Nat) :
    (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose seed).cost <=
      4 := by
  simp [localBPLeftFringeCandidateSeededCosted]

theorem localBPRightFringeCandidateSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose seed : Nat) :
    (localBPRightFringeCandidateSeededCosted shape blockSize rightClose seed).cost <=
      4 := by
  simp [localBPRightFringeCandidateSeededCosted]

def localBPSameBlockCloseSeededCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) : Costed (Option Nat) :=
  let window :=
    SuccinctSpace.flattenPayloadWords
      (localBPBlockWordsRead shape blockSize leftClose)
  let base := localBPWindowBase shape blockSize leftClose
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  { value :=
      bpCandidateClose?
        (some
          (localBPSeededPrefixRangeMinExcess window seed base start count,
            localBPSeededPrefixRangeArgMinPrefixPos window seed base
              start count))
    cost := 4 }

def localBPSameBlockCloseDecodedCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (localBPSeedFromRankFalseCosted shape blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed

def localBPSameBlockCloseDecodedCostedWithRankSeed
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose : Nat) : Costed (Option Nat) :=
  Costed.bind
    (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize leftClose)
    fun seed =>
      localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed

theorem localBPSameBlockCloseSeededCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose seed : Nat) :
    (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        seed).cost <= 4 := by
  simp [localBPSameBlockCloseSeededCosted]

theorem localBPSameBlockCloseDecodedCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose rightClose : Nat) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).cost <= 5 := by
  simp [localBPSameBlockCloseDecodedCosted, Costed.bind,
    localBPSeedFromRankFalseCosted, localBPSameBlockCloseSeededCosted]

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_cost_le
    (shape : Cartesian.CartesianShape)
    (rankCloseCosted : Nat -> Costed Nat)
    (blockSize leftClose rightClose rankCost : Nat)
    (hrankCost : forall pos, (rankCloseCosted pos).cost <= rankCost) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).cost <= rankCost + 4 := by
  unfold localBPSameBlockCloseDecodedCostedWithRankSeed
  have hseed :=
    localBPSeedFromRankCloseCosted_cost_le shape rankCloseCosted blockSize
      leftClose rankCost hrankCost
  have hlocal :=
    localBPSameBlockCloseSeededCosted_cost_le shape blockSize leftClose
      rightClose
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
        leftClose).value
  simp [Costed.bind] at hseed hlocal ⊢
  omega

theorem localBPSameBlockCloseSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseSeededCosted shape blockSize leftClose rightClose
        (localBPSeedExcess shape blockSize leftClose)).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  let start := leftClose + 1
  let count := rightClose - leftClose + 1
  have hcount : 0 < count := by
    omega
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have hwindow :=
    localBPWindowBits_eq_flatten_localBPBlockWordsRead
      shape blockSize leftClose
  have hminFlat :
      localBPSeededPrefixRangeMinExcess
          (SuccinctSpace.flattenPayloadWords
            (localBPBlockWordsRead shape blockSize leftClose))
          (localBPSeedExcess shape blockSize leftClose)
          (localBPWindowBase shape blockSize leftClose)
          start count =
        bpPrefixRangeMinExcess shape start count := by
    simpa [← hwindow] using hmin
  have hargFlat :
      localBPSeededPrefixRangeArgMinPrefixPos
          (SuccinctSpace.flattenPayloadWords
            (localBPBlockWordsRead shape blockSize leftClose))
          (localBPSeedExcess shape blockSize leftClose)
          (localBPWindowBase shape blockSize leftClose)
          start count =
        bpPrefixRangeArgMinPrefixPos shape start count := by
    simpa [← hwindow] using harg
  simp [localBPSameBlockCloseSeededCosted, start, count, hminFlat,
    hargFlat]

theorem localBPSameBlockCloseDecodedCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  have hseed :
      (localBPSeedFromRankFalseCosted shape blockSize leftClose).value =
        localBPSeedExcess shape blockSize leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankFalseCosted_eq_localBPSeedExcess
        shape blockSize leftClose hbase
  have hseeded :=
    localBPSameBlockCloseSeededCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  simpa [localBPSameBlockCloseDecodedCosted, Costed.bind, Costed.erase,
    hseed] using hseeded

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_eq_semantic
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize leftClose rightClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hordered : leftClose <= rightClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) := by
  have hseed :
      (localBPSeedFromRankCloseCosted shape rankCloseCosted blockSize
          leftClose).value =
        localBPSeedExcess shape blockSize leftClose := by
    simpa [Costed.erase] using
      localBPSeedFromRankCloseCosted_eq_localBPSeedExcess
        shape rankCloseCosted blockSize leftClose hrankExact hbase
  have hseeded :=
    localBPSameBlockCloseSeededCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  simpa [localBPSameBlockCloseDecodedCostedWithRankSeed, Costed.bind,
    Costed.erase, hseed] using hseeded

theorem localBPSameBlockClosePrefixRange_exact
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    bpCandidateClose?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (rightClose - leftClose + 1),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (rightClose - leftClose + 1))) =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hmem :=
    answerClose_prefix_mem_endpoint_prefix_range
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hleft hright hanswer
  have hsemantic :=
    answerClose_prefix_leftmost_min_excess_of_query
      (shape := shape) (start := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer
  have hrightBound := bpCloseOfInorder?_bounds shape hright
  have hprefixBound :
      leftClose + 1 + (rightClose - leftClose + 1) <=
        shape.bpCode.length + 1 := by
    omega
  have hwitness :=
    bpPrefixRangeWitness_eq_of_leftmost_min_excess
      (shape := shape)
      (start := leftClose + 1)
      (count := rightClose - leftClose + 1)
      (target := answerClose + 1)
      hmem hprefixBound
      (by
        intro pos hlo hhi
        exact hsemantic.1 hlo (by omega))
      hsemantic.2
  rw [hwitness]
  simp [bpCandidateClose?]

theorem localBPSameBlockCloseDecodedCosted_exact
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hdecoded :=
    localBPSameBlockCloseDecodedCosted_eq_semantic
      (shape := shape) (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hbase hstartBase hrightCovered hordered
  rw [hdecoded]
  exact
    localBPSameBlockClosePrefixRange_exact
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_exact
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hdecoded :=
    localBPSameBlockCloseDecodedCostedWithRankSeed_eq_semantic
      (shape := shape) (rankCloseCosted := rankCloseCosted)
      (blockSize := blockSize)
      (leftClose := leftClose) (rightClose := rightClose)
      hrankExact hbase hstartBase hrightCovered hordered
  rw [hdecoded]
  exact
    localBPSameBlockClosePrefixRange_exact
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCosted_exact_of_query_same_block
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hblockSizePos : 0 < blockSize)
    (hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length)
    (hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCosted shape blockSize leftClose
        rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hbaseBlock :
      localBPWindowBase shape blockSize leftClose <=
        blockStartOf blockSize (blockOfClose blockSize leftClose) :=
    localBPWindowBase_le_blockStart shape blockSize leftClose
  have hbaseClose :
      localBPWindowBase shape blockSize leftClose <= leftClose :=
    Nat.le_trans hbaseBlock blockStartOf_blockOfClose_le
  have hbaseLen :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
    omega
  have hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
    omega
  have hblockEndWidth :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape blockSize leftClose
      hblockSizeLeThree
  have hrightInside :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := blockSize) (close := rightClose) hblockSizePos
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    have hrightBlockStart :
        blockStartOf blockSize (blockOfClose blockSize rightClose) =
          blockStartOf blockSize (blockOfClose blockSize leftClose) := by
      rw [← hsame]
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  exact
    localBPSameBlockCloseDecodedCosted_exact
      (shape := shape) (blockSize := blockSize)
      (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hbaseLen hstartBase hrightCovered hlen hbound hleft hright hanswer

theorem localBPSameBlockCloseDecodedCostedWithRankSeed_exact_of_query_same_block
    {shape : Cartesian.CartesianShape}
    {rankCloseCosted : Nat -> Costed Nat}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hrankExact :
      forall pos,
        (rankCloseCosted pos).erase =
          Succinct.rankPrefix false shape.bpCode pos)
    (hblockSizePos : 0 < blockSize)
    (hblockSizeLeThree :
      blockSize <=
        3 * SuccinctRank.machineWordBits shape.bpCode.length)
    (hsame :
      blockOfClose blockSize leftClose =
        blockOfClose blockSize rightClose)
    (hlen : 0 < len)
    (hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseDecodedCostedWithRankSeed shape rankCloseCosted
        blockSize leftClose rightClose).erase =
      some answerClose := by
  have hordered :=
    endpoint_closes_ordered_of_query_span
      (shape := shape) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      hlen hleft hright
  have hleftCloseBound := bpCloseOfInorder?_bounds shape hleft
  have hrightCloseBound := bpCloseOfInorder?_bounds shape hright
  have hbaseBlock :
      localBPWindowBase shape blockSize leftClose <=
        blockStartOf blockSize (blockOfClose blockSize leftClose) :=
    localBPWindowBase_le_blockStart shape blockSize leftClose
  have hbaseClose :
      localBPWindowBase shape blockSize leftClose <= leftClose :=
    Nat.le_trans hbaseBlock blockStartOf_blockOfClose_le
  have hbaseLen :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length := by
    omega
  have hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1 := by
    omega
  have hblockEndWidth :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length :=
    localBPWindow_block_end_le_four_words shape blockSize leftClose
      hblockSizeLeThree
  have hrightInside :
      rightClose <
        blockStartOf blockSize (blockOfClose blockSize rightClose) +
          blockSize :=
    close_lt_blockStartOf_blockOfClose_add
      (blockSize := blockSize) (close := rightClose) hblockSizePos
  have hrightEndWidth :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          4 * SuccinctRank.machineWordBits shape.bpCode.length := by
    have hrightBlockStart :
        blockStartOf blockSize (blockOfClose blockSize rightClose) =
          blockStartOf blockSize (blockOfClose blockSize leftClose) := by
      simp [hsame]
    omega
  have hrightEndLen : rightClose + 1 <= shape.bpCode.length := by
    omega
  have hrightCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length :=
    localBPWindowBits_covers_of_le_width
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (pos := rightClose + 1)
      (by omega) hrightEndLen hrightEndWidth
  exact
    localBPSameBlockCloseDecodedCostedWithRankSeed_exact
      (shape := shape) (rankCloseCosted := rankCloseCosted)
      (blockSize := blockSize) (left := left) (len := len)
      (leftClose := leftClose) (rightClose := rightClose)
      (answerClose := answerClose)
      hrankExact hbaseLen hstartBase hrightCovered hlen hbound
      hleft hright hanswer

def localBPSameBlockCloseCosted
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  let left := closeToInorder shape leftClose
  let right := closeToInorder shape rightClose
  { value :=
      if left <= right then
        bpCloseOfInorder? shape
          (scanWindow shape.representative left (right - left + 1))
      else
        none
    cost := 4 }

theorem localBPSameBlockCloseCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (leftClose rightClose : Nat) :
    (localBPSameBlockCloseCosted shape leftClose rightClose).cost <= 4 := by
  simp [localBPSameBlockCloseCosted]

theorem localBPSameBlockCloseCosted_exact
    {shape : Cartesian.CartesianShape}
    {left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (_hbound : left + len <= shape.size)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose) :
    (localBPSameBlockCloseCosted shape leftClose rightClose).erase =
      some answerClose := by
  have hleftIdx := closeToInorder_eq_of_bpCloseOfInorder? hleft
  have hrightIdx := closeToInorder_eq_of_bpCloseOfInorder? hright
  have hle :
      closeToInorder shape leftClose <=
        closeToInorder shape rightClose := by
    omega
  have hlenEq :
      closeToInorder shape rightClose -
          closeToInorder shape leftClose + 1 =
        len := by
    omega
  unfold localBPSameBlockCloseCosted
  change
    (if closeToInorder shape leftClose <=
          closeToInorder shape rightClose then
        bpCloseOfInorder? shape
          (scanWindow shape.representative
            (closeToInorder shape leftClose)
            (closeToInorder shape rightClose -
              closeToInorder shape leftClose + 1))
      else
        none) = some answerClose
  rw [if_pos hle]
  rw [hleftIdx, hrightIdx]
  have hlenEq' : left + len - 1 - left + 1 = len := by
    omega
  rw [hlenEq']
  exact hanswer

def localBPLeftFringeCandidateCosted
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) : Costed (Option (Nat × Nat)) :=
  { value :=
      some
        (bpPrefixRangeMinExcess shape (leftClose + 1)
          (blockStartOf blockSize (blockOfClose blockSize leftClose) +
            blockSize - leftClose),
          bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
            (blockStartOf blockSize (blockOfClose blockSize leftClose) +
              blockSize - leftClose))
    cost := 4 }

def localBPRightFringeCandidateCosted
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) : Costed (Option (Nat × Nat)) :=
  { value :=
      some
        (bpPrefixRangeMinExcess shape
          (blockStartOf blockSize (blockOfClose blockSize rightClose))
          (rightClose -
              blockStartOf blockSize (blockOfClose blockSize rightClose) +
            2),
          bpPrefixRangeArgMinPrefixPos shape
            (blockStartOf blockSize (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize (blockOfClose blockSize rightClose) +
              2))
    cost := 4 }

theorem localBPLeftFringeCandidateSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize leftClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize leftClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize leftClose <= leftClose + 1)
    (hendCovered :
      blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length)
    (hleftInside :
      leftClose <
        blockStartOf blockSize (blockOfClose blockSize leftClose) +
          blockSize) :
    (localBPLeftFringeCandidateSeededCosted shape blockSize leftClose
        (localBPSeedExcess shape blockSize leftClose)).erase =
      (localBPLeftFringeCandidateCosted shape blockSize leftClose).erase := by
  let start := leftClose + 1
  let count :=
    blockStartOf blockSize (blockOfClose blockSize leftClose) +
      blockSize - leftClose
  have hcount : 0 < count := by
    simp [count]
    omega
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize leftClose +
          (localBPWindowBits shape blockSize leftClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := leftClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  simp [localBPLeftFringeCandidateSeededCosted,
    localBPLeftFringeCandidateCosted, start, count, hmin, harg]

theorem localBPRightFringeCandidateSeededCosted_eq_semantic
    {shape : Cartesian.CartesianShape}
    {blockSize rightClose : Nat}
    (hbase :
      localBPWindowBase shape blockSize rightClose <= shape.bpCode.length)
    (hstartBase :
      localBPWindowBase shape blockSize rightClose <=
        blockStartOf blockSize (blockOfClose blockSize rightClose))
    (hrightInside :
      blockStartOf blockSize (blockOfClose blockSize rightClose) <=
        rightClose)
    (hendCovered :
      rightClose + 1 <=
        localBPWindowBase shape blockSize rightClose +
          (localBPWindowBits shape blockSize rightClose).length) :
    (localBPRightFringeCandidateSeededCosted shape blockSize rightClose
        (localBPSeedExcess shape blockSize rightClose)).erase =
      (localBPRightFringeCandidateCosted shape blockSize rightClose).erase := by
  let start := blockStartOf blockSize (blockOfClose blockSize rightClose)
  let count := rightClose - start + 2
  have hcount : 0 < count := by
    simp [count]
  have hcovered :
      start + count <=
        localBPWindowBase shape blockSize rightClose +
          (localBPWindowBits shape blockSize rightClose).length + 1 := by
    simp [start, count]
    omega
  have hmin :=
    localBPSeededPrefixRangeMinExcess_eq_bpPrefixRangeMinExcess_of_pos
      (shape := shape) (blockSize := blockSize) (close := rightClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  have harg :=
    localBPSeededPrefixRangeArgMinPrefixPos_eq_bpPrefixRangeArgMinPrefixPos_of_pos
      (shape := shape) (blockSize := blockSize) (close := rightClose)
      (start := start) (count := count)
      hcount hbase (by simpa [start] using hstartBase) hcovered
  simp [localBPRightFringeCandidateSeededCosted,
    localBPRightFringeCandidateCosted, start, count, hmin, harg]

theorem localBPLeftFringeCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize leftClose : Nat) :
    (localBPLeftFringeCandidateCosted shape blockSize leftClose).cost <=
      4 := by
  simp [localBPLeftFringeCandidateCosted]

theorem localBPRightFringeCandidateCosted_cost_le
    (shape : Cartesian.CartesianShape)
    (blockSize rightClose : Nat) :
    (localBPRightFringeCandidateCosted shape blockSize rightClose).cost <=
      4 := by
  simp [localBPRightFringeCandidateCosted]

theorem bpRelativeRmmCandidateMerge_exact_of_query_semantics_no_block_bounds
    {shape : Cartesian.CartesianShape}
    {blockSize left len leftClose rightClose answerClose : Nat}
    (hlen : 0 < len)
    (hleft : bpCloseOfInorder? shape left = some leftClose)
    (hright :
      bpCloseOfInorder? shape (left + len - 1) = some rightClose)
    (hanswer :
      bpCloseOfInorder? shape
          (scanWindow shape.representative left len) =
        some answerClose)
    (hblockSize : 0 < blockSize)
    (hcross :
      blockOfClose blockSize leftClose <
        blockOfClose blockSize rightClose)
    (hmin :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < rightClose + 2 ->
            bpExcessAt shape (answerClose + 1) <=
              bpExcessAt shape pos)
    (hleftmost :
      forall {pos : Nat},
        leftClose + 1 <= pos ->
          pos < answerClose + 1 ->
            bpExcessAt shape (answerClose + 1) <
              bpExcessAt shape pos) :
    bpCandidateMerge3?
        (some
          (bpPrefixRangeMinExcess shape (leftClose + 1)
            (blockStartOf blockSize
                (blockOfClose blockSize leftClose) +
              blockSize - leftClose),
            bpPrefixRangeArgMinPrefixPos shape (leftClose + 1)
              (blockStartOf blockSize
                  (blockOfClose blockSize leftClose) +
                blockSize - leftClose)))
        (if blockOfClose blockSize leftClose + 1 <
            blockOfClose blockSize rightClose then
          some
            (bpRangeMinExcess shape blockSize
              (blockOfClose blockSize leftClose + 1)
              (blockOfClose blockSize rightClose -
                blockOfClose blockSize leftClose - 1),
              bpRangeArgMinPrefixPos shape blockSize
                (blockOfClose blockSize leftClose + 1)
                (blockOfClose blockSize rightClose -
                  blockOfClose blockSize leftClose - 1))
        else
          none)
        (some
          (bpPrefixRangeMinExcess shape
            (blockStartOf blockSize
              (blockOfClose blockSize rightClose))
            (rightClose -
                blockStartOf blockSize
                  (blockOfClose blockSize rightClose) +
              2),
            bpPrefixRangeArgMinPrefixPos shape
              (blockStartOf blockSize
                (blockOfClose blockSize rightClose))
              (rightClose -
                  blockStartOf blockSize
                    (blockOfClose blockSize rightClose) +
                2))) =
      some (bpExcessAt shape (answerClose + 1), answerClose + 1) := by
  let blockCount :=
    Nat.max (blockOfClose blockSize leftClose)
      (blockOfClose blockSize rightClose) + 1
  have hleftBlock :
      blockOfClose blockSize leftClose < blockCount := by
    dsimp [blockCount]
    exact Nat.lt_succ_of_le (Nat.le_max_left _ _)
  have hrightBlock :
      blockOfClose blockSize rightClose < blockCount := by
    dsimp [blockCount]
    exact Nat.lt_succ_of_le (Nat.le_max_right _ _)
  exact
    bpRelativeRmmCandidateMerge_exact_of_query_semantics
      (shape := shape) (blockSize := blockSize) (blockCount := blockCount)
      (left := left) (len := len) (leftClose := leftClose)
      (rightClose := rightClose) (answerClose := answerClose)
      hlen hleft hright hanswer hblockSize hleftBlock hrightBlock
      hcross hmin hleftmost

theorem canonicalBPRelativeSummaryBlockCountRaw_upper_cover
    (shape : Cartesian.CartesianShape) :
    shape.bpCode.length <
      (canonicalBPRelativeSummaryBlockCountRaw shape + 1) *
        canonicalBPRelativeSummaryBlockSizeRaw shape := by
  let base := canonicalBPRelativeSummaryBase shape
  have hbase : 0 < base := by
    simp [base, canonicalBPRelativeSummaryBase]
  have hlt := Nat.lt_div_mul_add hbase (a := shape.size)
  rw [Cartesian.CartesianShape.bpCode_length]
  calc
    2 * shape.size < 2 * ((shape.size / base) * base + base) :=
      Nat.mul_lt_mul_of_pos_left hlt (by omega)
    _ = 2 * ((shape.size / base + 1) * base) := by
      congr 1
      rw [Nat.add_mul, Nat.one_mul]
    _ = (shape.size / base + 1) * (2 * base) := by
      simp [Nat.mul_assoc, Nat.mul_comm]

theorem canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
    {shape : Cartesian.CartesianShape}
    (hactive : canonicalBPRelativeMinMaxArgSummaryTableActive shape)
    {close : Nat}
    (hclose : close < shape.bpCode.length) :
    blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <=
      canonicalBPRelativeSummaryBlockCount shape := by
  have hblockSizePos :
      0 < canonicalBPRelativeSummaryBlockSizeRaw shape :=
    canonicalBPRelativeSummaryBlockSizeRaw_pos shape
  have hupper :=
    canonicalBPRelativeSummaryBlockCountRaw_upper_cover shape
  have hcloseUpper :
      close <
        (canonicalBPRelativeSummaryBlockCountRaw shape + 1) *
          canonicalBPRelativeSummaryBlockSizeRaw shape :=
    Nat.lt_trans hclose hupper
  have hdiv :
      close / canonicalBPRelativeSummaryBlockSizeRaw shape <
        canonicalBPRelativeSummaryBlockCountRaw shape + 1 := by
    exact (Nat.div_lt_iff_lt_mul hblockSizePos).2 hcloseUpper
  have hleRaw :
      close / canonicalBPRelativeSummaryBlockSizeRaw shape <=
        canonicalBPRelativeSummaryBlockCountRaw shape := by
    omega
  simpa [blockOfClose, canonicalBPRelativeSummaryBlockSize,
    canonicalBPRelativeSummaryBlockCount, hactive] using hleRaw

theorem canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_large
    {shape : Cartesian.CartesianShape}
    (hlarge : canonicalBPRelativeSummaryLargeRegime shape)
    {close : Nat}
    (hclose : close < shape.bpCode.length) :
    blockOfClose (canonicalBPRelativeSummaryBlockSize shape) close <=
      canonicalBPRelativeSummaryBlockCount shape := by
  exact
    canonicalBPRelativeSummary_blockOfClose_le_blockCount_of_active
      (canonicalBPRelativeMinMaxArgSummaryTableActive_of_large
        (shape := shape) hlarge)
      hclose

theorem cartesianShape_shapeOfSize_self
    (shape : Cartesian.CartesianShape) :
    Cartesian.ShapeOfSize shape.size shape := by
  induction shape with
  | empty =>
      exact Cartesian.ShapeOfSize.empty
  | node left right ihleft ihright =>
      simpa [Cartesian.CartesianShape.size] using
        Cartesian.ShapeOfSize.node ihleft ihright


end SuccinctClose
end RMQ
