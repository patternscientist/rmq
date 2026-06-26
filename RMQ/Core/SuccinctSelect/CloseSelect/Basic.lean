import RMQ.Core.SuccinctSelect.DenseLocalTables
import RMQ.Core.GenericSelect.DenseEntryTable

/-!
# Basic false-select routing helpers

Split implementation layer for the select-side close-select proposal.
Public declarations stay in the historical `RMQ.SuccinctSelect`
namespace.
-/

namespace RMQ
namespace SuccinctSelect

/-!
## Sparse/dense false-select close locator

This is the C1-specific close-select surface for `select false shape.bpCode`.
It reuses the packed four-field locator-entry codec above for super and
coarse local inventories, while dense-local payload fields are split across
`FixedWidthSparseDenseFalseSelectDenseLocalEntryTable`.  The dense case reads
that split dense entry before the two aligned BP payload-word fallback; all
directory reads go through payload-backed stores.
-/

/-- Canonical coarse slot budget for the sparse/dense false-select locator. -/
def canonicalSparseDenseFalseSelectOverhead (n : Nat) : Nat :=
  sparseDenseFalseSelectOverhead 32 32 32 32 (2 * n)

theorem canonicalSparseDenseFalseSelectOverhead_littleO :
    SuccinctSpace.LittleOLinear canonicalSparseDenseFalseSelectOverhead := by
  unfold canonicalSparseDenseFalseSelectOverhead
  exact (sparseDenseFalseSelectOverhead_littleO 32 32 32 32).comp_two_mul_arg

/-- Fixed model cost for one sparse/dense close-select query. -/
def sparseDenseFalseSelectQueryCost : Nat := 16

def sparseDenseFalseSelectWordBits
    (shape : Cartesian.CartesianShape) : Nat :=
  SuccinctRank.machineWordBits shape.bpCode.length

def sparseDenseFalseSelectEll
    (shape : Cartesian.CartesianShape) : Nat :=
  Nat.log2 (sparseDenseFalseSelectWordBits shape) + 1

def sparseDenseFalseSelectSuperStride
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape *
    sparseDenseFalseSelectWordBits shape

def sparseDenseFalseSelectLocalStride
    (shape : Cartesian.CartesianShape) : Nat :=
  max 1
    (sparseDenseFalseSelectWordBits shape /
      (sparseDenseFalseSelectEll shape *
        sparseDenseFalseSelectEll shape))

def sparseDenseFalseSelectSuperLongSpan
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectSuperStride shape *
    sparseDenseFalseSelectWordBits shape *
      sparseDenseFalseSelectEll shape

def sparseDenseFalseSelectLocalSparseSpan
    (shape : Cartesian.CartesianShape) : Nat :=
  sparseDenseFalseSelectWordBits shape

/-- Collect target-bit positions, continuing from an absolute base offset. -/
def selectPositionsFrom
    (target : Bool) : List Bool -> Nat -> List Nat
  | [], _base => []
  | bit :: rest, base =>
      let tail := selectPositionsFrom target rest (base + 1)
      if bit = target then base :: tail else tail

/-- Collect all absolute positions whose bit equals `target`. -/
def selectPositions (target : Bool) (bits : List Bool) : List Nat :=
  selectPositionsFrom target bits 0

theorem selectPositionsFrom_get?_eq_selectFrom
    (target : Bool) (bits : List Bool) (base occurrence : Nat) :
    (selectPositionsFrom target bits base)[occurrence]? =
      RMQ.Succinct.selectFrom target bits base occurrence := by
  induction bits generalizing base occurrence with
  | nil =>
      simp [selectPositionsFrom, RMQ.Succinct.selectFrom]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · cases occurrence with
        | zero =>
            simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit]
        | succ occurrence =>
            simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
              ih (base + 1) occurrence]
      · simp [selectPositionsFrom, RMQ.Succinct.selectFrom, hbit,
          ih (base + 1) occurrence]

theorem selectPositions_get?_eq_select
    (target : Bool) (bits : List Bool) (occurrence : Nat) :
    (selectPositions target bits)[occurrence]? =
      RMQ.Succinct.select target bits occurrence := by
  simp [selectPositions, RMQ.Succinct.select,
    selectPositionsFrom_get?_eq_selectFrom]

theorem selectPositionsFrom_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) (base : Nat) :
    (selectPositionsFrom target bits base).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  induction bits generalizing base with
  | nil =>
      simp [selectPositionsFrom, RMQ.Succinct.rankPrefix]
  | cons bit rest ih =>
      by_cases hbit : bit = target
      · simp [selectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1), Nat.add_comm]
      · simp [selectPositionsFrom, RMQ.Succinct.rankPrefix, hbit,
          ih (base + 1)]

theorem selectPositions_length_eq_rankPrefix_length
    (target : Bool) (bits : List Bool) :
    (selectPositions target bits).length =
      RMQ.Succinct.rankPrefix target bits bits.length := by
  simpa [selectPositions] using
    selectPositionsFrom_length_eq_rankPrefix_length target bits 0

theorem select_exists_of_lt_rankPrefix
    {target : Bool} {bits : List Bool} {occurrence limit : Nat}
    (hcount :
      occurrence < RMQ.Succinct.rankPrefix target bits limit) :
    exists pos, RMQ.Succinct.select target bits occurrence = some pos := by
  have hcountMin :
      occurrence <
        RMQ.Succinct.rankPrefix target bits
          (Nat.min limit bits.length) := by
    simpa [RMQ.Succinct.rankPrefix_min_length_eq] using hcount
  have htotal :
      occurrence <
        RMQ.Succinct.rankPrefix target bits bits.length := by
    exact Nat.lt_of_lt_of_le hcountMin
      (RMQ.Succinct.rankPrefix_mono_limit
        target bits (Nat.min_le_right limit bits.length))
  have hidx :
      occurrence < (selectPositions target bits).length := by
    simpa [selectPositions_length_eq_rankPrefix_length] using htotal
  refine ⟨(selectPositions target bits)[occurrence], ?_⟩
  have hget :
      (selectPositions target bits)[occurrence]? =
        some ((selectPositions target bits)[occurrence]) :=
    List.getElem?_eq_getElem hidx
  simpa [selectPositions_get?_eq_select] using hget

theorem select_none_of_rankPrefix_length_le
    {target : Bool} {bits : List Bool} {occurrence : Nat}
    (hcount :
      RMQ.Succinct.rankPrefix target bits bits.length <= occurrence) :
    RMQ.Succinct.select target bits occurrence = none := by
  have hget :
      (selectPositions target bits)[occurrence]? = none := by
    exact List.getElem?_eq_none (by
      simpa [selectPositions_length_eq_rankPrefix_length] using hcount)
  simpa [selectPositions_get?_eq_select] using hget

/--
Dense local fallback for a sparse/dense select interval.

The base position may be unaligned, so the query reads the aligned word
containing it and, only when necessary, the next aligned word.  The only
non-read primitives are counted word-rank and word-select operations.
-/
def denseTwoWordFalseSelectCosted
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) : Costed (Option Nat) :=
  let firstWordIndex := basePosition / wordSize
  let firstWordStart := firstWordIndex * wordSize
  let firstOffset := basePosition - firstWordStart
  let localOccurrence := q - baseOccurrence
  Costed.bind (bitWords.store.readWordCosted firstWordIndex) fun firstWord? =>
    match firstWord? with
    | none => Costed.pure none
    | some firstWord =>
        Costed.bind
          (RMQ.RAM.rankBoolWordPrefix false firstWord firstOffset).toCosted
          fun beforeFirst =>
            Costed.bind
              (RMQ.RAM.rankBoolWordPrefix
                false firstWord firstWord.length).toCosted
              fun uptoFirst =>
                let firstCount := uptoFirst - beforeFirst
                if localOccurrence < firstCount then
                  Costed.map
                    (fun local? =>
                      local?.map fun offset => firstWordStart + offset)
                    (RMQ.RAM.selectBoolWord false firstWord
                      (beforeFirst + localOccurrence)).toCosted
                else
                  Costed.bind
                    (bitWords.store.readWordCosted (firstWordIndex + 1))
                    fun secondWord? =>
                      match secondWord? with
                      | none => Costed.pure none
                      | some secondWord =>
                          Costed.map
                            (fun local? =>
                              local?.map fun offset =>
                                (firstWordIndex + 1) * wordSize + offset)
                            (RMQ.RAM.selectBoolWord false secondWord
                              (localOccurrence - firstCount)).toCosted

theorem denseTwoWordFalseSelectCosted_cost_le_five
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (basePosition baseOccurrence q : Nat) :
    (denseTwoWordFalseSelectCosted
      bitWords basePosition baseOccurrence q).cost <= 5 := by
  unfold denseTwoWordFalseSelectCosted
  cases hfirst :
      (bitWords.store.readWordCosted
        (basePosition / wordSize)).value with
  | none =>
      simp [Costed.bind, Costed.pure, hfirst]
  | some firstWord =>
      by_cases hchoose :
          q - baseOccurrence <
            RMQ.RAM.boolRankPrefix false firstWord firstWord.length -
              RMQ.RAM.boolRankPrefix false firstWord
                (basePosition - basePosition / wordSize * wordSize)
      · simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose]
      · cases hsecond :
            (bitWords.store.readWordCosted
              (basePosition / wordSize + 1)).value with
        | none =>
            simp [Costed.bind, Costed.pure, hfirst, hchoose,
              hsecond]
        | some secondWord =>
            simp [Costed.bind, Costed.map, Costed.pure, hfirst, hchoose,
              hsecond]

def sparseDenseFalseSelectDenseLocalEntryBasePosition
    (wordSize : Nat)
    (entry : SparseDenseFalseSelectDenseLocalEntry) : Nat :=
  entry.baseWordIndex * wordSize + entry.firstOffset

def denseLocalEntryFalseSelectCosted
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) : Costed (Option Nat) :=
  denseTwoWordFalseSelectCosted bitWords
    (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
    entry.baseOccurrence q

theorem denseLocalEntryFalseSelectCosted_cost_le_five
    {bits : List Bool} {wordSize : Nat}
    (bitWords : SuccinctSpace.BoundedPayloadWordStore bits wordSize)
    (entry : SparseDenseFalseSelectDenseLocalEntry)
    (q : Nat) :
    (denseLocalEntryFalseSelectCosted bitWords entry q).cost <= 5 := by
  exact
    denseTwoWordFalseSelectCosted_cost_le_five bitWords
      (sparseDenseFalseSelectDenseLocalEntryBasePosition wordSize entry)
      entry.baseOccurrence q


end SuccinctSelect
end RMQ
