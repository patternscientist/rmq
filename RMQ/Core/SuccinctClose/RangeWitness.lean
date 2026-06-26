import RMQ.Core.SuccinctClose.RelativeSummary

/-!
# Position-bearing BP range witnesses

Payload-live argmin-prefix summaries, range-witness tables, and the first
block-pair macro candidate layer. The historical `RMQ.SuccinctCloseProposal`
namespace is preserved.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

/-!
## Position-bearing BP block summaries

The min/max summary table above is not enough to route a close/LCA answer.  The
next concrete payload layer stores the first sampled prefix position attaining a
block-local minimum excess.  This is still not the final answer-close theorem,
but unlike the min/max-only table it carries a charged position witness for the
macro range-min path.
-/

/-- Payload-live min/max summary table plus a charged argmin prefix position. -/
structure PayloadLiveBPRangeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth overhead : Nat) where
  summary :
    PayloadLiveBPRangeMinMaxSummaryTable shape blockSize blockCount
      fieldWidth (2 * (blockCount * fieldWidth))
  argTable :
    FixedWidthNatTable
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
      fieldWidth
  payload_length_eq :
    summary.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPRangeMinMaxArgSummaryTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) : List Bool :=
  table.summary.payload ++ table.argTable.payload

def argMinPrefixPosCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option Nat) :=
  table.argTable.readCosted block

def summaryArgCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) : Costed (Option (Nat × Nat × Nat)) :=
  Costed.bind (table.summary.summaryCosted block) fun summary? =>
    Costed.map
      (fun arg? =>
        match summary?, arg? with
        | some (minExcess, maxExcess), some argPos =>
            some (minExcess, maxExcess, argPos)
        | _, _ => none)
      (table.argMinPrefixPosCosted block)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem argMinPrefixPosCosted_cost_le_one
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.argMinPrefixPosCosted block).cost <= 1 := by
  simp [argMinPrefixPosCosted]

theorem argMinPrefixPosCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.argMinPrefixPosCosted block).erase =
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? := by
  simp [argMinPrefixPosCosted]

theorem summaryArgCosted_cost_le_three
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryArgCosted block).cost <= 3 := by
  unfold summaryArgCosted argMinPrefixPosCosted
  have hsummary := table.summary.summaryCosted_cost_le_two block
  have harg := table.argTable.readCosted_cost_le_one block
  cases hread : (table.summary.summaryCosted block).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
      omega
  | some value =>
      simp [Costed.bind, Costed.map, hread]
      omega

theorem summaryArgCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (block : Nat) :
    (table.summaryArgCosted block).erase =
      match
        (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
        (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
        (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? with
      | some minExcess, some maxExcess, some argPos =>
          some (minExcess, maxExcess, argPos)
      | _, _, _ => none := by
  unfold summaryArgCosted
  have hsummary :
      (table.summary.summaryCosted block).value =
        match
          (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
          (bpBlockMaxExcessEntries shape blockSize blockCount)[block]? with
        | some minExcess, some maxExcess => some (minExcess, maxExcess)
        | _, _ => none := by
    simpa [Costed.erase] using table.summary.summaryCosted_erase block
  have harg :
      (table.argTable.readCosted block).value =
        (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]? := by
    exact table.argTable.readCosted_erase block
  cases hmin : (bpBlockMinExcessEntries shape blockSize blockCount)[block]?
  <;> cases hmax :
    (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?
  <;> cases hargEntry :
    (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, argMinPrefixPosCosted,
    hsummary, harg, hmin, hmax, hargEntry]

theorem arg_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {block : Nat} {word : List Bool}
    (hword : table.argTable.store.words[block]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlen := table.argTable.read_word_length_of_some hword
  omega

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {block : Nat} {word : List Bool},
      table.summary.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.summary.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  have hsummary :=
    table.summary.summary_read_words_length_le_machine hmachine
  exact ⟨hsummary.1, hsummary.2,
    by
      intro block word hword
      exact table.arg_read_word_length_le_machine hmachine hword⟩

theorem payload_length_le_sampled
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead slots n : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead)
    (hbudget :
      overhead <= sampledDirectoryOverhead slots n) :
    table.payload.length <= sampledDirectoryOverhead slots n := by
  rw [table.payload_length]
  exact hbudget

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (table :
      PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
        fieldWidth overhead) :
    table.payload.length = overhead /\
      (forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none) := by
  constructor
  · exact table.payload_length
  intro block
  exact ⟨table.summaryArgCosted_cost_le_three block,
    table.summaryArgCosted_erase block⟩

end PayloadLiveBPRangeMinMaxArgSummaryTable

def concreteBPRangeMinMaxArgSummaryTable
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPRangeMinMaxArgSummaryTable shape blockSize blockCount
      fieldWidth (3 * (blockCount * fieldWidth)) where
  summary :=
    concreteBPRangeMinMaxSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
      fieldWidth
      (by
        intro entry hmem
        exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)
  payload_length_eq := by
    have hsummary :
        (concreteBPRangeMinMaxSummaryTable
          shape blockSize blockCount fieldWidth hwidth).payload.length =
          2 * (blockCount * fieldWidth) := by
      exact
        (concreteBPRangeMinMaxSummaryTable
          shape blockSize blockCount fieldWidth hwidth).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload.length =
          blockCount * fieldWidth := by
      simpa [bpBlockArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)
          fieldWidth
          (by
            intro entry hmem
            exact bpBlockArgMinPrefixPosEntries_mem_bound hwidth hmem)).payload_length
    omega

theorem concreteBPRangeMinMaxArgSummaryTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    table.payload.length = 3 * (blockCount * fieldWidth) /\
      forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none := by
  exact
    (concreteBPRangeMinMaxArgSummaryTable
      shape blockSize blockCount fieldWidth hwidth).profile

theorem concreteBPRangeMinMaxArgSummaryTable_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hbudget :
      3 * (blockCount * fieldWidth) <= sampledDirectoryOverhead slots n) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      table.payload.length <= sampledDirectoryOverhead slots n /\
      (forall block,
        (table.summaryArgCosted block).cost <= 3 /\
          (table.summaryArgCosted block).erase =
            match
              (bpBlockMinExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockMaxExcessEntries shape blockSize blockCount)[block]?,
              (bpBlockArgMinPrefixPosEntries shape blockSize blockCount)[block]?
            with
            | some minExcess, some maxExcess, some argPos =>
                some (minExcess, maxExcess, argPos)
            | _, _, _ => none) := by
  let table :=
    concreteBPRangeMinMaxArgSummaryTable
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · exact table.payload_length_le_sampled hbudget
  intro block
  exact ⟨table.summaryArgCosted_cost_le_three block,
    table.summaryArgCosted_erase block⟩

theorem concreteBPRangeMinMaxArgSummaryTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth
    (forall {block : Nat} {word : List Bool},
      table.summary.minTable.store.words[block]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.summary.maxTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) /\
      (forall {block : Nat} {word : List Bool},
        table.argTable.store.words[block]? = some word ->
          word.length <=
            SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRangeMinMaxArgSummaryTable.read_words_length_le_machine
      (concreteBPRangeMinMaxArgSummaryTable
        shape blockSize blockCount fieldWidth hwidth)
      hmachine

/-!
## Position-bearing BP range witnesses

The block summaries above are single-block data.  The next macro ingredient is
an actual range witness: for each stored block range, the payload stores both
the minimum excess value and the prefix position attaining it.  The close
candidate returned by `rangeCloseCosted` is therefore computed from charged
payload reads instead of from proof-only block scans.
-/

def bpBetterArgMinPrefixPos
    (shape : Cartesian.CartesianShape) (left right : Nat) : Nat :=
  if bpExcessAt shape right < bpExcessAt shape left then right else left

theorem bpBetterArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hleft : left <= shape.bpCode.length)
    (hright : right <= shape.bpCode.length) :
    bpBetterArgMinPrefixPos shape left right <= shape.bpCode.length := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt, hright]
  · simp [hlt, hleft]

theorem bpExcessAt_bpBetterArgMinPrefixPos_le_left
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    bpExcessAt shape (bpBetterArgMinPrefixPos shape left right) <=
      bpExcessAt shape left := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt, Nat.le_of_lt hlt]
  · simp [hlt]

theorem bpExcessAt_bpBetterArgMinPrefixPos_le_right
    (shape : Cartesian.CartesianShape) (left right : Nat) :
    bpExcessAt shape (bpBetterArgMinPrefixPos shape left right) <=
      bpExcessAt shape right := by
  unfold bpBetterArgMinPrefixPos
  by_cases hlt : bpExcessAt shape right < bpExcessAt shape left
  · simp [hlt]
  · have hle :
        bpExcessAt shape left <= bpExcessAt shape right := by
      exact Nat.le_of_not_gt hlt
    simp [hlt, hle]

theorem bpBetterArgMinPrefixPos_eq_left_of_excess_le
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hle :
      bpExcessAt shape left <= bpExcessAt shape right) :
    bpBetterArgMinPrefixPos shape left right = left := by
  unfold bpBetterArgMinPrefixPos
  have hnot :
      ¬ bpExcessAt shape right < bpExcessAt shape left := by
    omega
  simp [hnot]

theorem bpBetterArgMinPrefixPos_eq_right_of_excess_lt
    (shape : Cartesian.CartesianShape) {left right : Nat}
    (hlt :
      bpExcessAt shape right < bpExcessAt shape left) :
    bpBetterArgMinPrefixPos shape left right = right := by
  simp [bpBetterArgMinPrefixPos, hlt]

def bpRangeArgMinPrefixPosFrom
    (shape : Cartesian.CartesianShape) (blockSize : Nat) :
    Nat -> Nat -> Nat -> Nat
  | _block, 0, best => best
  | block, steps + 1, best =>
      let candidate := bpBlockArgMinPrefixPos shape blockSize block
      let best' := bpBetterArgMinPrefixPos shape best candidate
      bpRangeArgMinPrefixPosFrom shape blockSize (block + 1) steps best'

theorem bpRangeArgMinPrefixPosFrom_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize block steps best : Nat)
    (hbest : best <= shape.bpCode.length) :
    bpRangeArgMinPrefixPosFrom shape blockSize block steps best <=
      shape.bpCode.length := by
  induction steps generalizing block best with
  | zero =>
      simpa [bpRangeArgMinPrefixPosFrom] using hbest
  | succ steps ih =>
      unfold bpRangeArgMinPrefixPosFrom
      exact ih (block + 1)
        (bpBetterArgMinPrefixPos shape best
          (bpBlockArgMinPrefixPos shape blockSize block))
        (bpBetterArgMinPrefixPos_le_length shape hbest
          (bpBlockArgMinPrefixPos_le_length shape blockSize block))

def bpRangeArgMinPrefixPos
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  match blockCount with
  | 0 => Nat.min (blockStartOf blockSize startBlock) shape.bpCode.length
  | count + 1 =>
      bpRangeArgMinPrefixPosFrom shape blockSize (startBlock + 1) count
        (bpBlockArgMinPrefixPos shape blockSize startBlock)

theorem bpRangeArgMinPrefixPos_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) :
    bpRangeArgMinPrefixPos shape blockSize startBlock blockCount <=
      shape.bpCode.length := by
  unfold bpRangeArgMinPrefixPos
  cases blockCount with
  | zero =>
      exact Nat.min_le_right (blockStartOf blockSize startBlock)
        shape.bpCode.length
  | succ count =>
      exact bpRangeArgMinPrefixPosFrom_le_length shape blockSize
        (startBlock + 1) count
        (bpBlockArgMinPrefixPos shape blockSize startBlock)
        (bpBlockArgMinPrefixPos_le_length shape blockSize startBlock)

def bpRangeMinExcess
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) : Nat :=
  bpExcessAt shape
    (bpRangeArgMinPrefixPos shape blockSize startBlock blockCount)

theorem bpRangeMinExcess_le_length
    (shape : Cartesian.CartesianShape)
    (blockSize startBlock blockCount : Nat) :
    bpRangeMinExcess shape blockSize startBlock blockCount <=
      shape.bpCode.length := by
  exact bpExcessAt_le_length shape
    (bpRangeArgMinPrefixPos shape blockSize startBlock blockCount)

def bpRangeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpRangeMinExcess shape blockSize range.1 range.2

def bpRangeArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpRangeArgMinPrefixPos shape blockSize range.1 range.2

theorem bpRangeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) :
    (bpRangeMinExcessEntries shape blockSize ranges).length =
      ranges.length := by
  simp [bpRangeMinExcessEntries]

theorem bpRangeArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (blockSize : Nat) (ranges : List (Nat × Nat)) :
    (bpRangeArgMinPrefixPosEntries shape blockSize ranges).length =
      ranges.length := by
  simp [bpRangeArgMinPrefixPosEntries]

theorem bpRangeMinExcessEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {blockSize : Nat}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? =
      some (bpRangeMinExcess shape blockSize range.1 range.2) := by
  simp [bpRangeMinExcessEntries, List.getElem?_map, hget]

theorem bpRangeArgMinPrefixPosEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {blockSize : Nat}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? =
      some (bpRangeArgMinPrefixPos shape blockSize range.1 range.2) := by
  simp [bpRangeArgMinPrefixPosEntries, List.getElem?_map, hget]

theorem bpRangeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpRangeMinExcessEntries shape blockSize ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpRangeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpRangeMinExcess_le_length shape blockSize range.1 range.2) hwidth

theorem bpRangeArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpRangeArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpRangeArgMinPrefixPos_le_length shape blockSize range.1 range.2)
    hwidth

/--
Payload-live macro witness table for explicit BP block ranges.

Each range consumes two fixed-width payload reads: one for the minimum excess
value and one for the prefix-position witness attaining that value.
-/
structure PayloadLiveBPRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth overhead : Nat)
    (ranges : List (Nat × Nat)) where
  minTable :
    FixedWidthNatTable
      (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
  argTable :
    FixedWidthNatTable
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
  payload_length_eq :
    minTable.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPRangeArgMinWitnessTable

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) : List Bool :=
  table.minTable.payload ++ table.argTable.payload

def rangeWitnessCosted
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minTable.readCosted rangeIndex) fun min? =>
    Costed.map
      (fun arg? =>
        match min?, arg? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none)
      (table.argTable.readCosted rangeIndex)

def rangeCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) : Costed (Option Nat) :=
  Costed.map
    (fun candidate? => candidate?.map fun candidate => candidate.2 - 1)
    (table.rangeWitnessCosted rangeIndex)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem rangeWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).cost <= 2 := by
  unfold rangeWitnessCosted
  cases hread :
      (table.minTable.readCosted rangeIndex).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
  | some minExcess =>
      simp [Costed.bind, Costed.map, hread]

theorem rangeCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeCloseCosted rangeIndex).cost <= 2 := by
  simpa [rangeCloseCosted, Costed.map_cost] using
    table.rangeWitnessCosted_cost_le_two rangeIndex

theorem rangeWitnessCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).erase =
      match
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? with
      | some minExcess, some prefixPos => some (minExcess, prefixPos)
      | _, _ => none := by
  unfold rangeWitnessCosted
  have hmin :
      (table.minTable.readCosted rangeIndex).value =
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? := by
    exact table.minTable.readCosted_erase rangeIndex
  have harg :
      (table.argTable.readCosted rangeIndex).value =
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? := by
    exact table.argTable.readCosted_erase rangeIndex
  cases hminEntry :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hmin, harg,
    hminEntry, hargEntry]

theorem rangeCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (rangeIndex : Nat) :
    (table.rangeCloseCosted rangeIndex).erase =
      match
        (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? with
      | some _minExcess, some prefixPos => some (prefixPos - 1)
      | _, _ => none := by
  cases hminEntry :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]?
  <;> simp [rangeCloseCosted, Costed.erase_map,
    table.rangeWitnessCosted_erase, hminEntry, hargEntry]

theorem rangeCloseCosted_exact_of_prefix_pos
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead answerClose rangeIndex : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmin :
      (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]? =
        some (bpExcessAt shape (answerClose + 1)))
    (harg :
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges)[rangeIndex]? =
        some (answerClose + 1)) :
    (table.rangeCloseCosted rangeIndex).erase = some answerClose := by
  simp [table.rangeCloseCosted_erase, hmin, harg]

theorem min_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.minTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlen := table.minTable.read_word_length_of_some hword
  omega

theorem arg_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length)
    {rangeIndex : Nat} {word : List Bool}
    (hword : table.argTable.store.words[rangeIndex]? = some word) :
    word.length <=
      SuccinctRank.machineWordBits shape.bpCode.length := by
  have hlen := table.argTable.read_word_length_of_some hword
  omega

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  constructor
  · intro rangeIndex word hword
    exact table.min_read_word_length_le_machine hmachine hword
  · intro rangeIndex word hword
    exact table.arg_read_word_length_le_machine hmachine hword

theorem payload_length_le_sampled
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead slots n : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges)
    (hoverhead : overhead <= sampledDirectoryOverhead slots n) :
    table.payload.length <= sampledDirectoryOverhead slots n := by
  rw [table.payload_length]
  exact hoverhead

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
        overhead ranges) :
    table.payload.length = overhead /\
      (forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none) /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  constructor
  · exact table.payload_length
  constructor
  · intro rangeIndex
    exact ⟨table.rangeWitnessCosted_cost_le_two rangeIndex,
      table.rangeWitnessCosted_erase rangeIndex⟩
  · intro rangeIndex
    exact ⟨table.rangeCloseCosted_cost_le_two rangeIndex,
      table.rangeCloseCosted_erase rangeIndex⟩

end PayloadLiveBPRangeArgMinWitnessTable

def concreteBPRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth
      (2 * (ranges.length * fieldWidth)) ranges where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
      (bpRangeMinExcessEntries_mem_bound hwidth)
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
      (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
          (bpRangeMinExcessEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpRangeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpRangeMinExcessEntries shape blockSize ranges) fieldWidth
          (bpRangeMinExcessEntries_mem_bound hwidth)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
          (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpRangeArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpRangeArgMinPrefixPosEntries shape blockSize ranges) fieldWidth
          (bpRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload_length
    omega

theorem concreteBPRangeArgMinWitnessTable_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    table.payload.length = 2 * (ranges.length * fieldWidth) /\
      (forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none) /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  exact
    (concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth ranges hwidth).profile

theorem concreteBPRangeArgMinWitnessTable_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth slots n : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hoverhead :
      2 * (ranges.length * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      table.payload.length <= sampledDirectoryOverhead slots n /\
      (forall rangeIndex,
        (table.rangeCloseCosted rangeIndex).cost <= 2 /\
          (table.rangeCloseCosted rangeIndex).erase =
            match
              (bpRangeMinExcessEntries shape blockSize ranges)[rangeIndex]?,
              (bpRangeArgMinPrefixPosEntries
                shape blockSize ranges)[rangeIndex]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none) := by
  let table :=
    concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth ranges hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · exact
      PayloadLiveBPRangeArgMinWitnessTable.payload_length_le_sampled
        table hoverhead
  · intro rangeIndex
    exact (concreteBPRangeArgMinWitnessTable_profile
      shape blockSize fieldWidth ranges hwidth).2.2 rangeIndex

theorem concreteBPRangeArgMinWitnessTable_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let table :=
      concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPRangeArgMinWitnessTable.read_words_length_le_machine
      (concreteBPRangeArgMinWitnessTable
        shape blockSize fieldWidth ranges hwidth) hmachine

/-!
## Block-pair macro close candidate

This component consumes the range-witness table through an
`lcaCloseCosted`-shaped API.  It is intentionally only the macro candidate:
the full C2 close answer still has to combine this interior witness with
endpoint-fringe repair.
-/

def blockPairRangeSlot
    (blockCount leftBlock rightBlock : Nat) : Nat :=
  leftBlock * blockCount + rightBlock

def blockPairRangeOfSlot (blockCount slot : Nat) : Nat × Nat :=
  let leftBlock := slot / blockCount
  let rightBlock := slot % blockCount
  if leftBlock <= rightBlock then
    (leftBlock, rightBlock - leftBlock + 1)
  else
    (leftBlock, 0)

def blockPairRanges (blockCount : Nat) : List (Nat × Nat) :=
  (List.range (blockCount * blockCount)).map
    (blockPairRangeOfSlot blockCount)

theorem blockPairRanges_length (blockCount : Nat) :
    (blockPairRanges blockCount).length =
      blockCount * blockCount := by
  simp [blockPairRanges]

theorem blockPairRangeSlot_lt
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock <
      blockCount * blockCount := by
  simpa [blockPairRangeSlot, densePairSlot] using
    densePairSlot_lt hleft hright

theorem blockPairRangeSlot_div
    {blockCount leftBlock rightBlock : Nat}
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
      leftBlock := by
  simpa [blockPairRangeSlot, densePairSlot] using
    (densePairSlot_div
      (blockSize := blockCount) (leftLocal := leftBlock)
      (rightLocal := rightBlock) hright)

theorem blockPairRangeSlot_mod
    {blockCount leftBlock rightBlock : Nat}
    (hright : rightBlock < blockCount) :
    blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
      rightBlock := by
  simpa [blockPairRangeSlot, densePairSlot] using
    (densePairSlot_mod
      (blockSize := blockCount) (leftLocal := leftBlock)
      (rightLocal := rightBlock) hright)

theorem blockPairRanges_get?_of_ordered_bounds
    {blockCount leftBlock rightBlock : Nat}
    (hleft : leftBlock < blockCount)
    (hright : rightBlock < blockCount)
    (hordered : leftBlock <= rightBlock) :
    (blockPairRanges blockCount)[
        blockPairRangeSlot blockCount leftBlock rightBlock]? =
      some (leftBlock, rightBlock - leftBlock + 1) := by
  have hslot :
      blockPairRangeSlot blockCount leftBlock rightBlock <
        blockCount * blockCount :=
    blockPairRangeSlot_lt hleft hright
  have hslotGet :
      (List.range (blockCount * blockCount))[
          blockPairRangeSlot blockCount leftBlock rightBlock]? =
        some (blockPairRangeSlot blockCount leftBlock rightBlock) := by
    exact List.getElem?_range hslot
  have hdiv :
      blockPairRangeSlot blockCount leftBlock rightBlock / blockCount =
        leftBlock :=
    blockPairRangeSlot_div hright
  have hmod :
      blockPairRangeSlot blockCount leftBlock rightBlock % blockCount =
        rightBlock :=
    blockPairRangeSlot_mod hright
  simp [blockPairRanges, List.getElem?_map, hslotGet,
    blockPairRangeOfSlot, hdiv, hmod, hordered]

/--
Concrete payload-live macro candidate indexed by the endpoint close blocks.

The payload is a position-bearing range-witness table over the block-pair range
list.  A query reads the block-pair witness and returns its close candidate.
-/
structure PayloadLiveBPBlockPairRangeWitnessMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth overhead : Nat) where
  table :
    PayloadLiveBPRangeArgMinWitnessTable shape blockSize fieldWidth overhead
      (blockPairRanges blockCount)

namespace PayloadLiveBPBlockPairRangeWitnessMacro

def payload
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) : List Bool :=
  component.table.payload

def rangeIndex
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (_component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) : Nat :=
  blockPairRangeSlot blockCount
    (blockOfClose blockSize leftClose)
    (blockOfClose blockSize rightClose)

def lcaCloseCosted
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) : Costed (Option Nat) :=
  component.table.rangeCloseCosted
    (component.rangeIndex leftClose rightClose)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) :
    component.payload.length = overhead := by
  exact component.table.payload_length

theorem lcaCloseCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).cost <= 2 := by
  exact component.table.rangeCloseCosted_cost_le_two
    (component.rangeIndex leftClose rightClose)

theorem lcaCloseCosted_erase
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      match
        (bpRangeMinExcessEntries shape blockSize
          (blockPairRanges blockCount))[
            component.rangeIndex leftClose rightClose]?,
        (bpRangeArgMinPrefixPosEntries shape blockSize
          (blockPairRanges blockCount))[
            component.rangeIndex leftClose rightClose]? with
      | some _minExcess, some prefixPos => some (prefixPos - 1)
      | _, _ => none := by
  exact component.table.rangeCloseCosted_erase
    (component.rangeIndex leftClose rightClose)

theorem lcaCloseCosted_exact_of_prefix_pos
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead answerClose : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (leftClose rightClose : Nat)
    (hmin :
      (bpRangeMinExcessEntries shape blockSize
        (blockPairRanges blockCount))[
          component.rangeIndex leftClose rightClose]? =
        some (bpExcessAt shape (answerClose + 1)))
    (harg :
      (bpRangeArgMinPrefixPosEntries shape blockSize
        (blockPairRanges blockCount))[
          component.rangeIndex leftClose rightClose]? =
        some (answerClose + 1)) :
    (component.lcaCloseCosted leftClose rightClose).erase =
      some answerClose := by
  exact component.table.rangeCloseCosted_exact_of_prefix_pos hmin harg

theorem read_words_length_le_machine
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact component.table.read_words_length_le_machine hmachine

theorem profile
    {shape : Cartesian.CartesianShape}
    {blockSize blockCount fieldWidth overhead : Nat}
    (component :
      PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
        fieldWidth overhead) :
    component.payload.length = overhead /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  constructor
  · exact component.payload_length
  · intro leftClose rightClose
    exact ⟨component.lcaCloseCosted_cost_le_two leftClose rightClose,
      component.lcaCloseCosted_erase leftClose rightClose⟩

end PayloadLiveBPBlockPairRangeWitnessMacro

def concreteBPBlockPairRangeWitnessMacro
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPBlockPairRangeWitnessMacro shape blockSize blockCount
      fieldWidth
        (2 * ((blockPairRanges blockCount).length * fieldWidth)) where
  table :=
    concreteBPRangeArgMinWitnessTable
      shape blockSize fieldWidth (blockPairRanges blockCount) hwidth

theorem concreteBPBlockPairRangeWitnessMacro_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    component.payload.length =
        2 * ((blockCount * blockCount) * fieldWidth) /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  have hprofile :=
    (concreteBPBlockPairRangeWitnessMacro
      shape blockSize blockCount fieldWidth hwidth).profile
  constructor
  · simpa [concreteBPBlockPairRangeWitnessMacro, blockPairRanges_length]
      using hprofile.1
  · exact hprofile.2

theorem concreteBPBlockPairRangeWitnessMacro_sampled_profile
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth slots n : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hoverhead :
      2 * ((blockCount * blockCount) * fieldWidth) <=
        sampledDirectoryOverhead slots n) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    LittleOLinear (sampledDirectoryOverhead slots) /\
      component.payload.length <= sampledDirectoryOverhead slots n /\
      forall leftClose rightClose,
        (component.lcaCloseCosted leftClose rightClose).cost <= 2 /\
          (component.lcaCloseCosted leftClose rightClose).erase =
            match
              (bpRangeMinExcessEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]?,
              (bpRangeArgMinPrefixPosEntries shape blockSize
                (blockPairRanges blockCount))[
                  component.rangeIndex leftClose rightClose]? with
            | some _minExcess, some prefixPos => some (prefixPos - 1)
            | _, _ => none := by
  let component :=
    concreteBPBlockPairRangeWitnessMacro
      shape blockSize blockCount fieldWidth hwidth
  constructor
  · exact sampledDirectoryOverhead_littleO slots
  constructor
  · rw [component.payload_length]
    simpa [blockPairRanges_length] using hoverhead
  · exact (concreteBPBlockPairRangeWitnessMacro_profile
      shape blockSize blockCount fieldWidth hwidth).2

theorem concreteBPBlockPairRangeWitnessMacro_read_words_length_le_machine
    (shape : Cartesian.CartesianShape)
    (blockSize blockCount fieldWidth : Nat)
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmachine :
      fieldWidth <=
        SuccinctRank.machineWordBits shape.bpCode.length) :
    let component :=
      concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.minTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) /\
    (forall {rangeIndex : Nat} {word : List Bool},
      component.table.argTable.store.words[rangeIndex]? = some word ->
        word.length <=
          SuccinctRank.machineWordBits shape.bpCode.length) := by
  exact
    PayloadLiveBPBlockPairRangeWitnessMacro.read_words_length_le_machine
      (concreteBPBlockPairRangeWitnessMacro
        shape blockSize blockCount fieldWidth hwidth) hmachine


end SuccinctCloseProposal
end RMQ
