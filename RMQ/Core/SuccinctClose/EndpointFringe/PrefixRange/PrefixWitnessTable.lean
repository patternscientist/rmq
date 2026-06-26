import RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange.AnswerSemantics

/-!
# Payload-live prefix-range witness table

Split from `RMQ.Core.SuccinctClose.EndpointFringe.PrefixRange`.
Public declarations keep the historical `RMQ.SuccinctCloseProposal` namespace.
-/

namespace RMQ
namespace SuccinctCloseProposal

open SuccinctSpace

def bpPrefixRangeMinExcessEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range => bpPrefixRangeMinExcess shape range.1 range.2

def bpPrefixRangeArgMinPrefixPosEntries
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) : List Nat :=
  ranges.map fun range =>
    bpPrefixRangeArgMinPrefixPos shape range.1 range.2

theorem bpPrefixRangeMinExcessEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeMinExcessEntries shape ranges).length = ranges.length := by
  simp [bpPrefixRangeMinExcessEntries]

theorem bpPrefixRangeArgMinPrefixPosEntries_length
    (shape : Cartesian.CartesianShape)
    (ranges : List (Nat × Nat)) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges).length =
      ranges.length := by
  simp [bpPrefixRangeArgMinPrefixPosEntries]

theorem bpPrefixRangeMinExcessEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeMinExcess shape range.1 range.2) := by
  simp [bpPrefixRangeMinExcessEntries, List.getElem?_map, hget]

theorem bpPrefixRangeArgMinPrefixPosEntries_get?_of_ranges_get?
    {shape : Cartesian.CartesianShape}
    {ranges : List (Nat × Nat)}
    {rangeIndex : Nat} {range : Nat × Nat}
    (hget : ranges[rangeIndex]? = some range) :
    (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? =
      some (bpPrefixRangeArgMinPrefixPos shape range.1 range.2) := by
  simp [bpPrefixRangeArgMinPrefixPosEntries, List.getElem?_map, hget]

theorem bpPrefixRangeMinExcessEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeMinExcessEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeMinExcessEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeMinExcess_le_length shape range.1 range.2) hwidth

theorem bpPrefixRangeArgMinPrefixPosEntries_mem_bound
    {shape : Cartesian.CartesianShape}
    {fieldWidth entry : Nat}
    {ranges : List (Nat × Nat)}
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth)
    (hmem :
      List.Mem entry (bpPrefixRangeArgMinPrefixPosEntries shape ranges)) :
    entry < 2 ^ fieldWidth := by
  unfold bpPrefixRangeArgMinPrefixPosEntries at hmem
  rcases List.mem_map.mp hmem with ⟨range, _hrange, hentry⟩
  rw [← hentry]
  exact Nat.lt_of_le_of_lt
    (bpPrefixRangeArgMinPrefixPos_le_length shape range.1 range.2)
    hwidth

structure PayloadLiveBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth overhead : Nat)
    (ranges : List (Nat × Nat)) where
  minTable :
    FixedWidthNatTable
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
  argTable :
    FixedWidthNatTable
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
  payload_length_eq :
    minTable.payload.length + argTable.payload.length = overhead

namespace PayloadLiveBPPrefixRangeArgMinWitnessTable

def payload
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) : List Bool :=
  table.minTable.payload ++ table.argTable.payload

def rangeWitnessCosted
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) : Costed (Option (Nat × Nat)) :=
  Costed.bind (table.minTable.readCosted rangeIndex) fun min? =>
    Costed.map
      (fun arg? =>
        match min?, arg? with
        | some minExcess, some prefixPos => some (minExcess, prefixPos)
        | _, _ => none)
      (table.argTable.readCosted rangeIndex)

theorem payload_length
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead := by
  simp [payload, table.payload_length_eq]

theorem rangeWitnessCosted_cost_le_two
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).cost <= 2 := by
  unfold rangeWitnessCosted
  cases hread :
      (table.minTable.readCosted rangeIndex).value with
  | none =>
      simp [Costed.bind, Costed.map, hread]
  | some minExcess =>
      simp [Costed.bind, Costed.map, hread]

theorem rangeWitnessCosted_erase
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
    (rangeIndex : Nat) :
    (table.rangeWitnessCosted rangeIndex).erase =
      match
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? with
      | some minExcess, some prefixPos => some (minExcess, prefixPos)
      | _, _ => none := by
  unfold rangeWitnessCosted
  have hmin :
      (table.minTable.readCosted rangeIndex).value =
        (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]? := by
    exact table.minTable.readCosted_erase rangeIndex
  have harg :
      (table.argTable.readCosted rangeIndex).value =
        (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]? := by
    exact table.argTable.readCosted_erase rangeIndex
  cases hminEntry :
      (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?
  <;> cases hargEntry :
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
  <;> simp [Costed.bind, Costed.map, Costed.erase, hmin, harg,
    hminEntry, hargEntry]

theorem min_read_word_length_le_machine
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges)
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

theorem profile
    {shape : Cartesian.CartesianShape}
    {fieldWidth overhead : Nat}
    {ranges : List (Nat × Nat)}
    (table :
      PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth overhead
        ranges) :
    table.payload.length = overhead /\
      forall rangeIndex,
        (table.rangeWitnessCosted rangeIndex).cost <= 2 /\
          (table.rangeWitnessCosted rangeIndex).erase =
            match
              (bpPrefixRangeMinExcessEntries shape ranges)[rangeIndex]?,
              (bpPrefixRangeArgMinPrefixPosEntries shape ranges)[rangeIndex]?
            with
            | some minExcess, some prefixPos =>
                some (minExcess, prefixPos)
            | _, _ => none := by
  constructor
  · exact table.payload_length
  intro rangeIndex
  exact ⟨table.rangeWitnessCosted_cost_le_two rangeIndex,
    table.rangeWitnessCosted_erase rangeIndex⟩

end PayloadLiveBPPrefixRangeArgMinWitnessTable

def concreteBPPrefixRangeArgMinWitnessTable
    (shape : Cartesian.CartesianShape)
    (fieldWidth : Nat)
    (ranges : List (Nat × Nat))
    (hwidth : shape.bpCode.length < 2 ^ fieldWidth) :
    PayloadLiveBPPrefixRangeArgMinWitnessTable shape fieldWidth
      (2 * (ranges.length * fieldWidth)) ranges where
  minTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
      (bpPrefixRangeMinExcessEntries_mem_bound hwidth)
  argTable :=
    FixedWidthNatTable.ofEntries
      (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
      (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)
  payload_length_eq := by
    have hmin :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeMinExcessEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeMinExcessEntries shape ranges) fieldWidth
          (bpPrefixRangeMinExcessEntries_mem_bound hwidth)).payload_length
    have harg :
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload.length =
          ranges.length * fieldWidth := by
      simpa [bpPrefixRangeArgMinPrefixPosEntries_length] using
        (FixedWidthNatTable.ofEntries
          (bpPrefixRangeArgMinPrefixPosEntries shape ranges) fieldWidth
          (bpPrefixRangeArgMinPrefixPosEntries_mem_bound hwidth)).payload_length
    omega

end SuccinctCloseProposal
end RMQ
