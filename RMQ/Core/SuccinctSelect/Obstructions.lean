import RMQ.Core.SuccinctSelect.TwoLevel

/-!
# Select-side finite-table obstruction layer

This module contains the finite-table payload budget facts and obstruction
lemmas that sit above the two-level select layer. It keeps the historical
`RMQ.SuccinctSelect` namespace so theorem names remain stable.
-/

namespace RMQ
namespace SuccinctSelect

/-- Bit budget occupied by the true/false fixed-width select locator tables. -/
def selectLocatorPayloadBudget
    (trueEntries falseEntries : List (Option SuccinctSpace.StoredWordSelectSample))
    (fieldWidth : Nat) : Nat :=
  trueEntries.length * SuccinctSpace.selectSampleWordWidth fieldWidth +
    falseEntries.length * SuccinctSpace.selectSampleWordWidth fieldWidth

theorem fixedWidthSelectSampleTables_payload_length_eq_budget
    {trueEntries falseEntries :
      List (Option SuccinctSpace.StoredWordSelectSample)}
    {fieldWidth : Nat}
    (tables :
      SuccinctSpace.FixedWidthSelectSampleTables
        trueEntries falseEntries fieldWidth) :
    tables.payload.length =
      selectLocatorPayloadBudget trueEntries falseEntries fieldWidth := by
  simp [selectLocatorPayloadBudget,
    SuccinctSpace.FixedWidthSelectSampleTables.payload_length]

theorem fixedWidthSelectSampleTables_payload_length_le_sampled
    {trueEntries falseEntries :
      List (Option SuccinctSpace.StoredWordSelectSample)}
    {fieldWidth slots n : Nat}
    (tables :
      SuccinctSpace.FixedWidthSelectSampleTables
        trueEntries falseEntries fieldWidth)
    (hbudget :
      selectLocatorPayloadBudget trueEntries falseEntries fieldWidth <=
        SuccinctSpace.sampledDirectoryOverhead slots n) :
    tables.payload.length <=
      SuccinctSpace.sampledDirectoryOverhead slots n := by
  rw [fixedWidthSelectSampleTables_payload_length_eq_budget tables]
  exact hbudget

theorem canonicalSelectBlockTablesFinite_payload_length_eq
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) :
    (canonicalSelectBlockTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).payload.length =
      (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth +
        (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth := by
  simp [canonicalSelectBlockTablesFinite, canonicalSelectBlockTables,
    selectBlockDeltaEntries, canonicalSelectBlockCount,
    SuccinctSpace.FixedWidthSelectSampleTables.payload_length]

theorem canonicalSelectBlockTablesFinite_payload_length_ge_succ
    {bits : List Bool} {wordSize occurrencesPerSuper fieldWidth : Nat}
    (hbits : bits.length < 2 ^ fieldWidth) :
    bits.length + 1 <=
      (canonicalSelectBlockTablesFinite
        bits wordSize occurrencesPerSuper fieldWidth hbits).payload.length := by
  rw [canonicalSelectBlockTablesFinite_payload_length_eq hbits]
  have hword :
      1 <= SuccinctSpace.selectSampleWordWidth fieldWidth := by
    unfold SuccinctSpace.selectSampleWordWidth
    omega
  have hfirst :
      bits.length + 1 <=
        (bits.length + 1) *
          SuccinctSpace.selectSampleWordWidth fieldWidth := by
    simpa using Nat.mul_le_mul_left (bits.length + 1) hword
  exact Nat.le_trans hfirst (Nat.le_add_right _ _)

theorem not_littleOLinear_of_succ_le
    {overhead : Nat -> Nat}
    (hle : forall n : Nat, n + 1 <= overhead n) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  intro hoverhead
  rcases hoverhead 2 (by omega) with ⟨threshold, hthreshold⟩
  have hscaled : 2 * overhead threshold <= threshold :=
    hthreshold threshold (Nat.le_refl threshold)
  have hsucc : threshold + 1 <= overhead threshold := hle threshold
  have hcontr : 2 * (threshold + 1) <= threshold := by
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hsucc) hscaled
  omega

theorem not_littleOLinear_of_self_le
    {overhead : Nat -> Nat}
    (hle : forall n : Nat, n <= overhead n) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  intro hoverhead
  rcases hoverhead 2 (by omega) with ⟨threshold, hthreshold⟩
  let n := threshold + 1
  have hscaled : 2 * overhead n <= n :=
    hthreshold n (by omega)
  have hself : n <= overhead n := hle n
  have hcontr : 2 * n <= n := by
    exact Nat.le_trans (Nat.mul_le_mul_left 2 hself) hscaled
  omega

def clarkSelectTwoWordDescriptorIndexIdentityOverhead (n : Nat) : Nat :=
  let bits : List Bool := List.replicate n false
  let fieldWidth := SuccinctRank.machineWordBits bits.length
  (clarkSelectTwoWordDescriptorIndexTable
    false bits 1 1 fieldWidth (bits.length + 1)
    (by omega)
    (by omega)
    (by
      simpa [fieldWidth, SuccinctRank.machineWordBits] using
        (Nat.lt_log2_self (n := bits.length)))).table.payload.length

theorem clarkSelectTwoWordDescriptorIndexIdentityOverhead_ge_succ
    (n : Nat) :
    n + 1 <= clarkSelectTwoWordDescriptorIndexIdentityOverhead n := by
  let bits : List Bool := List.replicate n false
  let fieldWidth := SuccinctRank.machineWordBits bits.length
  have hbits : bits.length < 2 ^ fieldWidth := by
    simpa [fieldWidth, SuccinctRank.machineWordBits] using
      (Nat.lt_log2_self (n := bits.length))
  have hpayload :
      clarkSelectTwoWordDescriptorIndexIdentityOverhead n =
        (bits.length + 1) * fieldWidth := by
    simp [clarkSelectTwoWordDescriptorIndexIdentityOverhead, bits,
      fieldWidth, clarkSelectTwoWordDescriptorIndexTable,
      clarkSelectTwoWordDescriptorIndexEntries,
      SuccinctSpace.FixedWidthNatTable.payload_length]
  have hfield : 1 <= fieldWidth := by
    exact SuccinctRank.machineWordBits_pos bits.length
  have hmul : bits.length + 1 <= (bits.length + 1) * fieldWidth := by
    simpa using Nat.mul_le_mul_left (bits.length + 1) hfield
  have hlen : bits.length = n := by
    simp [bits]
  rw [hpayload]
  simpa [hlen] using hmul

theorem clarkSelectTwoWordDescriptorIndexIdentityOverhead_not_littleO :
    ¬ SuccinctSpace.LittleOLinear
        clarkSelectTwoWordDescriptorIndexIdentityOverhead := by
  exact not_littleOLinear_of_succ_le
    clarkSelectTwoWordDescriptorIndexIdentityOverhead_ge_succ

theorem canonicalSelectBlockTablesFinite_identity_payload_not_littleO
    {overhead : Nat -> Nat}
    (hbound :
      forall bits : List Bool,
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (by
              simpa [SuccinctRank.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length <=
          overhead bits.length) :
    ¬ SuccinctSpace.LittleOLinear overhead := by
  apply not_littleOLinear_of_succ_le
  intro n
  let bits : List Bool := List.replicate n false
  have hpayload :
      bits.length + 1 <=
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (by
              simpa [SuccinctRank.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length :=
    canonicalSelectBlockTablesFinite_payload_length_ge_succ
      (bits := bits)
      (wordSize := SuccinctRank.machineWordBits bits.length)
      (occurrencesPerSuper :=
        SuccinctRank.machineWordBits bits.length)
      (fieldWidth := SuccinctRank.machineWordBits bits.length)
      (by
        simpa [SuccinctRank.machineWordBits] using
          (Nat.lt_log2_self (n := bits.length)))
  have hboundBits := hbound bits
  have hlen : bits.length = n := by
    simp [bits]
  have hcombined := Nat.le_trans hpayload hboundBits
  simpa [hlen] using hcombined

theorem noTwoLevelPayloadLiveStoredWordRankSelectFamily_with_canonical_select_block
    {rankSuper rankBlock selectSuper selectBlock : Nat -> Nat}
    {queryCost : Nat}
    (family :
      TwoLevelPayloadLiveStoredWordRankSelectFamily
        rankSuper rankBlock selectSuper selectBlock queryCost) :
    ¬ (forall bits : List Bool,
        (canonicalSelectBlockTablesFinite
            bits
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (SuccinctRank.machineWordBits bits.length)
            (by
              simpa [SuccinctRank.machineWordBits] using
                (Nat.lt_log2_self (n := bits.length)))).payload.length <=
          selectBlock bits.length) := by
  intro hbound
  exact
    canonicalSelectBlockTablesFinite_identity_payload_not_littleO
      hbound family.selectBlock_littleO


end SuccinctSelect
end RMQ
