import RMQ.Core.SuccinctSelect.AsymptoticFacts

/-!
# Select-side finite-table obstruction layer

This module contains the finite-table obstruction lemmas that sit above the
two-level select layer. Reusable neutral payload-size and linear-growth facts
live in `RMQ.Core.SuccinctSelect.AsymptoticFacts` so active implementations do
not import this historical obstruction surface just for helper lemmas.
-/

namespace RMQ
namespace SuccinctSelect

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
