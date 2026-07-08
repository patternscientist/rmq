import RMQ.Core.SuccinctSelect.TwoLevel

/-!
# Neutral select-side asymptotic facts

Reusable payload-size and linear-growth lemmas for the select-side
constructions. Negative obstruction modules import this file, but active
positive implementations can depend on these neutral facts without importing
the historical obstruction theorem surface.
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

end SuccinctSelect
end RMQ
