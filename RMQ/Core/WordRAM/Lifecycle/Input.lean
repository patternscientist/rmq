import RMQ.Core.WordRAM.Lifecycle.Safety
import RMQ.Core.WordRAM.Lifecycle.Builder

/-! # Supplied lifecycle input and bounded request storage

Materialization is an explicit input boundary. The word route supplies encoded
keys, the comparison route supplies separate Int cells, and both place exactly
two request words after their numeric input in the same owned arena.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle

open PackedConstruction (Operand put)
open PackedWordRAM (wordWidth)

inductive InputModel where
  | word | comparison
deriving DecidableEq, Repr

def InputModel.source : InputModel → PackedConstruction.Structured.Block
  | .word => PackedConstruction.wordLeaf
  | .comparison => PackedConstruction.keyLeaf

def inputCore (model : InputModel) (xs : List Int) : PackedConstruction.State :=
  match model with
  | .word => PackedConstruction.wordInputState (wordWidth xs.length) xs
  | .comparison => PackedConstruction.comparisonInputState xs

def initialState (model : InputModel) (xs : List Int) (left right entry : Nat) : State :=
  let s := inputCore model xs
  { core := { s with
      memory := put (put s.memory s.extent (some left)) (s.extent + 1) (some right)
      extent := s.extent + 2
      pc := entry }
    keyExtent := if model = .comparison then xs.length else 0
    keyRegExtent := if model = .comparison then 2 else 0 }

def InputDomain (model : InputModel) (xs : List Int) : Prop :=
  match model with
  | .word => PackedConstruction.InputFits (wordWidth xs.length) xs
  | .comparison => True

theorem inputCore_extent_pos (model : InputModel) (xs : List Int) :
    0 < (inputCore model xs).extent := by
  cases model <;> simp [inputCore, PackedConstruction.wordInputState,
    PackedConstruction.comparisonInputState, PackedConstruction.inputCellCount]

theorem initial_memory_below (model : InputModel) (xs : List Int) (left right entry a : Nat)
    (ha : a < (inputCore model xs).extent) :
    (initialState model xs left right entry).core.memory a = (inputCore model xs).memory a := by
  simp [initialState, put, show a ≠ (inputCore model xs).extent by omega,
    show a ≠ (inputCore model xs).extent + 1 by omega]

theorem initial_requests (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialState model xs left right entry).core.memory (inputCore model xs).extent = some left ∧
    (initialState model xs left right entry).core.memory ((inputCore model xs).extent + 1) =
      some right := by
  simp [initialState, put]

theorem initial_header (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialState model xs left right entry).core.memory 0 = some xs.length := by
  rw [initial_memory_below model xs left right entry 0 (inputCore_extent_pos model xs)]
  cases model <;> simp [inputCore, PackedConstruction.wordInputState,
    PackedConstruction.comparisonInputState]

theorem initial_clean (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialState model xs left right entry).Closed := by
  have ht : PackedConstruction.CleanTail (inputCore model xs) := by
    cases model
    · exact PackedConstruction.wordInputState_cleanTail _ _
    · exact PackedConstruction.comparisonInputState_cleanTail _
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    change (inputCore model xs).extent + 2 ≤ a at ha
    simp [initialState, put, show a ≠ (inputCore model xs).extent by omega,
      show a ≠ (inputCore model xs).extent + 1 by omega, ht a (by omega)]
  · intro a ha
    cases model with
    | word => rfl
    | comparison =>
      change xs.length ≤ a at ha
      exact List.getElem?_eq_none_iff.mpr ha
  · intro r _
    cases model <;> rfl

theorem initial_input (model : InputModel) (xs : List Int) (left right entry : Nat)
    (domain : InputDomain model xs) :
    match model with
    | .word => PackedConstruction.Proof.WordInput (wordWidth xs.length) xs
        (initialState model xs left right entry).core
    | .comparison => PackedConstruction.Proof.OracleInput xs
        (initialState model xs left right entry).core := by
  cases model with
  | comparison => rfl
  | word =>
    refine ⟨domain, ?_, ?_⟩
    · change xs.length + 1 ≤ (xs.length + 1) + 2
      omega
    · intro k hk
      rw [initial_memory_below .word xs left right entry (k+1) (by
        change k + 1 < xs.length + 1; omega)]
      exact PackedConstruction.encodeInput_key
        (PackedConstruction.Proof.getD_eq_of_getElem? hk)

/-- The original width has ample slack for two supplied request cells as well
as the original construction envelope. -/
theorem initial_capacity (model : InputModel) (xs : List Int) (left right entry : Nat) :
    (initialState model xs left right entry).core.extent +
      64 * (400000 * (xs.length + 1)) < 2 ^ wordWidth xs.length := by
  have h := PackedConstruction.Proof.bankcap_wordWidth xs.length
  have hp : 2 * xs.length + 4 ≤ (2 * xs.length + 4) ^ 8 :=
    Nat.le_self_pow (by decide) _
  have h32 : (2 : Nat) ^ 32 = 4294967296 := by decide
  rw [h32] at h
  cases model <;>
    simp only [initialState, inputCore, PackedConstruction.wordInputState,
      PackedConstruction.comparisonInputState, PackedConstruction.inputCellCount] <;> omega

theorem initial_fits (model : InputModel) (xs : List Int) (left right entry : Nat)
    (domain : InputDomain model xs) (hl : left < 2 ^ wordWidth xs.length)
    (hr : right < 2 ^ wordWidth xs.length) (he : entry < 2 ^ wordWidth xs.length) :
    (initialState model xs left right entry).Fits (wordWidth xs.length) := by
  have cap := initial_capacity model xs left right entry
  have hn : xs.length < 2 ^ wordWidth xs.length := by
    have h := PackedConstruction.Proof.cap_wordWidth xs.length
    omega
  have hpos : 0 < 2 ^ wordWidth xs.length := Nat.two_pow_pos _
  refine ⟨⟨?_, he, by omega, ?_, ?_⟩, ?_, ?_⟩
  · intro r
    cases model <;> exact hpos
  · intro a v hv
    simp only [initialState, put] at hv
    split at hv
    · cases hv; exact hr
    · split at hv
      · cases hv; exact hl
      · cases model with
        | word => exact PackedConstruction.encodeInput_word_fits domain hv
        | comparison =>
          simp only [inputCore, PackedConstruction.comparisonInputState] at hv
          split at hv
          · cases hv; exact hn
          · cases hv
  · intro v hv
    cases model <;> cases hv
  · cases model <;> simp only [initialState, reduceCtorEq, ↓reduceIte]
    · exact hpos
    · exact hn
  · have hw := PackedConstruction.Proof.wordWidth_ge_32 xs.length
    have hp := Nat.pow_le_pow_right (by decide : 0 < 2) hw
    cases model <;> simp only [initialState, reduceCtorEq, ↓reduceIte] <;> omega

end RMQ.SuccinctFinal.PackedLifecycle
