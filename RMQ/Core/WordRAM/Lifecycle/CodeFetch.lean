import RMQ.Core.WordRAM.Lifecycle.Physical

/-! # Actual instruction fetches in the counted code region

PCs index instructions. Their checked translation to variable-length encoded
word offsets identifies every opcode and operand in the same numeric view.
-/

namespace RMQ.SuccinctFinal.PackedLifecycle.Physical

def codeOffset (program : List Instruction) (pc : Nat) : Nat :=
  ((program.take pc).map Instruction.encoding).flatten.length

theorem encoded_fetch (program : List Instruction) (pc : Nat) (instruction : Instruction)
    (fetch : program[pc]? = some instruction) (field word : Nat)
    (encoded : instruction.encoding[field]? = some word) :
    ((program.map Instruction.encoding).flatten)[codeOffset program pc + field]? = some word := by
  induction program generalizing pc with
  | nil => simp at fetch
  | cons first rest ih =>
    cases pc with
    | zero =>
      have heq : first = instruction := Option.some.inj fetch
      subst first
      have inside := (List.getElem?_eq_some_iff.mp encoded).1
      simpa only [codeOffset, List.take_zero, List.map_nil, List.flatten_nil, List.length_nil,
        Nat.zero_add, List.map_cons, List.flatten_cons, List.getElem?_append_left inside] using encoded
    | succ pc =>
      have next : rest[pc]? = some instruction := fetch
      have actual := ih pc next
      simp only [List.map_cons, List.flatten_cons, codeOffset, List.take_succ_cons,
        List.length_append]
      rw [List.getElem?_append_right (by omega)]
      simpa only [codeOffset, Nat.add_assoc, Nat.add_sub_cancel_left] using actual

theorem fetched_word (model : InputModel) (s : State) (instruction : Instruction)
    (fetch : (Layout.program model)[s.core.pc]? = some instruction)
    (field word : Nat) (encoded : instruction.encoding[field]? = some word) :
    codeOffset (Layout.program model) s.core.pc + field < codeLength model ∧
    lookup model s (codeAddress model (codeOffset (Layout.program model) s.core.pc + field)) = some word := by
  have encodedWord := encoded_fetch (Layout.program model) s.core.pc instruction fetch field word encoded
  have bound := (List.getElem?_eq_some_iff.mp encodedWord).1
  exact ⟨bound, (lookup_code model s _ bound).trans encodedWord⟩

theorem run_fetched_words (model : InputModel) (fuel : Nat) (s : State)
    (index : Nat) (t : Transition)
    (occurs : (run (Layout.program model) fuel s).transitions[index]? = some t) :
    ∃ instruction, t.action = .instruction instruction ∧
      (Layout.program model)[t.before.core.pc]? = some instruction ∧
      ∀ field word, instruction.encoding[field]? = some word →
        codeOffset (Layout.program model) t.before.core.pc + field < codeLength model ∧
        lookup model t.before
          (codeAddress model (codeOffset (Layout.program model) t.before.core.pc + field)) = some word := by
  obtain ⟨_, step⟩ := run_transition_at occurs
  obtain ⟨hb, _, instruction, fetch, action, _⟩ := step_spec step
  exact ⟨instruction, action, fetch, fetched_word model t.before instruction fetch⟩

end RMQ.SuccinctFinal.PackedLifecycle.Physical
