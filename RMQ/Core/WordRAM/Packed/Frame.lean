import RMQ.Core.WordRAM.Packed.Compiler

/-! # Register frames for finite structured assembly -/

namespace RMQ.SuccinctFinal.PackedWordRAM.Structured

def Action.destination : Action → Nat
  | .load dst _ | .constant dst _ | .move dst _ |
    .arithmetic _ dst _ _ | .comparison _ dst _ _ => dst

def Block.WritesOnly (allowed : Nat → Prop) : Block → Prop
  | .skip | .exit _ => True
  | .action op => allowed op.destination
  | .seq a b | .ifZero _ a b => a.WritesOnly allowed ∧ b.WritesOnly allowed
  | .repeat _ body => body.WritesOnly allowed

theorem Action.eval_frame (memory : Memory) (op : Action) (s : Data) (r : Nat)
    (h : r ≠ op.destination) : (op.eval memory s).final.regs r = s.regs r := by
  cases op <;> simp only [Action.destination] at h
  all_goals simp [Action.eval, Action.instruction, execute, State.writeNext,
    Data.ofState, Registers.write, h]
  split <;> simp_all [Registers.write]

/-- Every source constructor respects its actual destination inventory,
including failed loads, stopped states, conditional branches and repeats. -/
theorem Block.eval_frame (memory : Memory) (block : Block) (allowed : Nat → Prop)
    (writes : block.WritesOnly allowed) (r : Nat) (outside : ¬ allowed r) (s : Data) :
    (block.eval memory s).final.regs r = s.regs r := by
  induction block generalizing s with
  | skip => cases hs : s.status <;> simp [Block.eval, hs]
  | action op =>
      by_cases hs : s.status = .running
      · simp only [Block.eval, hs]
        exact op.eval_frame memory s r (by intro h; apply outside; simpa [h] using writes)
      · rw [Block.eval_stopped memory _ _ hs]
  | exit src => cases hs : s.status <;> simp [Block.eval, hs]
  | seq a b iha ihb =>
      rw [Block.eval_seq]
      exact (ihb writes.2 (a.eval memory s).final).trans (iha writes.1 s)
  | ifZero c a b iha ihb =>
      by_cases hs : s.status = .running
      · simp only [Block.eval, hs]
        split
        · exact iha writes.1 s
        · exact ihb writes.2 s
      · rw [Block.eval_stopped memory _ _ hs]
  | «repeat» count body ih =>
      induction count generalizing s with
      | zero => rw [Block.eval_repeat]; rfl
      | succ count ihc =>
          rw [Block.eval_repeat_succ]
          exact (ihc writes (body.eval memory s).final).trans (ih writes s)

theorem Block.WritesOnly.sequence (blocks : List Block) (allowed : Nat → Prop)
    (h : ∀ block ∈ blocks, block.WritesOnly allowed) :
    (Block.sequence blocks).WritesOnly allowed := by
  induction blocks with
  | nil => trivial
  | cons block blocks ih =>
      exact ⟨h block (by simp), ih (by intro b hb; exact h b (by simp [hb]))⟩

theorem Block.WritesOnly.mono (block : Block) {small large : Nat → Prop}
    (h : block.WritesOnly small) (subset : ∀ r, small r → large r) :
    block.WritesOnly large := by
  induction block with
  | skip => trivial
  | action op => exact subset op.destination h
  | exit src => trivial
  | seq a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | ifZero c a b iha ihb => exact ⟨iha h.1, ihb h.2⟩
  | «repeat» count body ih => exact ih h

end RMQ.SuccinctFinal.PackedWordRAM.Structured
