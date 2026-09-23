import RMQ.Core.WordRAM.Packed.Frame

/-! # Finite scratch storage for actual primitive runs -/

namespace RMQ.SuccinctFinal.PackedWordRAM

def Instruction.WritesOnly (allowed : Nat → Prop) : Instruction → Prop
  | .load dst _ | .constant dst _ | .move dst _ |
    .arithmetic _ dst _ _ | .comparison _ dst _ _ => allowed dst
  | .jump _ | .jumpRegister _ | .branchZero _ _ | .halt _ => True

theorem execute_frame (memory : Memory) (instruction : Instruction) (state : State)
    (allowed : Nat → Prop) (hwrites : instruction.WritesOnly allowed)
    (r : Nat) (hout : ¬ allowed r) :
    (execute memory instruction state).1.regs r = state.regs r := by
  have hne : ∀ d, allowed d → r ≠ d := by
    intro d hd heq
    subst r
    exact hout hd
  cases instruction <;> simp only [Instruction.WritesOnly] at hwrites
  all_goals first
    | rfl
    | (have hn := hne _ hwrites
       simp [execute, State.writeNext, Registers.write, hn])
  split <;> simp_all [Registers.write]

theorem step_frame (memory : Memory) (program : Program) (state : State)
    (allowed : Nat → Prop) (hwrites : ∀ i ∈ program, i.WritesOnly allowed)
    (r : Nat) (hout : ¬ allowed r) (t : Transition)
    (hstep : step memory program state = some t) : t.after.regs r = state.regs r := by
  cases hs : state.status with
  | halted value => simp [step, hs] at hstep
  | fault => simp [step, hs] at hstep
  | running =>
      cases hi : program[state.pc]? with
      | none => simp [step, hs, hi] at hstep
      | some instruction =>
          simp only [step, hs, hi, Option.some.injEq] at hstep
          subst t
          exact execute_frame memory instruction state allowed
            (hwrites instruction (List.mem_of_getElem? hi)) r hout

/-- This applies to every fuel prefix, including faults and early halts. -/
theorem run_frame (memory : Memory) (program : Program) (fuel : Nat) (state : State)
    (allowed : Nat → Prop) (hwrites : ∀ i ∈ program, i.WritesOnly allowed)
    (r : Nat) (hout : ¬ allowed r) :
    (run memory program fuel state).final.regs r = state.regs r := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
      cases ht : step memory program state with
      | none => simp [run, ht]
      | some t =>
          simpa only [run, ht] using
            (ih t.after).trans (step_frame memory program state allowed hwrites r hout t ht)

namespace Structured

def Block.maxDestination : Block → Nat
  | .skip | .exit _ => 0
  | .action op => op.destination
  | .seq a b | .ifZero _ a b => max a.maxDestination b.maxDestination
  | .repeat _ body => body.maxDestination

theorem Block.writesOnly_maxDestination (block : Block) :
    block.WritesOnly (fun r => r ≤ block.maxDestination) := by
  induction block with
  | skip => trivial
  | exit src => trivial
  | action op => exact Nat.le_refl _
  | seq a b iha ihb | ifZero condition a b iha ihb =>
      exact ⟨Block.WritesOnly.mono a iha (fun _ h => Nat.le_trans h (Nat.le_max_left ..)),
        Block.WritesOnly.mono b ihb (fun _ h => Nat.le_trans h (Nat.le_max_right ..))⟩
  | «repeat» count body ih => exact ih

theorem Block.compile_writesOnly (block : Block) (allowed : Nat → Prop)
    (h : block.WritesOnly allowed) (base : Nat) :
    ∀ instruction ∈ block.compileAt base, instruction.WritesOnly allowed := by
  induction block generalizing base with
  | skip => simp [Block.compileAt]
  | exit src => simp [Block.compileAt, Instruction.WritesOnly]
  | action op =>
      cases op <;> simpa [Block.compileAt, Action.instruction,
        Instruction.WritesOnly, Block.WritesOnly, Action.destination] using h
  | seq a b iha ihb =>
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact iha h.1 _ i hi
      · exact ihb h.2 _ i hi
  | ifZero condition a b iha ihb =>
      intro i hi
      simp only [Block.compileAt, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false] at hi
      rcases hi with ((rfl | hi) | rfl) | hi
      · trivial
      · exact ihb h.2 _ i hi
      · trivial
      · exact iha h.1 _ i hi
  | «repeat» count body ih =>
      intro i hi
      obtain ⟨code, hcode, hi⟩ := List.mem_flatten.mp hi
      obtain ⟨index, _, rfl⟩ := List.mem_map.mp hcode
      exact ih h _ i hi

end Structured
end RMQ.SuccinctFinal.PackedWordRAM
